/*
 * Copyright (C) 2012 Alexander Block.  All rights reserved.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License v2 as published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 021110-1307, USA.
 */

#include <linux/bsearch.h>
#include <linux/fs.h>
#include <linux/file.h>
#include <linux/sort.h>
#include <linux/mount.h>
#include <linux/xattr.h>
#include <linux/posix_acl_xattr.h>
#include <linux/radix-tree.h>
#include <linux/crc32c.h>

#include "send.h"
#include "backref.h"
#include "locking.h"
#include "disk-io.h"
#include "btrfs_inode.h"
#include "transaction.h"

static int g_verbose = 0;

#define verbose_printk(...) if (g_verbose) printk(__VA_ARGS__)

/*
 * A fs_path is a helper to dynamically build path names with unknown size.
 * It reallocates the internal buffer on demand.
 * It allows fast adding of path elements on the right side (normal path) and
 * fast adding to the left side (reversed path). A reversed path can also be
 * unreversed if needed.
 */
struct fs_path {
	union {
		struct {
			char *start;
			char *end;
			char *prepared;

			char *buf;
			int buf_len;
			int reversed:1;
			int virtual_mem:1;
			char inline_buf[];
		};
		char pad[PAGE_SIZE];
	};
};
#define FS_PATH_INLINE_SIZE \
	(sizeof(struct fs_path) - offsetof(struct fs_path, inline_buf))


/* reused for each extent */
struct clone_root {
	struct btrfs_root *root;
	u64 ino;
	u64 offset;

	u64 found_refs;
};

#define SEND_CTX_MAX_NAME_CACHE_SIZE 128
#define SEND_CTX_NAME_CACHE_CLEAN_SIZE (SEND_CTX_MAX_NAME_CACHE_SIZE * 2)

struct send_ctx {
	struct file *send_filp;
	loff_t send_off;
	char *send_buf;
	u32 send_size;
	u32 send_max_size;
	u64 total_send_size;
	u64 cmd_send_size[BTRFS_SEND_C_MAX + 1];

	struct vfsmount *mnt;

	struct btrfs_root *send_root;
	struct btrfs_root *parent_root;
	struct clone_root *clone_roots;
	int clone_roots_cnt;

	/* current state of the compare_tree call */
	struct btrfs_path *left_path;
	struct btrfs_path *right_path;
	struct btrfs_key *cmp_key;

	/*
	 * infos of the currently processed inode. In case of deleted inodes,
	 * these are the values from the deleted inode.
	 */
	u64 cur_ino;
	u64 cur_inode_gen;
	int cur_inode_new;
	int cur_inode_new_gen;
	int cur_inode_deleted;
	u64 cur_inode_size;
	u64 cur_inode_mode;

	u64 send_progress;

	struct list_head new_refs;
	struct list_head deleted_refs;

	struct radix_tree_root name_cache;
	struct list_head name_cache_list;
	int name_cache_size;

	struct file *cur_inode_filp;
	char *read_buf;
};

struct name_cache_entry {
	struct list_head list;
	struct list_head use_list;
	u64 ino;
	u64 gen;
	u64 parent_ino;
	u64 parent_gen;
	int ret;
	int need_later_update;
	int name_len;
	char name[];
};

static void fs_path_reset(struct fs_path *p)
{
	if (p->reversed) {
		p->start = p->buf + p->buf_len - 1;
		p->end = p->start;
		*p->start = 0;
	} else {
		p->start = p->buf;
		p->end = p->start;
		*p->start = 0;
	}
}

static struct fs_path *fs_path_alloc(struct send_ctx *sctx)
{
	struct fs_path *p;

	p = kmalloc(sizeof(*p), GFP_NOFS);
	if (!p)
		return NULL;
	p->reversed = 0;
	p->virtual_mem = 0;
	p->buf = p->inline_buf;
	p->buf_len = FS_PATH_INLINE_SIZE;
	fs_path_reset(p);
	return p;
}

static struct fs_path *fs_path_alloc_reversed(struct send_ctx *sctx)
{
	struct fs_path *p;

	p = fs_path_alloc(sctx);
	if (!p)
		return NULL;
	p->reversed = 1;
	fs_path_reset(p);
	return p;
}

static void fs_path_free(struct send_ctx *sctx, struct fs_path *p)
{
	if (!p)
		return;
	if (p->buf != p->inline_buf) {
		if (p->virtual_mem)
			vfree(p->buf);
		else
			kfree(p->buf);
	}
	kfree(p);
}

static int fs_path_len(struct fs_path *p)
{
	return p->end - p->start;
}

static int fs_path_ensure_buf(struct fs_path *p, int len)
{
	char *tmp_buf;
	int path_len;
	int old_buf_len;

	len++;

	if (p->buf_len >= len)
		return 0;

	path_len = p->end - p->start;
	old_buf_len = p->buf_len;
	len = PAGE_ALIGN(len);

	if (p->buf == p->inline_buf) {
		tmp_buf = kmalloc(len, GFP_NOFS);
		if (!tmp_buf) {
			tmp_buf = vmalloc(len);
			if (!tmp_buf)
				return -ENOMEM;
			p->virtual_mem = 1;
		}
		memcpy(tmp_buf, p->buf, p->buf_len);
		p->buf = tmp_buf;
		p->buf_len = len;
	} else {
		if (p->virtual_mem) {
			tmp_buf = vmalloc(len);
			if (!tmp_buf)
				return -ENOMEM;
			memcpy(tmp_buf, p->buf, p->buf_len);
			vfree(p->buf);
		} else {
			tmp_buf = krealloc(p->buf, len, GFP_NOFS);
			if (!tmp_buf) {
				tmp_buf = vmalloc(len);
				if (!tmp_buf)
					return -ENOMEM;
				memcpy(tmp_buf, p->buf, p->buf_len);
				kfree(p->buf);
				p->virtual_mem = 1;
			}
		}
		p->buf = tmp_buf;
		p->buf_len = len;
	}
	if (p->reversed) {
		tmp_buf = p->buf + old_buf_len - path_len - 1;
		p->end = p->buf + p->buf_len - 1;
		p->start = p->end - path_len;
		memmove(p->start, tmp_buf, path_len + 1);
	} else {
		p->start = p->buf;
		p->end = p->start + path_len;
	}
	return 0;
}

static int fs_path_prepare_for_add(struct fs_path *p, int name_len)
{
	int ret;
	int new_len;

	new_len = p->end - p->start + name_len;
	if (p->start != p->end)
		new_len++;
	ret = fs_path_ensure_buf(p, new_len);
	if (ret < 0)
		goto out;

	if (p->reversed) {
		if (p->start != p->end)
			*--p->start = '/';
		p->start -= name_len;
		p->prepared = p->start;
	} else {
		if (p->start != p->end)
			*p->end++ = '/';
		p->prepared = p->end;
		p->end += name_len;
		*p->end = 0;
	}

out:
	return ret;
}

static int fs_path_add(struct fs_path *p, char *name, int name_len)
{
	int ret;

	ret = fs_path_prepare_for_add(p, name_len);
	if (ret < 0)
		goto out;
	memcpy(p->prepared, name, name_len);
	p->prepared = NULL;

out:
	return ret;
}

static int fs_path_add_path(struct fs_path *p, struct fs_path *p2)
{
	int ret;

	ret = fs_path_prepare_for_add(p, p2->end - p2->start);
	if (ret < 0)
		goto out;
	memcpy(p->prepared, p2->start, p2->end - p2->start);
	p->prepared = NULL;

out:
	return ret;
}

static int fs_path_add_from_extent_buffer(struct fs_path *p,
					  struct extent_buffer *eb,
					  unsigned long off, int len)
{
	int ret;

	ret = fs_path_prepare_for_add(p, len);
	if (ret < 0)
		goto out;

	read_extent_buffer(eb, p->prepared, off, len);
	p->prepared = NULL;

out:
	return ret;
}

static int fs_path_copy(struct fs_path *p, struct fs_path *from)
{
	int ret;

	p->reversed = from->reversed;
	fs_path_reset(p);

	ret = fs_path_add_path(p, from);

	return ret;
}


static void fs_path_unreverse(struct fs_path *p)
{
	char *tmp;
	int len;

	if (!p->reversed)
		return;

	tmp = p->start;
	len = p->end - p->start;
	p->start = p->buf;
	p->end = p->start + len;
	memmove(p->start, tmp, len + 1);
	p->reversed = 0;
}

static struct btrfs_path *alloc_path_for_send(void)
{
	struct btrfs_path *path;

	path = btrfs_alloc_path();
	if (!path)
		return NULL;
	path->search_commit_root = 1;
	path->skip_locking = 1;
	return path;
}

static int write_buf(struct send_ctx *sctx, const void *buf, u32 len)
{
	int ret;
	mm_segment_t old_fs;
	u32 pos = 0;

	old_fs = get_fs();
	set_fs(KERNEL_DS);

	while (pos < len) {
		ret = vfs_write(sctx->send_filp, (char *)buf + pos, len - pos,
				&sctx->send_off);
		/* TODO handle that correctly */
		/*if (ret == -ERESTARTSYS) {
			continue;
		}*/
		if (ret < 0) {
			printk("%d\n", ret);
			goto out;
		}
		if (ret == 0) {
			ret = -EIO;
			goto out;
		}
		pos += ret;
	}

	ret = 0;

out:
	set_fs(old_fs);
	return ret;
}

static int tlv_put(struct send_ctx *sctx, u16 attr, const void *data, int len)
{
	struct btrfs_tlv_header *hdr;
	int total_len = sizeof(*hdr) + len;
	int left = sctx->send_max_size - sctx->send_size;

	if (unlikely(left < total_len))
		return -EOVERFLOW;

	hdr = (struct btrfs_tlv_header *) (sctx->send_buf + sctx->send_size);
	hdr->tlv_type = cpu_to_le16(attr);
	hdr->tlv_len = cpu_to_le16(len);
	memcpy(hdr + 1, data, len);
	sctx->send_size += total_len;

	return 0;
}

#if 0
static int tlv_put_u8(struct send_ctx *sctx, u16 attr, u8 value)
{
	return tlv_put(sctx, attr, &value, sizeof(value));
}

static int tlv_put_u16(struct send_ctx *sctx, u16 attr, u16 v)
{
	__le16 tmp = cpu_to_le16(value);
	return tlv_put(sctx, attr, &tmp, sizeof(tmp));
}

static int tlv_put_u32(struct send_ctx *sctx, u16 attr, u32 value)
{
	__le32 tmp = cpu_to_le32(value);
	return tlv_put(sctx, attr, &tmp, sizeof(tmp));
}
#endif

static int tlv_put_u64(struct send_ctx *sctx, u16 attr, u64 value)
{
	__le64 tmp = cpu_to_le64(value);
	return tlv_put(sctx, attr, &tmp, sizeof(tmp));
}

static int tlv_put_string(struct send_ctx *sctx, u16 attr,
			  const char *str, int len)
{
	if (len == -1)
		len = strlen(str);
	return tlv_put(sctx, attr, str, len);
}

static int tlv_put_uuid(struct send_ctx *sctx, u16 attr,
			const u8 *uuid)
{
	return tlv_put(sctx, attr, uuid, BTRFS_UUID_SIZE);
}

#if 0
static int tlv_put_timespec(struct send_ctx *sctx, u16 attr,
			    struct timespec *ts)
{
	struct btrfs_timespec bts;
	bts.sec = cpu_to_le64(ts->tv_sec);
	bts.nsec = cpu_to_le32(ts->tv_nsec);
	return tlv_put(sctx, attr, &bts, sizeof(bts));
}
#endif

static int tlv_put_btrfs_timespec(struct send_ctx *sctx, u16 attr,
				  struct extent_buffer *eb,
				  struct btrfs_timespec *ts)
{
	struct btrfs_timespec bts;
	read_extent_buffer(eb, &bts, (unsigned long)ts, sizeof(bts));
	return tlv_put(sctx, attr, &bts, sizeof(bts));
}


#define TLV_PUT(sctx, attrtype, attrlen, data) \
	do { \
		ret = tlv_put(sctx, attrtype, attrlen, data); \
		if (ret < 0) \
			goto tlv_put_failure; \
	} while (0)

#define TLV_PUT_INT(sctx, attrtype, bits, value) \
	do { \
		ret = tlv_put_u##bits(sctx, attrtype, value); \
		if (ret < 0) \
			goto tlv_put_failure; \
	} while (0)

#define TLV_PUT_U8(sctx, attrtype, data) TLV_PUT_INT(sctx, attrtype, 8, data)
#define TLV_PUT_U16(sctx, attrtype, data) TLV_PUT_INT(sctx, attrtype, 16, data)
#define TLV_PUT_U32(sctx, attrtype, data) TLV_PUT_INT(sctx, attrtype, 32, data)
#define TLV_PUT_U64(sctx, attrtype, data) TLV_PUT_INT(sctx, attrtype, 64, data)
#define TLV_PUT_STRING(sctx, attrtype, str, len) \
	do { \
		ret = tlv_put_string(sctx, attrtype, str, len); \
		if (ret < 0) \
			goto tlv_put_failure; \
	} while (0)
#define TLV_PUT_PATH(sctx, attrtype, p) \
	do { \
		ret = tlv_put_string(sctx, attrtype, p->start, \
			p->end - p->start); \
		if (ret < 0) \
			goto tlv_put_failure; \
	} while(0)
#define TLV_PUT_UUID(sctx, attrtype, uuid) \
	do { \
		ret = tlv_put_uuid(sctx, attrtype, uuid); \
		if (ret < 0) \
			goto tlv_put_failure; \
	} while (0)
#define TLV_PUT_TIMESPEC(sctx, attrtype, ts) \
	do { \
		ret = tlv_put_timespec(sctx, attrtype, ts); \
		if (ret < 0) \
			goto tlv_put_failure; \
	} while (0)
#define TLV_PUT_BTRFS_TIMESPEC(sctx, attrtype, eb, ts) \
	do { \
		ret = tlv_put_btrfs_timespec(sctx, attrtype, eb, ts); \
		if (ret < 0) \
			goto tlv_put_failure; \
	} while (0)

static int send_header(struct send_ctx *sctx)
{
	int ret;
	struct btrfs_stream_header hdr;

	strcpy(hdr.magic, BTRFS_SEND_STREAM_MAGIC);
	hdr.version = cpu_to_le32(BTRFS_SEND_STREAM_VERSION);

	ret = write_buf(sctx, &hdr, sizeof(hdr));

	return ret;
}

/*
 * For each command/item we want to send to userspace, we call this function.
 */
static int begin_cmd(struct send_ctx *sctx, int cmd)
{
	int ret = 0;
	struct btrfs_cmd_header *hdr;

	if (!sctx->send_buf) {
		WARN_ON(1);
		return -EINVAL;
	}

	BUG_ON(!sctx->send_buf);
	BUG_ON(sctx->send_size);

	sctx->send_size += sizeof(*hdr);
	hdr = (struct btrfs_cmd_header *)sctx->send_buf;
	hdr->cmd = cpu_to_le16(cmd);

	return ret;
}

static int send_cmd(struct send_ctx *sctx)
{
	int ret;
	struct btrfs_cmd_header *hdr;
	u32 crc;

	hdr = (struct btrfs_cmd_header *)sctx->send_buf;
	hdr->len = cpu_to_le32(sctx->send_size - sizeof(*hdr));
	hdr->crc = 0;

	crc = crc32c(0, (unsigned char *)sctx->send_buf, sctx->send_size);
	hdr->crc = cpu_to_le32(crc);

	ret = write_buf(sctx, sctx->send_buf, sctx->send_size);

	sctx->total_send_size += sctx->send_size;
	sctx->cmd_send_size[le16_to_cpu(hdr->cmd)] += sctx->send_size;
	sctx->send_size = 0;

	return ret;
}

/*
 * Sends a move instruction to user space
 */
static int send_rename(struct send_ctx *sctx,
		     struct fs_path *from, struct fs_path *to)
{
	int ret;

verbose_printk("btrfs: send_rename %s -> %s\n", from->start, to->start);

	ret = begin_cmd(sctx, BTRFS_SEND_C_RENAME);
	if (ret < 0)
		goto out;

	TLV_PUT_PATH(sctx, BTRFS_SEND_A_PATH, from);
	TLV_PUT_PATH(sctx, BTRFS_SEND_A_PATH_TO, to);

	ret = send_cmd(sctx);

tlv_put_failure:
out:
	return ret;
}

/*
 * Sends a link instruction to user space
 */
static int send_link(struct send_ctx *sctx,
		     struct fs_path *path, struct fs_path *lnk)
{
	int ret;

verbose_printk("btrfs: send_link %s -> %s\n", path->start, lnk->start);

	ret = begin_cmd(sctx, BTRFS_SEND_C_LINK);
	if (ret < 0)
		goto out;

	TLV_PUT_PATH(sctx, BTRFS_SEND_A_PATH, path);
	TLV_PUT_PATH(sctx, BTRFS_SEND_A_PATH_LINK, lnk);

	ret = send_cmd(sctx);

tlv_put_failure:
out:
	return ret;
}

/*
 * Sends an unlink instruction to user space
 */
static int send_unlink(struct send_ctx *sctx, struct fs_path *path)
{
	int ret;

verbose_printk("btrfs: send_unlink %s\n", path->start);

	ret = begin_cmd(sctx, BTRFS_SEND_C_UNLINK);
	if (ret < 0)
		goto out;

	TLV_PUT_PATH(sctx, BTRFS_SEND_A_PATH, path);

	ret = send_cmd(sctx);

tlv_put_failure:
out:
	return ret;
}

/*
 * Sends a rmdir instruction to user space
 */
static int send_rmdir(struct send_ctx *sctx, struct fs_path *path)
{
	int ret;

verbose_printk("btrfs: send_rmdir %s\n", path->start);

	ret = begin_cmd(sctx, BTRFS_SEND_C_RMDIR);
	if (ret < 0)
		goto out;

	TLV_PUT_PATH(sctx, BTRFS_SEND_A_PATH, path);

	ret = send_cmd(sctx);

tlv_put_failure:
out:
	return ret;
}

/*
 * Helper function to retrieve some fields from an inode item.
 */
static int get_inode_info(struct btrfs_root *root,
			  u64 ino, u64 *size, u64 *gen,
			  u64 *mode, u64 *uid, u64 *gid)
{
	int ret;
	struct btrfs_inode_item *ii;
	struct btrfs_key key;
	struct btrfs_path *path;

	path = alloc_path_for_send();
	if (!path)
		return -ENOMEM;

	key.objectid = ino;
	key.type = BTRFS_INODE_ITEM_KEY;
	key.offset = 0;
	ret = btrfs_search_slot(NULL, root, &key, path, 0, 0);
	if (ret < 0)
		goto out;
	if (ret) {
		ret = -ENOENT;
		goto out;
	}

	ii = btrfs_item_ptr(path->nodes[0], path->slots[0],
			struct btrfs_inode_item);
	if (size)
		*size = btrfs_inode_size(path->nodes[0], ii);
	if (gen)
		*gen = btrfs_inode_generation(path->nodes[0], ii);
	if (mode)
		*mode = btrfs_inode_mode(path->nodes[0], ii);
	if (uid)
		*uid = btrfs_inode_uid(path->nodes[0], ii);
	if (gid)
		*gid = btrfs_inode_gid(path->nodes[0], ii);

out:
	btrfs_free_path(path);
	return ret;
}

typedef int (*iterate_inode_ref_t)(int num, u64 dir, int index,
				   struct fs_path *p,
				   void *ctx);

/*
 * Helper function to iterate the entries in ONE btrfs_inode_ref.
 * The iterate callback may return a non zero value to stop iteration. This can
 * be a negative value for error codes or 1 to simply stop it.
 *
 * path must point to the INODE_REF when called.
 */
static int iterate_inode_ref(struct send_ctx *sctx,
			     struct btrfs_root *root, struct btrfs_path *path,
			     struct btrfs_key *found_key, int resolve,
			     iterate_inode_ref_t iterate, void *ctx)
{
	struct extent_buffer *eb;
	struct btrfs_item *item;
	struct btrfs_inode_ref *iref;
	struct btrfs_path *tmp_path;
	struct fs_path *p;
	u32 cur;
	u32 len;
	u32 total;
	int slot;
	u32 name_len;
	char *start;
	int ret = 0;
	int num;
	int index;

	p = fs_path_alloc_reversed(sctx);
	if (!p)
		return -ENOMEM;

	tmp_path = alloc_path_for_send();
	if (!tmp_path) {
		fs_path_free(sctx, p);
		return -ENOMEM;
	}

	eb = path->nodes[0];
	slot = path->slots[0];
	item = btrfs_item_nr(eb, slot);
	iref = btrfs_item_ptr(eb, slot, struct btrfs_inode_ref);
	cur = 0;
	len = 0;
	total = btrfs_item_size(eb, item);

	num = 0;
	while (cur < total) {
		fs_path_reset(p);

		name_len = btrfs_inode_ref_name_len(eb, iref);
		index = btrfs_inode_ref_index(eb, iref);
		if (resolve) {
			start = btrfs_iref_to_path(root, tmp_path, iref, eb,
						found_key->offset, p->buf,
						p->buf_len);
			if (IS_ERR(start)) {
				ret = PTR_ERR(start);
				goto out;
			}
			if (start < p->buf) {
				/* overflow , try again with larger buffer */
				ret = fs_path_ensure_buf(p,
						p->buf_len + p->buf - start);
				if (ret < 0)
					goto out;
				start = btrfs_iref_to_path(root, tmp_path, iref,
						eb, found_key->offset, p->buf,
						p->buf_len);
				if (IS_ERR(start)) {
					ret = PTR_ERR(start);
					goto out;
				}
				BUG_ON(start < p->buf);
			}
			p->start = start;
		} else {
			ret = fs_path_add_from_extent_buffer(p, eb,
					(unsigned long)(iref + 1), name_len);
			if (ret < 0)
				goto out;
		}


		len = sizeof(*iref) + name_len;
		iref = (struct btrfs_inode_ref *)((char *)iref + len);
		cur += len;

		ret = iterate(num, found_key->offset, index, p, ctx);
		if (ret < 0)
			goto out;
		if (ret) {
			ret = 0;
			goto out;
		}

		num++;
	}

out:
	btrfs_free_path(tmp_path);
	fs_path_free(sctx, p);
	return ret;
}

typedef int (*iterate_dir_item_t)(int num, const char *name, int name_len,
				  const char *data, int data_len,
				  u8 type, void *ctx);

/*
 * Helper function to iterate the entries in ONE btrfs_dir_item.
 * The iterate callback may return a non zero value to stop iteration. This can
 * be a negative value for error codes or 1 to simply stop it.
 *
 * path must point to the dir item when called.
 */
static int iterate_dir_item(struct send_ctx *sctx,
			    struct btrfs_root *root, struct btrfs_path *path,
			    struct btrfs_key *found_key,
			    iterate_dir_item_t iterate, void *ctx)
{
	int ret = 0;
	struct extent_buffer *eb;
	struct btrfs_item *item;
	struct btrfs_dir_item *di;
	struct btrfs_path *tmp_path = NULL;
	char *buf = NULL;
	char *buf2 = NULL;
	int buf_len;
	int buf_virtual = 0;
	u32 name_len;
	u32 data_len;
	u32 cur;
	u32 len;
	u32 total;
	int slot;
	int num;
	u8 type;

	buf_len = PAGE_SIZE;
	buf = kmalloc(buf_len, GFP_NOFS);
	if (!buf) {
		ret = -ENOMEM;
		goto out;
	}

	tmp_path = alloc_path_for_send();
	if (!tmp_path) {
		ret = -ENOMEM;
		goto out;
	}

	eb = path->nodes[0];
	slot = path->slots[0];
	item = btrfs_item_nr(eb, slot);
	di = btrfs_item_ptr(eb, slot, struct btrfs_dir_item);
	cur = 0;
	len = 0;
	total = btrfs_item_size(eb, item);

	num = 0;
	while (cur < total) {
		name_len = btrfs_dir_name_len(eb, di);
		data_len = btrfs_dir_data_len(eb, di);
		type = btrfs_dir_type(eb, di);

		if (name_len + data_len > buf_len) {
			buf_len = PAGE_ALIGN(name_len + data_len);
			if (buf_virtual) {
				buf2 = vmalloc(buf_len);
				if (!buf2) {
					ret = -ENOMEM;
					goto out;
				}
				vfree(buf);
			} else {
				buf2 = krealloc(buf, buf_len, GFP_NOFS);
				if (!buf2) {
					buf2 = vmalloc(buf_len);
					if (!buf) {
						ret = -ENOMEM;
						goto out;
					}
					kfree(buf);
					buf_virtual = 1;
				}
			}

			buf = buf2;
			buf2 = NULL;
		}

		read_extent_buffer(eb, buf, (unsigned long)(di + 1),
				name_len + data_len);

		len = sizeof(*di) + name_len + data_len;
		di = (struct btrfs_dir_item *)((char *)di + len);
		cur += len;

		ret = iterate(num, buf, name_len, buf + name_len, data_len,
				type, ctx);
		if (ret < 0)
			goto out;
		if (ret) {
			ret = 0;
			goto out;
		}

		num++;
	}

out:
	btrfs_free_path(tmp_path);
	if (buf_virtual)
		vfree(buf);
	else
		kfree(buf);
	return ret;
}

static int __copy_first_ref(int num, u64 dir, int index,
			    struct fs_path *p, void *ctx)
{
	int ret;
	struct fs_path *pt = ctx;

	ret = fs_path_copy(pt, p);
	if (ret < 0)
		return ret;

	/* we want the first only */
	return 1;
}

/*
 * Retrieve the first path of an inode. If an inode has more then one
 * ref/hardlink, this is ignored.
 */
static int get_inode_path(struct send_ctx *sctx, struct btrfs_root *root,
			  u64 ino, struct fs_path *path)
{
	int ret;
	struct btrfs_key key, found_key;
	struct btrfs_path *p;

	p = alloc_path_for_send();
	if (!p)
		return -ENOMEM;

	fs_path_reset(path);

	key.objectid = ino;
	key.type = BTRFS_INODE_REF_KEY;
	key.offset = 0;

	ret = btrfs_search_slot_for_read(root, &key, p, 1, 0);
	if (ret < 0)
		goto out;
	if (ret) {
		ret = 1;
		goto out;
	}
	btrfs_item_key_to_cpu(p->nodes[0], &found_key, p->slots[0]);
	if (found_key.objectid != ino ||
		found_key.type != BTRFS_INODE_REF_KEY) {
		ret = -ENOENT;
		goto out;
	}

	ret = iterate_inode_ref(sctx, root, p, &found_key, 1,
			__copy_first_ref, path);
	if (ret < 0)
		goto out;
	ret = 0;

out:
	btrfs_free_path(p);
	return ret;
}

