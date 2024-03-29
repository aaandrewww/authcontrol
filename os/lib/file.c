#include <inc/lib.h>
#include <inc/trap.h>
#include <inc/mmu.h>
#include <inc/fs.h>
#include <inc/x86.h>

// Maximum disk size we can handle (2GB).
#define DISKSIZE	0x80000000

// File system blocks are mapped into virtual memory starting at FSMAP.
#define FSMAP		0x50000000

// The file system superblock is always block 1.
static struct Super *super = (struct Super *) (FSMAP + BLKSIZE);
// The freemap always starts at block 2.
static int8_t *freemap = (int8_t *) (FSMAP + 2 * BLKSIZE);

static int inode_set_size(struct Inode *ino, size_t size);


static int flushpipe = -1;

static lock_t flushpipe_lock = 0;

// Buffer cache IPC helper function.
// Send a buffer cache 'reqtype' IPC (one of the BCREQ_ constants)
// for the file system block containing 'addr'.
// Returns 0 on success, < 0 on error.
//
static int
bcache_ipc(void *addr, int reqtype)
{
	int r;
	blocknum_t b = ((uintptr_t) addr - FSMAP) / BLKSIZE;

	if (b < 0 || b > (blocknum_t) (DISKSIZE / BLKSIZE))
		panic("bcache_ipc: va %08x out of disk address range", addr);
	// Be careful: check 'super' might not be loaded!
	if (b >= 2 && b >= super->s_nblocks)
		panic("bcache_ipc: block %d out of file system bounds", b);

	if (reqtype == BCREQ_FLUSH) {
		if (flushpipe < 0) {
			lock(&flushpipe_lock);
			if (flushpipe < 0) {
				int fp[2];
				struct Fd *fd;
				if ((r = pipe(fp)) < 0) {
					unlock(&flushpipe_lock);
					return r;
				}
				if ((r = fd_lookup(fp[1], &fd, true)) < 0) {
					unlock(&flushpipe_lock);
					return r;
				}
				do {
					ipc_send(ENVID_BUFCACHE, BCREQ_PIPE_ATTACH, 0, 0);
					r = ipc_recv(0, fd2data(fd), 0);
				} while (r == -E_AGAIN);
				if (r < 0) {
					unlock(&flushpipe_lock);
					return r;
				}
				flushpipe = fp[1];
				close(fp[0]);
			}
			unlock(&flushpipe_lock);
		}
		uint32_t flushrequest = MAKE_BCREQ(b,reqtype);
		while (write(flushpipe,&flushrequest,sizeof(uint32_t)) != sizeof(uint32_t)) {
			ipc_send(ENVID_BUFCACHE, BCREQ_FLUSH_PIPE, 0, 0);
		}
		return 0;
	} else {
		do {
			ipc_send(ENVID_BUFCACHE, MAKE_BCREQ(b, reqtype), 0, 0);
			r = ipc_recv(0, (void *) (FSMAP + b * PGSIZE), 0);
		} while (r == -E_AGAIN);
	}
	
	return r;
}


// Buffer cache page fault handler.
// If the page fault is in the disk area, load the page from the buffer cache
// (without locking).  Use bcache_ipc, then call resume() on success.
// Panic if the load fails.
// If the fault isn't in the disk area, return so other handlers run.
//
static void
bcache_pgfault_handler(struct UTrapframe *utf)
{
	// LAB 5: Your code here.
	int ret;
	uintptr_t va = utf->utf_fault_va;
	if (va >= FSMAP && va < FSMAP+DISKSIZE) {
		if ((ret = bcache_ipc((void *)va, BCREQ_MAP)) < 0) {
			panic("bcache request failed: %e", ret);
		} else {
			resume(utf);
		}
	}
}


// Return a pointer to inode number 'inum'.
// The inode might not be in memory right now (it should be demand paged).
//
static struct Inode *
get_inode(int inum)
{
	blocknum_t b = 1 + ROUNDUP(super->s_nblocks, PGSIZE) / PGSIZE + inum;
	if (inum == 0 || inum > super->s_ninodes)
		panic("inode %d out of range", inum);
	return (struct Inode *) (FSMAP + b * BLKSIZE);
}

// Open inode number 'inum'.
// A pointer to the inode is stored in '*ino_store'.
// The inode is locked exclusively, and its 'i_opencount' is incremented.
// On the first read from disk, the memory-only fields are initialized
// to sensible values.
// Every inode_open() must be balanced by an inode_close().
// Returns 0 on success, < 0 on failure.
//
static int
inode_open(int inum, struct Inode **ino_store)
{
	int r;
	struct Inode *ino;

	// Always make sure our pagefault handler is installed.
	add_pgfault_handler(bcache_pgfault_handler);

	ino = get_inode(inum);
	r = bcache_ipc(ino, BCREQ_MAP_WLOCK);
	if (r < 0) {
		*ino_store = 0;
		return r;
	}

	// Initialize memory-only fields when an inode is first read from disk.
	if (r == 0) {		// i.e., the block has not been INITIALIZEd
		ino->i_inum = inum;
		ino->i_opencount = 0;
		bcache_ipc(ino, BCREQ_INITIALIZE);
	}

	// Account for our reservation and return.
	++ino->i_opencount;
	*ino_store = ino;
	return 0;
}

// Close inode 'ino' (the converse of inode_open).
// Reduce its i_opencount and unlock the corresponding block.
// If the inode is now free, then free the corresponding data blocks.
//
static int
inode_close(struct Inode *ino)
{
	--ino->i_opencount;

	// The inode might now be free.
	// If no references remain on disk or in memory, then free the
	// corresponding data blocks.
	//
	// LAB 5: Your code here.
	int ret;
	if (ino->i_refcount == 0 && ino->i_opencount == 0) {
		// No references remain, free data blocks
		for (uint32_t i = 0; i < NDIRECT; i++) {
			blocknum_t block = ino->i_direct[i];
			do {
				ret = bcache_ipc(&freemap[block], BCREQ_MAP_WLOCK);
			} while (ret == -E_AGAIN);
			if (block) {
				freemap[block] = 1;
				bcache_ipc(&freemap[block], BCREQ_UNLOCK_FLUSH);
			} else {
				bcache_ipc(&freemap[block], BCREQ_UNLOCK);
			}
		}
	}

	return bcache_ipc(ino, BCREQ_UNLOCK);
}

// Allocate a new inode, storing the result in '*ino_store'.
// Returns 0 on success, < 0 on error.
// Error codes:
//	-E_NO_DISK if there are no free inodes
//	Other codes from inode_open
// The newly allocated inode is locked exclusively
// and must be closed with inode_close().
//
// The newly allocated inode still has no proper references
// and its contents are unchanged, except for the memory-only fields
// i_opencount and i_inum.
// The caller is expected to increment i_refcount and initialize
// its contents as required.
//
static int
inode_alloc(struct Inode **ino_store)
{
	inum_t inum;
	int r;
	struct Inode *ino;
	*ino_store = 0;
	for (inum = 2; inum < super->s_ninodes; ++inum) {
		if ((r = inode_open(inum, &ino)) < 0)
			return r;
		if (ino->i_refcount == 0 && ino->i_opencount == 1) {
			*ino_store = ino;
			return 0;
		}
		inode_close(ino);
	}
	return -E_NO_DISK;
}


// Allocate a block, marking it as allocated in the freemap.
// Returns the block number or < 0 on error.
// Error codes:
//	-E_NO_DISK if there are no free blocks
//
static blocknum_t
block_alloc(void)
{
	// Find a free block, allocate it, and return its number.
	// Use block locking to avoid concurrency issues -- but try to
	// avoid unnecessary IPCs.
	//
	// LAB 5: Your code here.
	int ret;

	for (blocknum_t block = 0; block < super->s_nblocks; block++) {
		// Does double-check locking work in C?
		if (freemap[block]) {
			void *blockaddr = (void *)&freemap[block];
			do {
				ret = bcache_ipc(blockaddr,BCREQ_MAP_WLOCK);
			} while (ret == -E_AGAIN);
			// Have a lock on the block
			if (freemap[block]) {
				freemap[block] = 0;
				bcache_ipc(blockaddr,BCREQ_UNLOCK_FLUSH);
				return block;
			}
			bcache_ipc(blockaddr,BCREQ_UNLOCK);
		}
	}

	return -E_NO_DISK;
}

// Returns a pointer into the FSMAP region for the data at byte 'off'
// in the file 'ino'.
// Returns NULL if 'off' is out of range for the file.
//
static void *
inode_data(struct Inode *ino, off_t off)
{
	blocknum_t blocknum;
	if (off < 0 || off >= ino->i_size)
		return 0;
	blocknum = ino->i_direct[off / PGSIZE];
	return (void *) (FSMAP + blocknum * BLKSIZE + off % PGSIZE);
}

// Sets inode 'ino's size to 'size',
// either allocating or freeing data blocks as required.
// Returns 0 on success, < 0 on error.
// Error codes:
//	-E_FILE_SIZE if 'size' is too big
//	-E_NO_DISK if out of disk space
//	possibly others
// On error, the inode's size and disk's allocation state should be unchanged.
// On success, any changed blocks are flushed.
//
static int
inode_set_size(struct Inode *ino, size_t size)
{
	// This function is correct as far as it goes, but does not handle
	// all cases.  Read the spec carefully: what is missing?
	// LAB 5: Your code somewhere here

	int b1, b2, ret;
	blocknum_t block;

	if (size > MAXFILESIZE)
		return -E_FILE_SIZE;

	b1 = ino->i_size / BLKSIZE;
	b2 = ROUNDUP(size, BLKSIZE) / BLKSIZE;
	for (; b1 < b2; ++b1)
		if (ino->i_direct[b1] == 0) {
			blocknum_t b = block_alloc();
			if (b < 0) {
				inode_set_size(ino, ino->i_size);
				return -E_NO_DISK;
			}
			ino->i_direct[b1] = b;
		}
	for (b1--; b2 < b1; --b1)
		if (ino->i_direct[b1] != 0) {
			// Free this block
			block = ino->i_direct[b1];
			do {
				ret = bcache_ipc(&freemap[block], BCREQ_MAP_WLOCK);
			} while (ret == -E_AGAIN);
			freemap[block] = 1;
			bcache_ipc(&freemap[block], BCREQ_UNLOCK_FLUSH);
		}

	if (ino->i_size != (off_t) size) {
		ino->i_size = size;
		bcache_ipc(ino, BCREQ_FLUSH);
	}
	return 0;
}


// Find a directory entry in the 'ino' directory.
// Looks for name 'name' with length 'namelen'.
// If 'create != 0', such an entry is created if none is found.
//   A newly created entry will have de_inum == 0.
// Returns 0 on success (storing a pointer to the struct Direntry in
//   *de_store), and < 0 on error.
// Error codes:
//	-E_BAD_PATH if 'ino' is not a directory.
//	-E_NO_DISK if out of space.
//	(possibly others)
//
static int
dir_find(struct Inode *ino, const char *name, int namelen,
	 struct Direntry **de_store, int create)
{
	off_t off;
	struct Direntry *empty = 0;

	*de_store = 0;

	if (ino->i_ftype != FTYPE_DIR)
		return -E_BAD_PATH;

	for (off = 0; off < ino->i_size; off += sizeof(struct Direntry)) {
		struct Direntry *de = (struct Direntry *) inode_data(ino, off);

		if (de->de_inum != 0
		    && de->de_namelen == namelen
		    && memcmp(de->de_name, name, namelen) == 0) {
			*de_store = de;
			return 0;
		}

		if (de->de_inum == 0 && !empty)
			empty = de;
	}

	if (!create)
		return -E_NOT_FOUND;

	if (!empty) {
		int r = inode_set_size(ino, ino->i_size + sizeof(struct Direntry));
		if (r < 0)
			return r;
		empty = (struct Direntry *) inode_data(ino, ino->i_size - sizeof(struct Direntry));
	}

	memset(empty, 0, sizeof(struct Direntry));
	empty->de_namelen = namelen;
	memcpy(empty->de_name, name, namelen);
	*de_store = empty;
	return 0;
}

static const char *
path_next_component(const char *path,
		    const char **component, int *component_len)
{
	while (*path == '/')
		++path;
	*component = path;
	while (*path != '/' && *path != 0)
		++path;
	*component_len = path - *component;
	while (*path == '/')
		++path;
	return path;
}

// Walks 'path' down the file system.
// Stores the rightmost directory inode in '*dirino_store',
// and a pointer to the directory entry in '*de_store'.
// For instance, if path == "/a/b/c/hello",
// then '*dirino_store' is the inode for "/a/b/c"
// and '*de_store' points to the embedded directory entry for "hello".
// If 'create != 0', the final directory entry is created if necessary.
//   A newly created entry will have 'de_inum == 0'.  (All real entries have
//   'de_inum != 0'.)
// On success, '*dirino_store' is locked and must be closed with
// inode_close().
//
// Returns 0 on success, < 0 on error.
// Error codes: See dir_find().
//
static int
path_walk(const char *path,
	  struct Inode **dirino_store, struct Direntry **de_store,
	  int create)
{
	int r;
	struct Inode *ino, *next_ino;
	struct Direntry *de;
	const char *component;
	int component_len;

	*dirino_store = 0;
	*de_store = 0;
	if ((r = inode_open(1, &ino)) < 0)
		return r;

	while (1) {
		// Find next path component
		path = path_next_component(path, &component, &component_len);

		// Special case: root directory
		if (component_len == 0) {
			*dirino_store = ino;
			*de_store = &super->s_root;
			return 0;
		}

		// Look up directory component
		// (This is the last path component iff *path == 0.)
		if ((r = dir_find(ino, component, component_len, &de,
				  create && *path == 0)) < 0)
			goto fail;

		// If done, return this direntry
		if (*path == 0) {
			*dirino_store = ino;
			*de_store = de;
			return 0;
		}

		// Otherwise, walk into subdirectory.
		// Always open the next inode before closing the current one.
		if ((r = inode_open(de->de_inum, &next_ino)) < 0)
			goto fail;
		inode_close(ino);
		ino = next_ino;
	}

 fail:
	inode_close(ino);
	return r;
}



static int devfile_close(struct Fd *fd);
static ssize_t devfile_read(struct Fd *fd, void *buf, size_t n);
static ssize_t devfile_write(struct Fd *fd, const void *buf, size_t n);
static int devfile_stat(struct Fd *fd, struct Stat *stat);
static int devfile_trunc(struct Fd *fd, off_t newsize);

struct Dev devfile =
{
	/* .dev_id = */		'f',
	/* .dev_name = */	"file",
	/* .dev_read = */	devfile_read,
	/* .dev_write = */	devfile_write,
	/* .dev_close = */	devfile_close,
	/* .dev_stat = */	devfile_stat,
	/* .dev_trunc =	*/	devfile_trunc
};

// Open a file (or directory).
//
// Returns:
// 	The file descriptor index on success
// 	-E_BAD_PATH if the path is too long (>= MAXPATHLEN)
//	-E_BAD_PATH if an intermediate path component is not a directory
//	-E_MAX_FD if no more file descriptors
//	-E_NOT_FOUND if the file (or a path component) was not found
//	(and others)
int
open(const char *path, int mode)
{
	// Find an unused file descriptor page using fd_find_unused
	// and allocate a page there (PTE_P|PTE_U|PTE_W|PTE_SHARE).
	//
	// LAB 5: Your code here.
	int ret;
	Fd *fd;
	struct Inode *dirInode;
	struct Direntry *dirEntry;
	struct Inode *fileInode;

	if ((ret = fd_find_unused(&fd)) < 0) goto done;
	if ((ret = sys_page_alloc(0, fd, PTE_P | PTE_U | PTE_W | PTE_SHARE)) < 0) goto done;

	// Check the pathname.  Error if too long.
        // Use path_walk to find the corresponding directory entry.
	// If '(mode & O_CREAT) == 0' (Exercise 4),
	//   Return -E_NOT_FOUND if the file is not found.
	//   Otherwise, use inode_open to open the inode.
	// If '(mode & O_CREAT) != 0' (Exercise 7),
	//   Create the file if it doesn't exist yet.
	//   Allocate a new inode, initialize its fields, and
	//   reference that inode from the new directory entry.
	//   Flush any blocks you change.
	// Directories can be opened, but only as read-only:
	// return -E_IS_DIR if '(mode & O_ACCMODE) != O_RDONLY'.
	//
	// Check for errors.  On error, make sure you clean up any
	// allocated objects.
	//
	// The root directory is a special case -- if you aren't careful,
	// you will deadlock when the root directory is opened.  (Why?)
	if (strlen(path) >= MAXPATHLEN) {
		ret = -E_BAD_PATH;
		goto done;
	}
	if ((mode & O_CREAT) == 0) {
		if ((ret = path_walk(path, &dirInode, &dirEntry, false)) < 0) {
			goto unallocatefd;
		}
	} else {
		if ((ret = path_walk(path, &dirInode, &dirEntry, true)) < 0) {
			goto unallocatefd;
		}
		if (dirEntry->de_inum == 0) {
			// Didn't find the file, but we should create it
			if ((ret = inode_alloc(&fileInode)) < 0) {
				goto unallocatefd;
			}
			// Initialize the inode's fields
			fileInode->i_ftype = FTYPE_REG;
			fileInode->i_refcount = 1;
			fileInode->i_size = 0;
			for (blocknum_t block = 0; block < NDIRECT; block++) {
				fileInode->i_direct[block] = 0;
			}
			dirEntry->de_inum = fileInode->i_inum;
			bcache_ipc(fileInode,BCREQ_FLUSH);
			bcache_ipc(dirInode,BCREQ_FLUSH);
			// Avoid a deadlock... inefficent but the logic is easier
			// than remembering to not open it again below
			inode_close(fileInode);
		}
	}
	if (dirEntry->de_inum == dirInode->i_inum) {
		// this is the root, fileInode is dirInode
		fileInode = dirInode;
	} else {
		// need to open the file's inode
		if ((ret = inode_open(dirEntry->de_inum, &fileInode)) < 0) {
			goto closedirinode;
		}
	}
	if ((fileInode->i_ftype == FTYPE_DIR) && ((mode & O_ACCMODE) != O_RDONLY)) {
		ret = -E_IS_DIR;
		goto closefileinode;
	}

	// If '(mode & O_TRUNC) != 0' and the open mode is not read-only,
	// set the file's length to 0.  Flush any blocks you change.
	//
	// LAB 5: Your code here (Exercise 8).
	if (((mode & O_TRUNC) != 0) && ((mode & O_ACCMODE) != O_RDONLY)) {
		if ((ret = inode_set_size(fileInode,0)) < 0) {
			goto closefileinode;
		}
	}

	// The open has succeeded.
	// Fill in all parts of the 'fd' appropriately.  Use 'devfile.dev_id'.
	// Copy the file's pathname into 'fd->fd_file.open_path' to improve
	// error messages later.
	// You must account for the open file reference in the inode as well.
	// Clean up any open inodes.
	//
	// LAB 5: Your code here (Exercise 4).
	fd->fd_dev_id = devfile.dev_id;
	fd->fd_offset = 0;
	fd->fd_omode = mode;
	strcpy(fd->fd_file.open_path, path);
	fd->fd_file.inum = fileInode->i_inum;

	ret = fd2num(fd);

	// CLEAN UP!
closefileinode:
	if (fileInode != dirInode) inode_close(fileInode);
closedirinode:
	inode_close(dirInode);
unallocatefd:
	if (ret < 0) sys_page_unmap(0, fd);
done:
	return ret;
}

// Close the file descriptor.
//
static int
devfile_close(struct Fd *fd)
{
	// If this call will close the last reference to the file descriptor,
	// then you must account for the outstanding open file reference
	// in the inode.
	// But the file descriptor might still be open elsewhere
	// (because of fork and dup).  Use pageref to check.
	//
	// LAB 5: Your code here.
	int ret;
	struct Inode *inode;
	if (pageref(fd) == 1) {
		if ((ret = inode_open(fd->fd_file.inum, &inode)) < 0) return ret;
		if ((ret = inode_close(inode)) < 0) return ret;
	}
	if ((ret = sys_page_unmap(0,fd)) < 0) {
		return ret;
	}

	return 0;
}

// Read at most 'n' bytes from 'fd' at the current position into 'buf'.
// Advance 'fd->f_offset' by the number of bytes read.
//
// Returns:
// 	The number of bytes successfully read.
// 	< 0 on error.
static ssize_t
devfile_read(struct Fd *fd, void *buf, size_t n)
{
	// Use inode_open, inode_close, and inode_data.
	// Be careful of block boundaries!
	//
	// Lab 5: Your code here.
	int ret;
	struct Inode *inode;
	
	// Try to open the files inode
	if ((ret = inode_open(fd->fd_file.inum, &inode)) < 0) return ret;
	
	// Start off needing to read n bytes
	size_t remaining = n;

	off_t start_offset = fd->fd_offset;
	off_t end_offset = 0;
	size_t available = 0;
	size_t to_read = 0;
	void *block_data = NULL;
	// While we haven't filled the buffer
	while (remaining > 0) {
		// If we're at the start of a block, can read a whole block, 
		// otherwise just to the end of the block
		end_offset = (start_offset % BLKSIZE) ? 
			ROUNDUP(start_offset, BLKSIZE) : start_offset + BLKSIZE;
		// Unless we've reaced the end of the file already
		end_offset = MIN(end_offset,inode->i_size);
		// Read from the current block either the remaining space in the
		// buffer, or the rest of the block, whichever is smaller
		available = end_offset - start_offset;
		to_read = MIN(available,remaining);

		// If inode_data returns non-null, we know it is safe to read
		// at least until the end of the block, so to_read is safe
		block_data = inode_data(inode,start_offset);
		if (!block_data) break;
		do {
			ret = bcache_ipc(block_data,BCREQ_MAP_WLOCK);
		} while (ret == -E_AGAIN);
		memcpy(buf,block_data,to_read);
		bcache_ipc(block_data, BCREQ_UNLOCK);
		
		// Record reading some bytes, move our pointer into the buffer,
		// and update our position in the file
		remaining -= to_read;
		buf = (void *)((char *)buf + to_read);
		start_offset = end_offset;
	}

	// Update the file descriptor offset
	size_t read = n - remaining;
	fd->fd_offset += read;

	if ((ret = inode_close(inode)) < 0) return ret;
	return read;
}

// Write at most 'n' bytes from 'buf' to 'fd' at the current seek position.
// Advance 'fd->f_offset' by the number of bytes written.
//
// Returns:
//	 The number of bytes successfully written.
//	 < 0 on error.
static ssize_t
devfile_write(struct Fd *fd, const void *buf, size_t n)
{
	// Use inode_open, inode_close, maybe inode_set_size, and inode_data.
	// Be careful of block boundaries!
	// Flush any blocks you change using BCREQ_FLUSH.
	//
	// LAB 5: Your code here.

	// Very similar to devfile_read()

	int ret;
	struct Inode *inode;
	
	// Try to open the files inode
	if ((ret = inode_open(fd->fd_file.inum, &inode)) < 0) return ret;

	// Make sure that the inode is big enough (i.e. at least as big as the
	// current offset + n). Then we don't habve to worry about allocation
	// in the rest of the function
	if (inode->i_size < fd->fd_offset + (off_t)n) {
		if ((ret = inode_set_size(inode, fd->fd_offset + n)) < 0) return ret;
	}

	// Start off needing to write n bytes
	size_t remaining = n;

	off_t start_offset = fd->fd_offset;
	off_t end_offset = 0;
	size_t available = 0;
	size_t to_write = 0;
	void *block_data = NULL;
	// While we haven't exhausted the buffer
	while (remaining > 0) {
		// If we're at the start of a block, can write a whole block, 
		//otherwise just to the end of the block
		end_offset = (start_offset % BLKSIZE) ? 
			ROUNDUP(start_offset, BLKSIZE) : start_offset + BLKSIZE;
		// Write to the current block either the remaining space in the
		// buffer, or the rest of the block, whichever is smaller
		available = end_offset - start_offset;
		to_write = MIN(available,remaining);

		// If inode_data returns non-null, we know it is safe to write
		// at least until the end of the block, so to_write is safe
		block_data = inode_data(inode,start_offset);
		if (!block_data) break;
		do {
			ret = bcache_ipc(block_data,BCREQ_MAP_WLOCK);
		} while (ret == -E_AGAIN);
		memcpy(block_data,buf,to_write);
		// Flush the block!
		bcache_ipc(block_data, BCREQ_UNLOCK_FLUSH);
		
		// Record reading some bytes, move our pointer into the buffer,
		// and update our position in the file
		remaining -= to_write;
		buf = (void *)((char *)buf + to_write);
		start_offset = end_offset;
	}

	// Update the file descriptor offset
	size_t written = n - remaining;
	fd->fd_offset += written;

	if ((ret = inode_close(inode)) < 0) return ret;
	return written;
}

static void
stat_base(const struct Inode *ino, struct Stat *stat)
{
	stat->st_size = ino->i_size;
	stat->st_ftype = ino->i_ftype;
	stat->st_dev = &devfile;
}

static int
devfile_stat(struct Fd *fd, struct Stat *stat)
{
	int r;
	struct Inode *ino;

	if ((r = inode_open(fd->fd_file.inum, &ino)) < 0)
		return r;

	strcpy(stat->st_name, fd->fd_file.open_path);
	stat_base(ino, stat);

	inode_close(ino);
	return 0;
}

int
istat(inum_t inum, struct Stat *stat)
{
	int r;
	struct Inode *ino;

	if ((r = inode_open(inum, &ino)) < 0)
		return r;

	strcpy(stat->st_name, "<inode>");
	stat_base(ino, stat);

	inode_close(ino);
	return 0;
}

// Truncate or extend an open file to 'size' bytes
static int
devfile_trunc(struct Fd *fd, off_t newsize)
{
	int r;
	struct Inode *ino;

	if ((r = inode_open(fd->fd_file.inum, &ino)) < 0)
		return r;

	r = inode_set_size(ino, newsize);

	inode_close(ino);
	return r;
}

// Deletes a file.
//
int
unlink(const char *path)
{
	int r;
	struct Inode *dirino, *ino;
	struct Direntry *de;

	if ((r = path_walk(path, &dirino, &de, 0)) < 0)
		goto done;
	if ((r = inode_open(de->de_inum, &ino)) < 0)
		goto closedirino;
	if (ino->i_ftype == FTYPE_DIR) {
		r = -E_IS_DIR;
		goto closeino;
	}
	// clear directory entry
	de->de_inum = 0;
	--ino->i_refcount;
	bcache_ipc(de, BCREQ_FLUSH);
	bcache_ipc(ino, BCREQ_FLUSH);
	r = 0;
 closeino:
	inode_close(ino);
 closedirino:
	inode_close(dirino);
 done:
	return r;
}


// Synchronizes the disk with buffer cache.
//
int
sync(void)
{
	// Our current implementation is synchronous.
	return 0;
}


// Checks file system structures.
// Checks all file system invariants hold and prints out any errors it finds.
// Does no locking, so if run in parallel with other environments, it can
// get confused and report transient "errors."
// Returns 0 if the file system is OK, -E_INVAL if any errors were found.
//
int
fsck(void)
{
	blocknum_t min_nblocks;
	int i, j, k;
	int errors = 0;

	add_pgfault_handler(bcache_pgfault_handler);

	// superblock checks
	if (super->s_magic != FS_MAGIC)
		panic("fsck: file system magic number %08x should be %08x", super->s_magic, FS_MAGIC);
	if (super->s_nblocks < 4)
		panic("fsck: file system must have at least 4 blocks");
	if (super->s_ninodes < 1)
		panic("fsck: file system must have at least 1 inode");
	min_nblocks = 2 /* boot sector, superblock */
		+ ROUNDUP(super->s_nblocks, BLKSIZE) / BLKSIZE /* freemap */
		+ (super->s_ninodes - 1); /* inodes */
	if (super->s_nblocks < min_nblocks)
		panic("fsck: file system with %d inodes has %d blocks, needs at least %d", super->s_ninodes, super->s_nblocks, min_nblocks);

	// basic freemap checks: initial blocks not free, free blocks marked
	// with 1 (later checks will overwrite freemap)
	for (i = 0; i < super->s_nblocks; ++i)
		if (i < min_nblocks && freemap[i] != 0) {
			cprintf("fsck: freemap[%d]: should be 0 (allocated), is %d\n", i, freemap[i]);
			++errors;
		} else if (freemap[i] != 0 && freemap[i] != 1) {
			cprintf("fsck: freemap[%d]: should be 0 or 1, is %d\n", i, freemap[i]);
			++errors;
			freemap[i] = (freemap[i] > 0 ? 1 : 0);
		}

	// inode checks: inode 1 is referenced, unreferenced inodes
	// have no data pointers, ftype makes sense, no data pointer overlap
	for (i = 1; i < super->s_ninodes; ++i) {
		struct Inode *ino = get_inode(i);
		off_t true_size;
		// check for open-but-unreferenced inode; be careful of
		// uninitialized inodes (use bcache_ipc to check)
		bool active = ino->i_refcount != 0;
		if (!active && ino->i_opencount != 0
		    && bcache_ipc(ino, BCREQ_MAP) != 0)
			active = true;
		if (active && ino->i_ftype != FTYPE_REG && ino->i_ftype != FTYPE_DIR) {
			cprintf("fsck: inode[%d]: odd i_ftype %d\n", i, ino->i_ftype);
			++errors;
		}
		if (i == 1 && ino->i_refcount == 0) {
			cprintf("fsck: inode[1]: root inode should be referenced\n");
			++errors;
		} else if (i == 1 && ino->i_ftype != FTYPE_DIR) {
			cprintf("fsck: inode[1]: root inode should be directory\n");
			++errors;
		}
		if (active && ino->i_size > MAXFILESIZE) {
			cprintf("fsck: inode[%d]: size %d too large\n", i, ino->i_size);
			++errors;
		}
		if (active && ino->i_inum != i) {
			cprintf("fsck: inode[%d]: wrong inumber %d\n", i, ino->i_inum);
			++errors;
		}
		true_size = active ? ino->i_size : 0;
		for (j = 0; j < NDIRECT; ++j) {
			blocknum_t b = ino->i_direct[j];
			if (j * BLKSIZE < true_size && !b) {
				cprintf("fsck: inode[%d]: direct block %d is null, though file size is %d\n", i, j, true_size);
				++errors;
			} else if (j * BLKSIZE >= true_size && b && active) {
				cprintf("fsck: inode[%d]: direct block %d exists, though file size is %d\n", i, j, true_size);
				++errors;
			}
			if (b && active) {
				if (b < min_nblocks) {
					cprintf("fsck: inode[%d]: direct block %d == %d is in special block range\n", i, j, b);
					++errors;
				} else if (freemap[b] == 1) {
					cprintf("fsck: inode[%d]: direct block %d == %d is marked as free\n", i, j, b);
					++errors;
				} else if (freemap[b] == -1) {
					cprintf("fsck: inode[%d]: direct block %d == %d used more than once\n", i, j, b);
					++errors;
				} else
					freemap[b] = -1;
			}
		}
		ino->i_fsck_refcount = (i == 1 ? 1 : 0);
		ino->i_fsck_checked = 0;
	}

	// directory checks
	while (1) {
		struct Inode *ino;
		for (i = 1; i < super->s_ninodes; ++i) {
			ino = get_inode(i);
			if (ino->i_fsck_refcount > 0
			    && !ino->i_fsck_checked
			    && ino->i_ftype == FTYPE_DIR)
				goto check_directory_inode;
		}
		break;

	check_directory_inode:
		ino->i_fsck_checked = 1;
		if (ino->i_size % sizeof(struct Direntry) != 0) {
			cprintf("inode[%d]: directory size %d not multiple of %d\n", i, ino->i_size, sizeof(struct Direntry));
			++errors;
		}
		for (j = 0; (off_t) (j + sizeof(struct Direntry)) <= ino->i_size; j += sizeof(struct Direntry)) {
			struct Direntry *de = (struct Direntry *) inode_data(ino, j);
			char name[MAXNAMELEN];
			int namelen;

			if (de->de_inum == 0)
				continue;

			if (de->de_namelen <= 0 || de->de_namelen >= MAXNAMELEN) {
				cprintf("inode[%d] de@%d: bad filename length %d\n", i, j, de->de_namelen);
				++errors;
			} else if (de->de_name[de->de_namelen] != 0) {
				cprintf("inode[%d] de@%d: filename is not null terminated\n", i, j);
				++errors;
			}
			memcpy(name, de->de_name, MAXNAMELEN);
			namelen = MAX(MIN(de->de_namelen, MAXNAMELEN - 1), 0);
			name[namelen] = 0;

			if (de->de_inum >= super->s_ninodes) {
				cprintf("inode[%d] de@%d (%s): inode %d out of range\n", i, j, name, de->de_inum);
				++errors;
			} else {
				struct Inode *refed = get_inode(de->de_inum);
				++refed->i_fsck_refcount;
				if (refed->i_refcount == 0) {
					cprintf("inode[%d] de@%d (%s): refers to free inode %d\n", i, j, name, de->de_inum);
					++errors;
				}
			}
			for (k = 0; k < j && de->de_namelen < MAXNAMELEN; k += sizeof(struct Direntry)) {
				struct Direntry *xde = (struct Direntry *) inode_data(ino, k);
				if (xde->de_inum != 0
				    && xde->de_namelen == namelen
				    && memcmp(xde->de_name, name, namelen) == 0) {
					cprintf("inode[%d] de@%d (%s): same filename as de@%d\n", i, j, name, k);
					++errors;
				}
			}
		}
	}

	// refcount consistency
	for (i = 1; i < super->s_ninodes; ++i) {
		struct Inode *ino = get_inode(i);
		if (ino->i_refcount != ino->i_fsck_refcount) {
			cprintf("fsck: inode[%d]: refcount %d should be %d\n", i, ino->i_refcount, ino->i_fsck_refcount);
			++errors;
		}
	}

	// clean up freemap
	for (i = 0; i < super->s_nblocks; ++i)
		if (freemap[i] == -1)
			freemap[i] = 0;
		else if (freemap[i] == 0 && i >= min_nblocks) {
			cprintf("fsck: freemap[%d]: unreferenced block is not free\n", i);
			++errors;
		}

	return errors ? -E_INVAL : 0;
}
