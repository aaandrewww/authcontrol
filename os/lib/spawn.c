#include <inc/lib.h>
#include <inc/elf.h>

static int copy_shared_pages(envid_t child);

//
// Allocate at least len bytes of physical memory for environment env,
// mapped at virtual address 'va' in 'dst_env's address space.
// Pages should be writable and zeroed.
// Return 0 on success, < 0 if an allocation attempt fails.
//
static int
segment_alloc(envid_t dst_env, uintptr_t va, size_t len)
{
	// LAB 4: Your code here.
	// (But only if you need it for spawn.)
	// Refer to your Lab 3 code in kern/env.c!
	int r;

	uintptr_t endva = va + len;
	for (uintptr_t curva = ROUNDDOWN(va, PGSIZE); curva < ROUNDUP(endva, PGSIZE); curva += PGSIZE) {
		if ((r = sys_page_alloc(dst_env, (void *)curva, PTE_U | PTE_W)) < 0) {
			return r;
		}
		if ((r = sys_page_map(dst_env, (void *)curva, thisenv->env_id, (void *)UTEMP, PTE_U | PTE_W)) < 0) {
			return r;
		}
		memset((void *)UTEMP, 0, PGSIZE);
	}

	return 0;
}

static int
segment_readonly(envid_t dst_env, uintptr_t va, size_t len)
{
	int r;
	uintptr_t endva = va + len;
	for (uintptr_t curva = ROUNDDOWN(va, PGSIZE); curva < ROUNDUP(endva, PGSIZE); curva += PGSIZE) {
		if ((r = sys_page_map(dst_env, (void *)curva, 0, UTEMP, PTE_U | PTE_W)) < 0) return r;
		if ((r = sys_page_map(0, UTEMP, dst_env, (void *)curva, PTE_U)) < 0) return r;
	}
	return 0;
}

//
// Shift an address from the UTEMP page to the corresponding value in the
// normal stack page (top address USTACKTOP).
//
static uintptr_t utemp_addr_to_stack_addr(void *ptr)
{
	uintptr_t addr = (uintptr_t) ptr;
	assert(ptr >= UTEMP && ptr < (char *) UTEMP + PGSIZE);
	return USTACKTOP - PGSIZE + PGOFF(addr);
}

//
// Set up the initial stack page for the new child process with envid 'child'
// using the arguments array pointed to by 'argv',
// which is a null-terminated array of pointers to '\0'-terminated strings.
//
// On success, returns 0 and sets *init_esp to the initial stack pointer
//   with which the child should start.
// Returns < 0 on failure.
//
static int
init_stack(envid_t child, const char **argv, uintptr_t *init_esp)
{
	size_t string_size;
	int argc, i, r;
	char *string_store;
	uintptr_t *argv_store;

	// Count the number of arguments (argc)
	// and the total amount of space needed for strings (string_size).
	string_size = 0;
	for (argc = 0; argv[argc] != 0; argc++)
		string_size += strlen(argv[argc]) + 1;

	// Determine where to place the strings and the argv array.
	// We set up the 'string_store' and 'argv_store' pointers to point
	// into the temporary page at UTEMP.
	// Later, we'll remap that page into the child environment
	// at (USTACKTOP - PGSIZE).

	// strings are topmost on the stack.
	string_store = (char *) UTEMP + PGSIZE - string_size;

	// argv is below that.  There's one argument pointer per argument, plus
	// a null pointer.
	argv_store = (uintptr_t *) ROUNDDOWN(string_store, 4) - (argc + 1);

	// Make sure that argv, strings, and the 2 words that hold 'argc'
	// and 'argv' themselves will all fit in a single stack page.
	if ((void*) (argv_store - 2) < (void*) UTEMP)
		return -E_NO_MEM;

	// Allocate a page at UTEMP.
	if ((r = sys_page_alloc(0, (void*) UTEMP, PTE_P|PTE_U|PTE_W)) < 0)
		return r;

	// Store the 'argc' and 'argv' parameters themselves
	// below 'argv_store' on the stack.  These parameters will be passed
	// to umain().
	argv_store[-2] = argc;
	argv_store[-1] = utemp_addr_to_stack_addr(argv_store);

	// Copy the argument strings from 'argv' into UTEMP
	// and initialize 'argv_store[i]' to point at argument string i
	// in the child's address space.
	// Then set 'argv_store[argc]' to 0 to null-terminate the args array.
	// LAB 4: Your code here.
	char *cur_string_store = string_store;
	for (int i = 0; i < argc; i++) {
		size_t string_size = strlen(argv[i]) + 1;
		memcpy(cur_string_store, argv[i], string_size);
		argv_store[i] = utemp_addr_to_stack_addr(cur_string_store);
		cur_string_store += string_size;
	}
	argv_store[argc] = 0;


	// Set *init_esp to the initial stack pointer for the child:
	// it should point at the "argc" value stored on the stack.
	// LAB 4: Your code here.
	*init_esp = utemp_addr_to_stack_addr(&argv_store[-2]);

	// After completing the stack, map it into the child's address space
	// and unmap it from ours!
	if ((r = sys_page_map(0, UTEMP, child, (void*) (USTACKTOP - PGSIZE), PTE_P | PTE_U | PTE_W)) < 0)
		goto error;
	if ((r = sys_page_unmap(0, UTEMP)) < 0)
		goto error;

	return 0;

error:
	sys_page_unmap(0, UTEMP);
	return r;
}

ssize_t
file_program_read(envid_t envid, void *va, int fd, uint32_t offset, size_t size) {
	int r;
	Env *env;
	size_t readable;
	ssize_t remaining;
	struct Stat fstats;

	//cprintf("stat\n");
	if ((r = fstat(fd,&fstats)) < 0) return r;
	
	//cprintf("check offset\n");
	if (offset > (uint32_t)fstats.st_size) return 0;
	readable = fstats.st_size - offset;
	if (readable < size) size = readable;
	
	// Seek to the desired offset
	if ((r = seek(fd,offset)) < 0) return r;

	//cprintf("remaining: %d\n", size);
	remaining = size;

	uint8_t *curpage = (uint8_t *)ROUNDDOWN(va,PGSIZE);
	uint8_t *curpageend = curpage + PGSIZE;
	uint8_t *readptr = (uint8_t *)UTEMP + ((uint8_t *)va-curpage);
	//cprintf("va: %08x curpage: %08x curpageend: %08x readptr: %08x\n", va, curpage, curpageend, readptr);
	while (remaining > 0) {
		if ((r = sys_page_map(envid, curpage, 0, UTEMP, PTE_P | PTE_U | PTE_W)) < 0) {
			//	cprintf("map failed: %e\n", r);
			break;
		}
		//cprintf("after page map\n");
		size_t readamount = MIN(PGSIZE - (readptr-(uint8_t *)UTEMP),remaining);
		size_t readsofar = 0;
		//cprintf("readamount: %d to: %08x\n", readamount, readptr);
		while (readsofar < readamount) {
			if ((r = read(fd,(void *)readptr,readamount)) < 0) {
				sys_page_unmap(0,UTEMP);
				break;
			}
			readsofar += r;
		}
		sys_page_unmap(0,UTEMP);
		remaining -= readamount;
		curpage = curpageend;
		curpageend = curpage + PGSIZE;
		readptr = (uint8_t *)UTEMP;
	}
	//cprintf("read %d\n", size-remaining);
	return size-remaining;
}

ssize_t
program_read(envid_t envid, void *va, int programid, uint32_t offset, size_t size) {
	if (programid >= PROGRAM_OFFSET) {
		return sys_program_read(envid,va,programid,offset,size);
	} else {
		return file_program_read(envid,va,programid,offset,size);
	}
}

//
// Spawn a new user process running a specified binary.
//
// This function loads all loadable segments from an ELF binary image
// into the environment's user memory, starting at the appropriate
// virtual addresses indicated in the ELF program header.
// It also clears to zero any portions of these segments
// that are marked in the program header as being mapped
// but not actually present in the ELF file -- i.e., the program's bss section.
//
// This is a lot like load_elf in kern/env.c, and you can reuse a lot of the
// same logic!  But instead of copying directly from an ELF image, you'll
// use the sys_program_read() system call.
//
// This function also maps one page for the program's initial stack.
// Command line arguments go on the stack, so it's not just an empty page;
// see init_stack.
//
// Returns the new environment's ID on success, and < 0 on error.
// If an error occurs, any new environment is destroyed.
//
envid_t
spawn(const char *prog, const char **argv)
{
	unsigned char elf_buf[512];
	struct Elf *elf = (struct Elf *) &elf_buf;

	int progid, i, r;
	struct Proghdr *ph;
	struct Proghdr *endph;
	int ret;

	// LAB 5 EXERCISE: If the first character of prog is '/',
	// look up the program using 'open' (not sys_program_lookup)
	// and read from it using 'read' and 'seek' (not sys_program_read).
	//
	// Program IDs returned by sys_program_lookup are greater than
	// or equal to PROGRAM_OFFSET (0x40000000).
	// No file descriptors are that big, so you can use a single variable
	// to hold either the program ID or the file descriptor number.
	//
	// Unfortunately, you cannot 'read' into a child address space,
	// so you'll need to code the 'read' case differently.
	//
	// Also, make sure you close the file descriptor, if any,
	// before returning from spawn().
	if (prog[0] == '/') {
		if ((progid = open(prog, O_RDONLY)) < 0) {
			ret = progid;
			goto exit;
		}
	} else {
		// Read ELF header from the kernel's binary collection.
		if ((progid = sys_program_lookup(prog, strlen(prog))) < 0) {
			ret = progid;
			goto exit;
		}
	}
	memset(elf_buf, 0, sizeof(elf_buf)); // ensure stack is writable
	if (program_read(0, elf_buf, progid, 0, sizeof(elf_buf)) != sizeof(elf_buf)
	    || elf->e_magic != ELF_MAGIC) {
		cprintf("elf magic %08x want %08x\n", elf->e_magic, ELF_MAGIC);
		ret = -E_NOT_EXEC;
		goto exit;
	}

	// Now create the child process, then load the ELF into it!
	// Hints:
	// - Refer to your load_elf.
	// - You can assume that all "struct Proghdr" structures are contained
	//   in the first 512 bytes of the ELF, which you loaded already.
	// - The virtual addresses included in ELF files might not be
	//   page-aligned.  However, ELF guarantees that no two segments
	//   will load different data into the same page.
	//   (ELF also guarantees that PGOFF(ph->p_va) == PGOFF(ph->p_offset),
	//   although you won't use that fact here.)
	// - Check out sys_env_set_trapframe and init_stack.
	//
	// LAB 4: Your code here.
	int envid;
	if ((envid = sys_exofork()) < 0) {
		ret = envid;
		goto exit;
	}
	// Don't need to check if we're the child because the child will not resume here

	if (elf->e_magic != ELF_MAGIC) {
		sys_env_destroy(envid);
		ret = -E_NOT_EXEC;
		goto exit;
	}

	// load each segment
	ph = (struct Proghdr *) ((uint8_t *) elf + elf->e_phoff);
	endph = ph + elf->e_phnum;
	for (; ph < endph; ph++) {
		if (ph->p_type == ELF_PROG_LOAD) {
			if ((r = segment_alloc(envid, ph->p_va, ph->p_memsz)) < 0) {
				sys_env_destroy(envid);
				ret = r;
				goto exit;
			}
			r = program_read(envid, (void *)ph->p_va, progid, ph->p_offset, ph->p_filesz);
			if ((r < 0) || ((size_t) r != ph->p_filesz)) {
				sys_env_destroy(envid);
				ret = -E_NOT_EXEC;
				goto exit;
			}
			if ((ph->p_flags & ELF_PROG_FLAG_WRITE) == 0) {
				if ((r = segment_readonly(envid, ph->p_va, ph->p_memsz)) < 0) {
					sys_env_destroy(envid);
					ret = r;
					goto exit;
				}
			}
		}
	}

	struct Trapframe trapframe;
	trapframe.tf_eip = elf->e_entry;

	if ((r = init_stack(envid, argv, &trapframe.tf_esp)) < 0) {
		sys_env_destroy(envid);
		ret = r;
		goto exit;
	}

	if ((r = sys_env_set_trapframe(envid, &trapframe)) < 0) {
		sys_env_destroy(envid);
		ret = r;
		goto exit;
	}
	
	close(progid);
	if ((r = copy_shared_pages(envid)) < 0) {
		sys_env_destroy(envid);
		return r;
	}
	if ((r = sys_env_set_status(envid, ENV_RUNNABLE)) < 0) {
		sys_env_destroy(envid);
		return r;
	}
	return envid;

 exit:
	if ((progid >= 0) && (progid < PROGRAM_OFFSET))
		close(progid);
	return ret;
}

// Spawn, taking command-line arguments array directly on the stack.
envid_t
spawnl(const char *prog, const char *arg0, ...)
{
	return spawn(prog, &arg0);
}


// Copy the mappings for shared pages into the child address space.
static int
copy_shared_pages(envid_t child)
{
	uintptr_t va;
	int r;
	for (va = 0; va < UTOP; va += PGSIZE)
		if (!(vpd[PDX(va)] & PTE_P))
			va = ROUNDUP(va + 1, PTSIZE) - PGSIZE;
		else if ((vpt[PGNUM(va)] & (PTE_P|PTE_SHARE)) == (PTE_P|PTE_SHARE)) {
			r = sys_page_map(0, (void *) va, child, (void *) va,
					 vpt[PGNUM(va)] & PTE_SYSCALL);
			if (r < 0)
				return r;
		}
	return 0;
}
