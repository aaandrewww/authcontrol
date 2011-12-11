/* See COPYRIGHT for copyright information. */

#include <inc/x86.h>
#include <inc/mmu.h>
#include <inc/error.h>
#include <inc/string.h>
#include <inc/assert.h>
#include <inc/elf.h>

#include <kern/env.h>
#include <kern/pmap.h>
#include <kern/trap.h>
#include <kern/monitor.h>
#include <kern/sched.h>

#include <inc/mm.h>

struct Env *envs = NULL;		// All environments
struct Env *curenv = NULL;		// The current env
struct Env *env_free_list = NULL;	// Free list

#define ENVGENSHIFT	12		// >= LOGNENV

static uint8_t authBuffer[4*PGSIZE];

bool
check_env_auth(struct Env *goalEnv, struct Env *proverEnv) {
	if (proverEnv->proof == NULL) return false;

	Heap authHeap;
	init_heap(&authHeap, &authBuffer, 4*PGSIZE);
	Heap *oldHeap = set_heap(&authHeap);

	lcr3(PADDR(goalEnv->env_pgdir));
	Formula goal = formula_says(principal_pcpl(goalEnv->env_id), formula_subst(goalEnv->goal, 0, proverEnv->env_id));
	lcr3(PADDR(proverEnv->env_pgdir));
	Proof proof = proof_cp(proverEnv->proof);
	
	bool result = proof_check(goal, proof, NULL);

	freeall();
	set_heap(oldHeap);

	return result;
}

//
// Converts an envid to an env pointer.
// If checkperm is set, the specified environment must be either the
// current environment or an immediate child of the current environment.
//
// RETURNS
//   0 on success, -E_BAD_ENV on error.
//   On success, sets *env_store to the environment.
//   On error, sets *env_store to NULL.
//
int
envid2env(envid_t envid, struct Env **env_store, bool checkperm)
{
	struct Env *e;

	// If envid is zero, return the current environment.
	if (envid == 0) {
		*env_store = curenv;
		return 0;
	}

	// Look up the Env structure via the index part of the envid,
	// then check the env_id field in that struct Env
	// to ensure that the envid is not stale
	// (i.e., does not refer to a _previous_ environment
	// that used the same slot in the envs[] array).
	e = &envs[ENVX(envid)];
	if (e->env_status == ENV_FREE || e->env_id != envid) {
		*env_store = 0;
		return -E_BAD_ENV;
	}

	// If checkperm is set, check that the calling environment 
	// has legitimate permission to manipulate the specified environment.
	if (checkperm) {
		if (e->goal == NULL) { // No authorization goal set, 
			               // use old parent-child relationship
			               // (the specified environment must be 
			               // either the current environment or an
	                               // immediate child of the current environment.
			if (e != curenv && e->env_parent_id != curenv->env_id) {
				*env_store = 0;
				return -E_BAD_ENV;
			}
		} else { // The environment set an authorization goal
			if (check_env_auth(e, curenv) != true) {
				*env_store = 0;
				return -E_BAD_ENV;
			}
		}
	}

	*env_store = e;
	return 0;
}

//
// Mark all environments in 'envs' as free, set their env_ids to 0,
// and insert them into the env_free_list.
// Insert in reverse order, so that the first call to env_alloc()
// returns envs[0].  (This is important for grading.)
//
void
env_init(void)
{
	// Set up envs array
	// LAB 3: Your code here.
	for (uint32_t i = NENV-1; i + 1 > 0; i--) {
		//cprintf("Setting up env %d at %x\n", i, &envs[i]);
		Env *env = &envs[i];
		env->env_id = 0;
		env->env_link = env_free_list;
		env_free_list = env;
	}
}

//
// Initialize the kernel virtual memory layout for environment e.
// Allocate a page directory, set e->env_pgdir accordingly,
// and initialize the kernel portion of the new environment's address space.
// Do NOT (yet) map anything into the user portion
// of the environment's virtual address space.
//
// Returns 0 on success, < 0 on error.  Errors include:
//	-E_NO_MEM if page directory or table could not be allocated.
//
static int
env_mem_init(struct Env *e)
{
	pte_t i;
	int r;
	struct Page *p;

	// Allocate a page for the page directory
	p = page_alloc();
	if (!p)
		return -E_NO_MEM;

	// Now, set e->env_pgdir and initialize the page directory.
	//
	// Hint:
	//    - Remember that page_alloc doesn't zero the page.
	//    - The VA space of all envs is identical above UTOP
	//	(except at UVPT, which we've set below).
	//	See inc/memlayout.h for permissions and layout.
	//	Can you use kern_pgdir as a template?  Hint: Yes.
	//	(Make sure you got the permissions right in Lab 2.)
	//    - The initial VA below UTOP is empty.
	//    - You do not need to make any more calls to page_alloc.
	//    - Note: In general, pp_ref is not maintained for
	//	physical pages mapped only above UTOP, but env_pgdir
	//	is an exception -- you need to increment env_pgdir's
	//	pp_ref for env_free to work correctly.
	//    - The functions in kern/pmap.h are handy.

	e->env_pgdir = (pde_t *) page2kva(p);
	//cprintf("CREATING NEW ENV_PGDIR AT 0x%08x\n", e->env_pgdir);
	p->pp_ref++;
	memcpy(e->env_pgdir, kern_pgdir, PGSIZE);

	// UVPT maps the env's own page table read-only.
	// Permissions: kernel R, user R
	e->env_pgdir[PDX(UVPT)] = PADDR(e->env_pgdir) | PTE_P | PTE_U;

	return 0;
}

//
// Allocates and initializes a new environment.
// On success, the new environment is stored in *newenv_store.
//
// Returns 0 on success, < 0 on failure.  Errors include:
//	-E_NO_FREE_ENV if all NENVS environments are allocated
//	-E_NO_MEM on memory exhaustion
//
int
env_alloc(struct Env **newenv_store, envid_t parent_id)
{
	int32_t generation;
	int r;
	struct Env *e = env_free_list;
	if (!e)
		return -E_NO_FREE_ENV;

	// Allocate and set up the page directory for this environment.
	if ((r = env_mem_init(e)) < 0)
		return r;

	// Generate an env_id for this environment.
	generation = (e->env_id + (1 << ENVGENSHIFT)) & ~(NENV - 1);
	if (generation <= 0)	// Don't create a negative env_id.
		generation = 1 << ENVGENSHIFT;
	e->env_id = generation | (e - envs);

	// Set the basic status variables.
	e->env_parent_id = parent_id;
	e->env_status = ENV_RUNNABLE;
	e->env_runs = 0;

	// Clear out all the saved register state,
	// to prevent the register values
	// of a prior environment inhabiting this Env structure
	// from "leaking" into our new environment.
	memset(&e->env_tf, 0, sizeof(e->env_tf));

	// Set up appropriate initial values for the segment registers.
	// GD_UD is the user data segment selector in the GDT, and
	// GD_UT is the user text segment selector (see inc/memlayout.h).
	// The low 2 bits of each segment register contains the
	// Requestor Privilege Level (RPL); 3 means user mode.
	e->env_tf.tf_ds = GD_UD | 3;
	e->env_tf.tf_es = GD_UD | 3;
	e->env_tf.tf_ss = GD_UD | 3;
	e->env_tf.tf_esp = USTACKTOP;
	e->env_tf.tf_cs = GD_UT | 3;
	// You will set e->env_tf.tf_eip later.

	// Give the env a ticket
	e->tickets = 1;

	// Enable interrupts while in user mode.
	// LAB 4: Your code here.
	e->env_tf.tf_eflags = e->env_tf.tf_eflags | FL_IF;

	// Clear the page fault handler until user installs one.
	e->env_pgfault_upcall = 0;

	// Also clear the IPC receiving flag.
	e->env_ipc_recving = 0;

	// If this is the buffer cache server (env_id == ENVID_BUFCACHE)
	// give it I/O privileges.
	// LAB 5: Your code here.
	e->env_tf.tf_eflags = e->env_tf.tf_eflags & (~FL_IOPL_MASK);
	if (e->env_id == ENVID_BUFCACHE) {
		e->env_tf.tf_eflags = e->env_tf.tf_eflags | FL_IOPL_3;
	}

	e->proof = NULL;
	e->goal = NULL;

	// commit the allocation
	env_free_list = e->env_link;
	*newenv_store = e;

	cprintf("[%08x] new env %08x\n", curenv ? curenv->env_id : 0, e->env_id);
	return 0;
}

//
// Allocate at least len bytes of physical memory for environment env,
// and map it at virtual address va in the environment's address space.
// Does not zero or otherwise initialize the mapped pages in any way.
// Pages should be writable by user and kernel.
// Panic if any allocation attempt fails.
//
static void
segment_alloc(struct Env *e, uintptr_t va, size_t len)
{
	// LAB 3: Your code here.
	// (But only if you need it for load_elf.)
	//
	// Hint: It is easier to use segment_alloc if the caller can pass
	//   'va' and 'len' values that are not page-aligned.
	//   You should round 'va' down, and round 'va + len' up.
}

static void
load_proghdr(pde_t *pgdir, uint8_t *binary, uintptr_t va,  
	     size_t filesz, size_t memsz, size_t offset);

//
// Set up the initial program binary, stack, and processor flags
// for a user process.
//
// This function loads all loadable segments from the ELF binary image
// into the environment's user memory, starting at the appropriate
// virtual addresses indicated in the ELF program header.
// It also clears to zero any portions of these segments
// that are marked in the program header as being mapped
// but not actually present in the ELF file -- i.e., the program's bss section.
//
// Finally, this function maps one page for the program's initial stack.
//
// load_elf panics if it encounters problems.
//  - How might load_elf fail?  What might be wrong with the given input?
//
static void
load_elf(struct Env *e, uint8_t *binary, size_t size)
{
	struct Elf *elf = (struct Elf *) binary;
	// Load each program segment into environment 'e's virtual memory
	// at the address specified in the ELF section header.
	// Only load segments with ph->p_type == ELF_PROG_LOAD.
	// Each segment's virtual address can be found in ph->p_va
	// and its size in memory can be found in ph->p_memsz.
	// The ph->p_filesz bytes from the ELF binary, starting at
	// 'binary + ph->p_offset', should be copied to virtual address
	// ph->p_va.  Any remaining memory bytes should be cleared to zero.
	// (The ELF header should have ph->p_filesz <= ph->p_memsz.)
	// Use functions from the previous lab to allocate and map pages.
	//
	// All page protection bits should be user read/write for now.
	// ELF segments are not necessarily page-aligned, but you can
	// assume for this function that no two segments will touch
	// the same virtual page.
	//
	// You may find a function like segment_alloc useful.
	//
	// Loading the segments is much simpler if you can move data
	// directly into the virtual addresses stored in the ELF binary.
	// So which page directory should be in force during
	// this function?
	//
	// All this is very similar to what our boot loader does, except the
	// boot loader reads the code from disk and doesn't check whether
	// segments are loadable.  Take a look at boot/main.c to get ideas.
	//
	// You must also store the program's entry point somewhere,
	// to make sure that the environment starts executing at that point.
	// See env_run() and env_iret() below.

	// LAB 3: Your code here.
	lcr3(PADDR(e->env_pgdir));
	
	// Is this a valid ELF?
	// XXX Probably should do something better than panic!
	if (elf->e_magic != ELF_MAGIC) panic("Trying to load invalid elf!");

	// Save the entry address
	e->env_tf.tf_eip = (uintptr_t) elf->e_entry;

	// load each segment
	Proghdr *ph = (struct Proghdr *) ((uint8_t *) elf + elf->e_phoff);
	Proghdr *eph = ph + elf->e_phnum;
	for (; ph < eph; ph++) {
		if (ph->p_type == ELF_PROG_LOAD) {
			load_proghdr(e->env_pgdir, binary, ph->p_va, 
				     ph->p_filesz, ph->p_memsz, ph->p_offset);
		}
	}

	// Now map one page for the program's initial stack
	// at virtual address USTACKTOP - PGSIZE.
	// (What should the permissions be?)

	// LAB 3: Your code here.
	Page *stackPage = page_alloc();
	if (page_insert(e->env_pgdir, stackPage, USTACKTOP-PGSIZE, PTE_U | PTE_W) < 0)
		panic("Stack allocation failed");
	memset((void *)(USTACKTOP-PGSIZE), 0, PGSIZE);

	//cprintf("Env page table\n");
	//print_page_table(e->env_pgdir, false, false);

	lcr3(PADDR(kern_pgdir));
}

static void
load_proghdr(pde_t *pgdir, uint8_t *binary, uintptr_t va, 
	     size_t filesz, size_t memsz, size_t offset) {
	//cprintf("Loading 0x%08x - 0x%08x\n", va, va + memsz); 
	assert(filesz <= memsz);
	uintptr_t end_va = va + memsz;
	assert(end_va <= UTOP);
	
	// Map and initialize the pages
	for (uintptr_t curva = ROUNDDOWN(va, PGSIZE); curva < ROUNDUP(end_va, PGSIZE); curva += PGSIZE) {
		Page *pp = page_alloc();
		int res = page_insert(pgdir, pp, curva, PTE_U | PTE_W);
		if (res < 0) panic ("Panic inserting ELF pages");
		memset((void *)curva, 0, PGSIZE);
	}

	// Copy the data
	memcpy((void *)va, binary+offset, filesz);
}

//
// Creates a new env running a specific binary.
// The new env's parent ID is set to 0.
// The implementation is a simple wrapper around env_alloc and load_elf.
//
void
env_create(uint8_t *binary, size_t size)
{
	// LAB 3: Your code here.
	Env *allocdEnv;
	int res = env_alloc(&allocdEnv, 0);
	if (res < 0) {
		cprintf("Failed to create env: %e\n", res);
		panic("");
	}
	load_elf(allocdEnv, binary, size);
}

//
// Frees env e and all memory it uses.
//
void
env_free(struct Env *e)
{
	pde_t *pgdir;
	pte_t *pt;
	uint32_t pdeno, pteno;
	physaddr_t pa;

	// If freeing the current environment, switch to kern_pgdir
	// before freeing the page directory, just in case the page
	// gets reused.
	if (e == curenv)
		lcr3(PADDR(kern_pgdir));

	// Note the environment's demise.
	cprintf("[%08x] free env %08x\n", curenv ? curenv->env_id : 0, e->env_id);

	// Flush all mapped pages in the user portion of the address space
	static_assert(UTOP % PTSIZE == 0);
	pgdir = e->env_pgdir;
	for (pdeno = 0; pdeno < PDX(UTOP); pdeno++) {
		// only look at mapped page tables
		if (!(pgdir[pdeno] & PTE_P))
			continue;

		// find the pa and va of the page table
		pt = (pte_t *) KADDR(PTE_ADDR(pgdir[pdeno]));

		// unmap all PTEs in this page table
		for (pteno = 0; pteno <= PTX(~0); pteno++) {
			if (pt[pteno] & PTE_P)
				page_remove(pgdir, PGADDR(pdeno, pteno, 0));
		}

		// free the page table itself
		pgdir[pdeno] = 0;
		page_decref(kva2page(pt));
	}

	// free the page directory
	e->env_pgdir = 0;
	page_decref(kva2page(pgdir));

	// return the environment to the free list
	e->env_status = ENV_FREE;
	e->env_link = env_free_list;
	env_free_list = e;
}

//
// Frees environment e.
// If e was the current env, then runs a new environment (and does not return
// to the caller).
//
void
env_destroy(struct Env *e)
{
	env_free(e);

	if (curenv == e) {
		curenv = NULL;
		sched_yield();
	}
}


//
// Restores the register values in the Trapframe with the 'iret' instruction.
// This exits the kernel and starts executing some environment's code
// at the location and registers specified in the Trapframe.
//
// This function does not return.
//
void
env_iret(struct Trapframe *tf)
{
	__asm __volatile("movl %0,%%esp\n"
		"\tpopal\n"
		"\tpopl %%es\n"
		"\tpopl %%ds\n"
		"\taddl $0x8,%%esp\n" /* skip tf_trapno and tf_errcode */
		"\tiret"
		: : "g" (tf) : "memory");
	panic("iret failed");  /* mostly to placate the compiler */
}

//
// Context switch from curenv to env e.
// Note: if this is the first call to env_run, curenv is NULL.
//
// This function does not return.
//
void
env_run(struct Env *e)
{
	// Step 1: If this is a context switch (a new environment is running),
	//	   then set 'curenv' to the new environment,
	//	   update its 'env_runs' counter, and
	//	   and use lcr3() to switch to its address space.
	// Step 2: Use env_iret() to restore the environment's
	//	   registers and drop into user mode in the
	//	   environment.

	// Hint: This function loads the new environment's state from
	//	e->env_tf.  Go back through the code you wrote above
	//	and make sure you have set the relevant parts of
	//	e->env_tf to sensible values.

	// LAB 3: Your code here.
	//	cprintf("Running ENV %08x\n", e->env_id);
	if (curenv != e) {
		e->env_runs++;
		curenv = e;
		lcr3(PADDR(e->env_pgdir));
	}
	//pte_t entry = *(pgdir_walk(e->env_pgdir,e->env_tf.tf_eip,false));
	//cprintf("EIP: 0x%08x\tEntry: 0x%08x\tP: %d\n", e->env_tf.tf_eip, PTE_ADDR(entry), entry & PTE_P);

	env_iret(&e->env_tf);
}

