// implement fork from user space

#include <inc/string.h>
#include <inc/lib.h>

// PTE_COW marks copy-on-write page table entries.
// It is one of the bits explicitly allocated to user processes (PTE_AVAIL).
#define PTE_COW		0x800

static bool
is_mapped(uintptr_t va, pte_t *pte_store)
{
	if ((vpd[PDX(va)] & PTE_P) && (vpt[PGNUM(va)] & PTE_P)) {
		if (pte_store) *pte_store = vpt[PGNUM(va)];
		return true;
	} else {
		return false;
	}
}

//
// Custom page fault handler - if faulting page is copy-on-write,
// map in our own private writable copy and call resume(utf).
//
static void
pgfault(struct UTrapframe *utf)
{
	void *addr = (void *) utf->utf_fault_va;
	uint32_t err = utf->utf_err;
	int r;
	void *faultpage = (void *)ROUNDDOWN((uintptr_t)addr,PGSIZE);
	pte_t pte;

	// Check that the faulting access was (1) a write, and (2) to a
	// copy-on-write page.  If not, return 0.
	// Hint: Use vpd and vpt.
	//	cprintf(">> in page fault handler!\n");

	// Check fault was a write
	if (!(err & 2)) return;
	//	cprintf(">> was a write!\n");

	// Check that the page was COW
	if ((r = is_mapped((uintptr_t)faultpage, &pte)) < 0) return;
	if (!(pte & PTE_COW)) return;
	//	cprintf(">> was COW\n");

	// Allocate a new page, map it at a temporary location (PFTEMP),
	// copy the data from the old page to the new page, then move the new
	// page to the old page's address.
	// Hint:
	//   You should make three system calls.
	//   No need to explicitly delete the old page's mapping.

	// LAB 4: Your code here.
	if ((r = sys_page_alloc(0, PFTEMP, PTE_U | PTE_W)) < 0) panic("Couldn't allocate PFTEMP");
	memcpy(PFTEMP,faultpage,PGSIZE);
	if ((r = sys_page_map(0, PFTEMP, 0, faultpage, PTE_U | PTE_W)) < 0) panic("Couldn't remap faulted page");
	if ((r = sys_page_unmap(0, PFTEMP)) < 0) panic("Couldn't unmap PFTEMP");

	resume(utf);
}

//
// Map our virtual page pn (address pn*PGSIZE) into the target envid
// at the same virtual address.  If the page is writable or copy-on-write,
// the new mapping must be created copy-on-write, and then our mapping must be
// marked copy-on-write as well.  (Exercise: Why do we need to mark ours
// copy-on-write again if it was already copy-on-write at the beginning of
// this function?)
//
// Returns: 0 on success, < 0 on error.
// It is also OK to panic on error.
//
static int
duppage(envid_t envid, uintptr_t va)
{
	int r;
	pte_t pte;
	pte_t perms;
	
	if (is_mapped(va, &pte)) {
		perms = pte & PTE_SYSCALL;
		// pa is the physical address corresponding to va
		if (pte & PTE_SHARE) {
			if ((r = sys_page_map(0, (void *)va, envid, (void *)va, perms)) < 0) return r;
		} else if ((pte & PTE_W) || (pte & PTE_COW)) {
			//	cprintf("[%08x] Duplicating W or COW page %p\n", thisenv->env_id, va);
			perms = (perms & ~PTE_W) | PTE_COW;
			if ((r = sys_page_map(0, (void *)va, envid, (void *)va, perms)) < 0) return r;
			// Change perms to COW
			if ((r = sys_page_map(0, (void *)va, 0, UTEMP, perms)) < 0) return r;
			if ((r = sys_page_map(0, UTEMP, 0, (void *)va, perms)) < 0) return r;
			if ((r = sys_page_unmap(0, UTEMP)) < 0) return r;
		} else {
			//	cprintf("[%08x] Duplicating R page %p\n", thisenv->env_id, va);
			if ((r = sys_page_map(0, (void *)va, envid, (void *)va, perms)) < 0) return r;
		}
	}
	return 0;
}

//
// User-level fork with copy-on-write.
// Set up our page fault handler appropriately.
// Create a child.
// Copy our address space and page fault handler setup to the child.
// Then mark the child as runnable and return.
//
// Returns: child's envid to the parent, 0 to the child, < 0 on error.
// It is also OK to panic on error.
//
// Hint:
//   Use vpd, vpt, and duppage.
//   Remember to fix "thisenv" in the child process.
//   Neither user exception stack should ever be marked copy-on-write,
//   so you must allocate a new page for the child's user exception stack.
//
envid_t
fork(void)
{
	int ret;
	envid_t child;

	// LAB 4: Your code here.
	// 1. Install pgfault() as the page fault handler
	add_pgfault_handler(pgfault);
	//	cprintf("pgfault handler %p\n", pgfault);

	// 2. Allocate a child environment with sys_exofork()
	if ((child = sys_exofork()) < 0) return child;
	//	cprintf("child [%08x]\n", child);
	if (child == 0) {
		// Fix thisenv and return 0
		thisenv = &envs[ENVX(sys_getenvid())];
		return 0;
	}

	//	cprintf("Set up COW pages\n");

	// 3. Set up COW pages
	for (uintptr_t page = 0; page < UTOP; page += PGSIZE) {
		if (page == UXSTACKTOP-PGSIZE) continue;
		if (is_mapped(page,NULL)) {
			if ((ret = duppage(child,page)) < 0) {
				sys_env_destroy(child);
				return ret;
			}
		}
	}

	//	cprintf("Allocated exception stack at %p\n", UXSTACKTOP-PGSIZE);

	// 4. Allocate exception stack
	if ((ret = sys_page_alloc(child, (void *)(UXSTACKTOP-PGSIZE), PTE_U | PTE_W)) < 0) {
		sys_env_destroy(child);
		return ret;
	}

	//	cprintf("Set up the page fault handler\n");

	// 5. Set up the page fault handler in the child
	if ((ret = sys_env_set_pgfault_upcall(child, (void *)thisenv->env_pgfault_upcall)) < 0) {
		sys_env_destroy(child);
		return ret;
	}

	//	cprintf("Make the child runnable\n");

	// 6. Mark the child runnable
	if ((ret = sys_env_set_status(child, ENV_RUNNABLE)) < 0) {
		sys_env_destroy(child);
		return ret;
	}

	return child;
}

// Challenge!
int
sfork(void)
{
	panic("sfork not implemented");
	return -E_INVAL;
}
