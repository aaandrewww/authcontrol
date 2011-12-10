// User-level page fault handler support.

#include <inc/lib.h>

// Our page fault handler, which tries all user-installed page fault handlers.
asmlinkage void _pgfault_upcall(struct UTrapframe utf);

// User-installed page fault handler pointers.
#define NUSER_HANDLERS 8
static pgfault_handler_t user_handlers[NUSER_HANDLERS];

// Add a page fault handler function.
//
// The first time we register a handler, we need to
// allocate an exception stack (one page of memory with its top
// at UXSTACKTOP), and tell the kernel to call the
// _pgfault_upcall routine when a page fault occurs.
//
void
add_pgfault_handler(pgfault_handler_t handler)
{
	int r;

	if (!thisenv->env_pgfault_upcall) {
		// LAB 4: Your code here.
		if (!user_handlers[0]) {
			// First handler! Need to allocate the exception stack
			r = sys_page_alloc(thisenv->env_id, (void *)(UXSTACKTOP-PGSIZE), PTE_U | PTE_W);
			if (r < 0) {
				cprintf("Failed to allocate exception stack page: %e\n", r);
				panic("Adding pagefault handler failed!");
			}
			// Also need to register our handler
			r = sys_env_set_pgfault_upcall(thisenv->env_id, (void *)_pgfault_upcall);
			if (r < 0) {
				cprintf("Failed to set pgfault upcall: %e\n", r);
				panic("Adding pagefault handler failed!");
			}
		}
	}

	// Store handler pointer in our list of handlers.
	for (int i = 0; i < NUSER_HANDLERS; ++i)
		if (user_handlers[i] == handler || !user_handlers[i]) {
			user_handlers[i] = handler;
			return;
		}

	panic("[%08x] too many page fault handlers\n", sys_getenvid());
}

// The page fault handler function calls each user page fault handler in order.
// One of the page fault handlers should handle fault and call resume().
//
asmlinkage void
_pgfault_upcall(struct UTrapframe utf)
{
	int i;
	for (i = NUSER_HANDLERS - 1; i >= 0; --i)
		if (user_handlers[i])
			user_handlers[i](&utf);

	panic("[%08x] unhandled page fault at va %08x from eip %08x\n",
	      sys_getenvid(), utf.utf_fault_va, utf.utf_eip);
}
