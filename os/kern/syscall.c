/* See COPYRIGHT for copyright information. */

#include <inc/x86.h>
#include <inc/error.h>
#include <inc/string.h>
#include <inc/assert.h>
#include <inc/formula.h>
#include <inc/proof.h>

#include <kern/env.h>
#include <kern/pmap.h>
#include <kern/trap.h>
#include <kern/syscall.h>
#include <kern/console.h>
#include <kern/sched.h>
#include <kern/programs.h>

// Print a string to the system console.
// The string is exactly 'len' characters long.
// Destroys the environment on memory errors.
static void
sys_cputs(uintptr_t s_ptr, size_t len)
{
	// Check that the user has permission to read memory [s, s+len).
	// Destroy the environment if not.

	// LAB 3 (Exercise 7): Your code here.
	user_mem_assert(curenv, s_ptr, len, PTE_U);

	// Print the string supplied by the user.
	cprintf("%.*s", len, (char *) s_ptr);
}

// Read a character from the system console without blocking.
// Returns the character, or 0 if there is no input waiting.
static int
sys_cgetc(void)
{
	return cons_getc();
}

// Returns the current environment's envid.
static envid_t
sys_getenvid(void)
{
	return curenv->env_id;
}

// Destroy a given environment (possibly the currently running environment).
//
// Returns 0 on success, < 0 on error.  Errors are:
//	-E_BAD_ENV if environment envid doesn't currently exist,
//		or the caller doesn't have permission to change envid.
static int
sys_env_destroy(envid_t envid)
{
	int r;
	struct Env *e;

	if ((r = envid2env(envid, &e, 1)) < 0)
		return r;
	if (e == curenv)
		cprintf("[%08x] exiting gracefully\n", curenv->env_id);
	else
		cprintf("[%08x] destroying %08x\n", curenv->env_id, e->env_id);
	env_destroy(e);
	return 0;
}

// Deschedule current environment and pick a different one to run.
static void
sys_yield(void)
{
	sched_yield();
}

// Allocate a new environment.
// Returns envid of new environment, or < 0 on error.  Errors are:
//	-E_NO_FREE_ENV if no free environment is available.
//	-E_NO_MEM on memory exhaustion.
static envid_t
sys_exofork(void)
{
	// Create the new environment with env_alloc(), from kern/env.c.
	// It should be left as env_alloc created it, except that
	// status is set to ENV_NOT_RUNNABLE, and the register set is copied
	// from the current environment.
	// Make sure that, when the new environment is run,
	// sys_exofork will appear to return 0 there.

	// LAB 3: Your code here.
	Env *newEnv;
	int ret = env_alloc(&newEnv, curenv->env_id);
	if (ret < 0) return ret;

	newEnv->env_status = ENV_NOT_RUNNABLE;
	memcpy(&newEnv->env_tf,&curenv->env_tf,sizeof(struct Trapframe));
	newEnv->env_tf.tf_regs.reg_eax = 0;
	return newEnv->env_id;
}

// Set envid's env_status to status, which must be ENV_RUNNABLE
// or ENV_NOT_RUNNABLE.
//
// Returns 0 on success, < 0 on error.  Errors are:
//	-E_BAD_ENV if environment envid doesn't currently exist,
//		or the caller doesn't have permission to change envid.
//	-E_INVAL if status is not a valid status for an environment.
static int
sys_env_set_status(envid_t envid, int status)
{
	// Hint: Use the 'envid2env' function from kern/env.c to translate an
	// envid to a struct Env.
	// You should set envid2env's third argument to 1, which will
	// check whether the current environment has permission to set
	// envid's status.

	// LAB 3: Your code here.
	Env *env;
	int ret = envid2env(envid, &env, true);
	if (ret < 0) return ret;

	switch (status) {
	case ENV_RUNNABLE:
	case ENV_NOT_RUNNABLE:
		env->env_status = status;
		return 0;
	default:
		return -E_INVAL;
	}
}

// Set the page fault upcall for 'envid' by modifying the corresponding struct
// Env's 'env_pgfault_upcall' field.  When 'envid' causes a page fault, the
// kernel will push a fault record onto the exception stack, then branch to
// 'func'.
//
// Returns 0 on success, < 0 on error.  Errors are:
//	-E_BAD_ENV if environment envid doesn't currently exist,
//		or the caller doesn't have permission to change envid.
static int
sys_env_set_pgfault_upcall(envid_t envid, uintptr_t func)
{
	// LAB 4: Your code here.
	int r;
	Env *env;
	if ((r = envid2env(envid, &env, true)) < 0) return r;
	// XXX Shouldn't we check this is a safe pointer to jump to?
	env->env_pgfault_upcall = func;
	return 0;
}

// Set envid's trap frame to the Trapframe stored in '*tf_ptr',
// modified to make sure that user environments always run with correct
// segment registers and with interrupts enabled.
//
// Returns 0 on success, < 0 on error.  Errors are:
//	-E_BAD_ENV if environment envid doesn't currently exist,
//		or the caller doesn't have permission to change envid.
//	Destroy the environment on memory errors.
static int
sys_env_set_trapframe(envid_t envid, uintptr_t tf_ptr)
{
	// LAB 4: Your code here.
	int r;
	Env *env;
	if ((r = envid2env(envid, &env, true)) < 0) return r;
	user_mem_assert(curenv, tf_ptr, sizeof(struct Trapframe), PTE_U);
	memcpy(&env->env_tf, (void *)tf_ptr, sizeof(struct Trapframe));
	env->env_tf.tf_ds = GD_UD | 3;
	env->env_tf.tf_es = GD_UD | 3;
	env->env_tf.tf_ss = GD_UD | 3;
	env->env_tf.tf_cs = GD_UT | 3;
	env->env_tf.tf_eflags = env->env_tf.tf_eflags | FL_IF;
	return 0;
}

// Allocate a page of memory and map it at 'va' with permission
// 'perm' in the address space of 'envid'.
// The page's contents are set to 0.
// If a page is already mapped at 'va', that page is unmapped as a
// side effect.
//
// perm -- PTE_U | PTE_P must be set, PTE_AVAIL | PTE_W may or may not be set,
//         but no other bits may be set.  See PTE_SYSCALL in inc/mmu.h.
//
// Return 0 on success, < 0 on error.  Errors are:
//	-E_BAD_ENV if environment envid doesn't currently exist,
//		or the caller doesn't have permission to change envid.
//	-E_INVAL if va >= UTOP, or va is not page-aligned.
//	-E_INVAL if perm is inappropriate (see above).
//	-E_NO_MEM if there's no memory to allocate the new page,
//		or to allocate any necessary page tables.
static int
sys_page_alloc(envid_t envid, uintptr_t va, int perm)
{
	// Hint: This function is a wrapper around page_alloc() and
	//   page_insert() from kern/pmap.c.
	//   Most of the new code you write should be to check the
	//   parameters for correctness.
	//   If page_insert() fails, remember to free the page you
	//   allocated!

	// LAB 3: Your code here.
	Env *env;
	int ret;
	
	ret = envid2env(envid, &env, true);
	if (ret < 0) return ret;

	if ((va >= UTOP) || (va != (va - PGOFF(va)))) return -E_INVAL;
	if (perm & (~PTE_SYSCALL)) return -E_INVAL;

	Page *pp = page_alloc();
	ret = page_insert(env->env_pgdir, pp, va, perm);
	if (ret < 0) {
		page_free(pp);
		return ret;
	}
	memset(page2kva(pp),0,PGSIZE);

	return 0;
}

// Map the page of memory at 'srcva' in srcenvid's address space
// at 'dstva' in dstenvid's address space with permission 'perm'.
// Perm has the same restrictions as in sys_page_alloc, except
// that it also must not grant write access to a read-only
// page.
//
// Return 0 on success, < 0 on error.  Errors are:
//	-E_BAD_ENV if srcenvid and/or dstenvid doesn't currently exist,
//		or the caller doesn't have permission to change one of them.
//	-E_INVAL if srcva >= UTOP or srcva is not page-aligned,
//		or dstva >= UTOP or dstva is not page-aligned.
//	-E_INVAL is srcva is not mapped in srcenvid's address space.
//	-E_INVAL if perm is inappropriate (see sys_page_alloc).
//	-E_INVAL if (perm & PTE_W), but srcva is read-only in srcenvid's
//		address space.
//	-E_NO_MEM if there's no memory to allocate any necessary page tables.
static int
sys_page_map(envid_t srcenvid, uintptr_t srcva,
	     envid_t dstenvid, uintptr_t dstva, int perm)
{
	// Hint: This function is a wrapper around page_lookup() and
	//   page_insert() from kern/pmap.c.
	//   Again, most of the new code you write should be to check the
	//   parameters for correctness.
	//   Use the third argument to page_lookup() to
	//   check the current permissions on the page.

	// LAB 3: Your code here.
	Env *srcEnv, *dstEnv;
	int ret;

	//cprintf("sys_page_map\n");
	
	ret = envid2env(srcenvid, &srcEnv, true);
	if (ret < 0) {
		//	cprintf("invalid srcenvid\n");
		return ret;
	}
	ret = envid2env(dstenvid, &dstEnv, true);
	if (ret < 0) {
		//	cprintf("invalid dstenvid\n");
		return ret;
	}

	if ((srcva >= UTOP) || (srcva != (srcva - PGOFF(srcva)))) {
		//	cprintf("bad srcva\n");
		return -E_INVAL;
	}
	if ((dstva >= UTOP) || (dstva != (dstva - PGOFF(dstva)))) {
		//	cprintf("bad dstva\n");
		return -E_INVAL;
	}
	if (perm & (~PTE_SYSCALL)) {
		//	cprintf("bad perms\n");
		return -E_INVAL;
	}

	//	cprintf("after checks\n");

	pte_t *pte;
	Page *pp = page_lookup(srcEnv->env_pgdir, srcva, &pte);
	//	cprintf("after page lookup\n");
	if (!pp) {
		//	cprintf("page unmapped in src\n");
		return -E_INVAL;
	}
	if ((perm & PTE_W) && !((*pte) & PTE_W)) {
		//	cprintf("W in perm but not in pte\n");
		return -E_INVAL;
	}

	//	cprintf("before page insert\n");
	ret = page_insert(dstEnv->env_pgdir, pp, dstva, perm);
	//	cprintf("after page insert\n");
	if (ret < 0) {
		//	cprintf("page insert failed\n");
		return ret;
	}

	return 0;
}

// Unmap the page of memory at 'va' in the address space of 'envid'.
// If no page is mapped, the function silently succeeds.
//
// Return 0 on success, < 0 on error.  Errors are:
//	-E_BAD_ENV if environment envid doesn't currently exist,
//		or the caller doesn't have permission to change envid.
//	-E_INVAL if va >= UTOP, or va is not page-aligned.
static int
sys_page_unmap(envid_t envid, uintptr_t va)
{
	// Hint: This function is a wrapper around page_remove().

	// LAB 3: Your code here.
	Env *env;
	int ret;
	
	ret = envid2env(envid, &env, true);
	if (ret < 0) return ret;

	if ((va >= UTOP) || (va != (va - PGOFF(va)))) return -E_INVAL;
	page_remove(env->env_pgdir, va);
	return 0;
}

int32_t
sys_env_inc_tickets(envid_t envid, uint16_t num)
{
	Env *env;
	int ret;
	ret = envid2env(envid, &env, true);
	if (ret < 0) return ret;

	if (env->tickets + num < env->tickets) return -E_INVAL;
	env->tickets = env->tickets + num;
	return env->tickets;
}

int32_t
sys_env_dec_tickets(envid_t envid, uint16_t num)
{
	Env *env;
	int ret;
	ret = envid2env(envid, &env, true);
	if (ret < 0) return ret;

	if (num >= env->tickets) return -E_INVAL;
	env->tickets = env->tickets - num;
	return env->tickets;
}

// Try to send 'value' to the target env 'envid'.
// If srcva < UTOP, then also send page currently mapped at 'srcva',
// so that receiver gets a duplicate mapping of the same page.
//
// The send fails with a return value of -E_IPC_NOT_RECV if the
// target is not blocked, waiting for an IPC.
//
// The send also can fail for the other reasons listed below.
//
// Otherwise, the send succeeds, and the target's ipc fields are
// updated as follows:
//    env_ipc_recving is set to 0 to block future sends;
//    env_ipc_from is set to the sending envid;
//    env_ipc_value is set to the 'value' parameter;
//    env_ipc_perm is set to 'perm' if a page was transferred, 0 otherwise.
// The target environment is marked runnable again, returning 0
// from the paused sys_ipc_recv system call.  (Hint: does the
// sys_ipc_recv function ever actually return?)
//
// If the sender wants to send a page but the receiver isn't asking for one,
// then no page mapping is transferred, but no error occurs.
// The ipc only happens when no errors occur.
//
// Returns 0 on success, < 0 on error.
// Errors are:
//	-E_BAD_ENV if environment envid doesn't currently exist.
//		(No need to check permissions.)
//	-E_IPC_NOT_RECV if envid is not currently blocked in sys_ipc_recv,
//		or another environment managed to send first.
//	-E_INVAL if srcva < UTOP but srcva is not page-aligned.
//	-E_INVAL if srcva < UTOP and perm is inappropriate
//		(see sys_page_alloc).
//	-E_INVAL if srcva < UTOP but srcva is not mapped in the caller's
//		address space.
//	-E_INVAL if (perm & PTE_W), but srcva is read-only in the
//		current environment's address space.
//	-E_NO_MEM if there's not enough memory to map srcva in envid's
//		address space.
static int
sys_ipc_try_send(envid_t envid, uint32_t value, uintptr_t srcva, unsigned perm)
{
	Env *recvr;
	int ret;
	
	// Check envid is valid
	if ((ret = envid2env(envid,&recvr,false)) < 0) {
		return ret;
	}
	// Check the environment is receiving
	if (recvr->env_ipc_recving == false) {
		return -E_IPC_NOT_RECV;
	}

	// Check page issues if we're sending a page
	if (srcva < UTOP) {
		if (!PGALIGNED(srcva)) return -E_INVAL;
		if (perm & ~PTE_SYSCALL) return -E_INVAL;
		if (user_mem_check(curenv,srcva,PGSIZE,PTE_U) < 0) return -E_INVAL;

		if (recvr->env_ipc_dstva < UTOP) {
			pte_t *pte;
			Page *pp = page_lookup(curenv->env_pgdir, srcva, &pte);
			if (!pp) {
				return -E_INVAL;
			}
			if ((perm & PTE_W) && !((*pte) & PTE_W)) {
				return -E_INVAL;
			}

			ret = page_insert(recvr->env_pgdir, pp, recvr->env_ipc_dstva, perm);
			if (ret < 0) {
				return ret;
			}
		}
	} else {
		perm = 0;
	}

	recvr->env_ipc_recving = false;
	recvr->env_ipc_from = curenv->env_id;
	recvr->env_ipc_value = value;
	recvr->env_ipc_perm = perm;

	// Recv syscall should return 0 in recvr!
	recvr->env_tf.tf_regs.reg_eax = 0;

	recvr->env_status = ENV_RUNNABLE;
	return 0;
}

// Block until a value is ready.  Record that you want to receive
// using the env_ipc_recving and env_ipc_dstva fields of struct Env,
// mark yourself not runnable, and then give up the CPU.
//
// If 'dstva' is < UTOP, then you are willing to receive a page of data.
// 'dstva' is the virtual address at which the sent page should be mapped.
//
// This function only returns on error, but the system call will eventually
// return 0 on success.
// Return < 0 on error.  Errors are:
//	-E_INVAL if dstva < UTOP but dstva is not page-aligned.
static int
sys_ipc_recv(uintptr_t dstva)
{
	// LAB 4: Your code here.
	if ((dstva < UTOP)&&(!(PGALIGNED(dstva)))) {
		return -E_INVAL;
	}
	
	curenv->env_ipc_dstva = dstva;
	curenv->env_ipc_recving = true;

	curenv->env_status = ENV_NOT_RUNNABLE;
	sys_yield();
	return 0;
}


// Look up a program from the kernel's program collection.
// Return the ID for the program named 'name' (length of name is 'len').
// If no such program exists, returns -E_NOT_EXEC.
// On memory fault destroys the environment.
// All valid program IDs are large positive numbers
// greater than or equal to PROGRAM_OFFSET.
static int
sys_program_lookup(uintptr_t name_ptr, size_t len)
{
	int i;

	user_mem_assert(curenv, name_ptr, len, PTE_U);
	const char *name = (const char *) name_ptr;

	for (i = 0; i < nprograms; i++)
		if (strncmp(programs[i].name, name, len) == 0)
			return PROGRAM_OFFSET + i;

	return -E_NOT_EXEC;
}

// Copy 'size' bytes of data from the embedded ELF binary
// for program 'programid' into address 'va' in environment 'envid'.
// Start copying 'offset' bytes into the ELF.
// Thus, multiple calls to sys_program_read can read an entire ELF binary.
// If 'offset' or 'offset + size' is too large for the ELF,
// returns the number of bytes actually copied
// (which might be 0 if nothing was copied).
//
// Returns the number of bytes read on success, < 0 on error.  Errors are:
//	-E_BAD_ENV if environment envid doesn't currently exist,
//		or the caller doesn't have permission to change envid.
//	-E_INVAL if programid is an invalid ELF program ID.
//	Kills the calling environment if [va, va+size) is not user-writable.
static ssize_t
sys_program_read(envid_t envid, uintptr_t va,
		 int programid, uint32_t offset, size_t size)
{
        // LAB 4: Your code here.
	int r;
      	Env *env;
	Program *program;
	size_t readable;

	if (programid < PROGRAM_OFFSET || programid >= PROGRAM_OFFSET + nprograms) return -E_INVAL;
	if ((r = envid2env(envid,&env,true)) < 0) return r;

	program = &programs[programid];

	if (offset > program->size) return 0;
	readable = program->size - offset;
	if (readable < size) size = readable;

	user_mem_assert(env, va, size, PTE_U | PTE_W);
	lcr3(PADDR(env->env_pgdir));
	memcpy((void *)va, program->data + offset, size);
	lcr3(PADDR(curenv->env_pgdir));

	return size;
}

// Set the goal other envs need to prove to manipulate this env
static int sys_set_goal(uintptr_t goal){
  curenv->goal = (Formula)goal;
  return 0;
}

// Set the proof to be used by the kernel when this env
// wants to manipulate another.
static int sys_set_proof(uintptr_t proof){
  curenv->proof = (Proof)proof;
  return 0;
}

// Dispatches to the correct kernel function, passing the arguments.
int32_t
syscall(uint32_t syscallno, uint32_t a1, uint32_t a2, uint32_t a3, uint32_t a4, uint32_t a5)
{
	// Call the function corresponding to the 'syscallno' parameter.
	// Return any appropriate return value.
	// LAB 3: Your code here.
	switch (syscallno) {
	case SYS_cputs: sys_cputs(a1, a2); break;
	case SYS_cgetc: return sys_cgetc();
	case SYS_getenvid: return sys_getenvid();
	case SYS_env_destroy: return sys_env_destroy(a1);
	case SYS_yield: sys_yield(); break;
	case SYS_env_set_status: return sys_env_set_status(a1, a2);
	case SYS_exofork: return sys_exofork();
	case SYS_page_alloc: return sys_page_alloc(a1, a2, a3);
	case SYS_page_map: return sys_page_map(a1, a2, a3, a4, a5);
	case SYS_page_unmap: return sys_page_unmap(a1, a2);
	case SYS_env_inc_tickets: return sys_env_inc_tickets(a1, a2);
	case SYS_env_dec_tickets: return sys_env_dec_tickets(a1, a2);
	case SYS_env_set_pgfault_upcall: return sys_env_set_pgfault_upcall(a1, a2);
	case SYS_ipc_try_send: return sys_ipc_try_send(a1, a2, a3, a4);
	case SYS_ipc_recv: return sys_ipc_recv(a1);
	case SYS_program_lookup: return sys_program_lookup(a1, a2);
	case SYS_program_read: return sys_program_read(a1, a2, a3, a4, a5);
	case SYS_env_set_trapframe: return sys_env_set_trapframe(a1, a2);
	case SYS_set_goal: return sys_set_goal(a1);
	case SYS_set_proof: return sys_set_proof(a1);
	default: return -E_INVAL;
	}

	return syscallno;
}

