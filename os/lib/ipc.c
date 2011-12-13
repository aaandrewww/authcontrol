// User-level IPC library routines

#include <inc/lib.h>
#include <inc/proof.h>
#include <inc/mm.h>

// Receive a proof using ipc
Proof receive_proof() {
  size_t offset = (size_t) ipc_recv(NULL, UTEMP, NULL);
  Proof p = proof_cp((Proof)((uint8_t *)UTEMP + offset));
  sys_page_unmap(0, UTEMP);
  return p;
}

// Send a proof over IPC
void send_proof(envid_t to, Proof p) {
  // Copy the proof to UTEMP
  sys_page_alloc(0, UTEMP, PTE_U | PTE_W);
  Heap tempHeap;
  init_heap(&tempHeap, UTEMP, PGSIZE);
  Heap *oldHeap = set_heap(&tempHeap);
  Proof copy = proof_cp(p);
  size_t offset = (uintptr_t)copy - (uintptr_t)UTEMP;

  // Send the proof
  ipc_send(to, offset, UTEMP, PTE_U);
  sys_page_unmap(0, UTEMP);

  // Reset the heap
  set_heap(oldHeap);
}

// Receive a value via IPC and return it.
// If 'pg' is nonnull, then any page sent by the sender will be mapped at
//	that address.
// If 'from_env_store' is nonnull, then store the IPC sender's envid in
//	*from_env_store.
// If 'perm_store' is nonnull, then store the IPC sender's page permission
//	in *perm_store (this is nonzero iff a page was successfully
//	transferred to 'pg').
// If the system call fails, then store 0 in *fromenv and *perm (if
//	they're nonnull) and return the error.
// Otherwise, return the value sent by the sender
//
// Hint:
//   Use 'thisenv' to discover the value and who sent it.
//   If 'pg' is null, pass sys_ipc_recv a value that it will understand
//   as meaning "no page".  (Zero is not the right value, since that's
//   a perfectly valid place to map a page.)
int32_t
ipc_recv(envid_t *from_env_store, void *pg, int *perm_store)
{
	// LAB 4: Your code here.
	void *dstva = (void *)UTOP;
	if (pg) dstva = pg;
	int ret = sys_ipc_recv(dstva);
	if (ret < 0) {
		if (perm_store) *perm_store = 0;
		if (from_env_store) *from_env_store = 0;
		return ret;
	} else {
		if (perm_store) *perm_store = thisenv->env_ipc_perm;
		if (from_env_store) *from_env_store = thisenv->env_ipc_from;
		return thisenv->env_ipc_value;
	}
}

// Send 'val' (and 'pg' with 'perm', if 'pg' is nonnull) to 'toenv'.
// This function keeps trying until it succeeds.
// It should panic() on any error other than -E_IPC_NOT_RECV.
//
// Hint:
//   Use sys_yield() to be CPU-friendly.
//   If 'pg' is null, pass sys_ipc_recv a value that it will understand
//   as meaning "no page".  (Zero is not the right value.)
void
ipc_send(envid_t to_env, uint32_t val, void *pg, int perm)
{
	//cprintf("to_env: %08x from_env: %08x\n", to_env, thisenv->env_id);
	int ret = -E_IPC_NOT_RECV;
	if (!pg) pg = (void *)UTOP;
	while (true) {
		ret = sys_ipc_try_send(to_env,val,pg,perm);
		if (ret == 0) return;
		if (ret != -E_IPC_NOT_RECV) break;
		sys_yield();
	}
	panic("Send failed: %e", ret);
}
