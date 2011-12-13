#include <inc/lib.h>
#include <inc/proof.h>
#include <inc/formula.h>

#define OK 42

static uint8_t heapBuffer[4*PGSIZE];


//Proof receive_proof() {
//  size_t offset = (size_t) ipc_recv(NULL, UTEMP, NULL);
//  Proof p = proof_cp((Proof)((uint8_t *)UTEMP + offset));
//  sys_page_unmap(0, UTEMP);
//  return p;
//}
//
//void send_proof(envid_t to, Proof p) {
//  // Copy the proof to UTEMP
//  sys_page_alloc(0, UTEMP, PTE_U | PTE_W);
//  Heap tempHeap;
//  init_heap(&tempHeap, UTEMP, PGSIZE);
//  Heap *oldHeap = set_heap(&tempHeap);
//  Proof copy = proof_cp(p);
//  size_t offset = (uintptr_t)copy - (uintptr_t)UTEMP;
//
//  // Send the proof
//  ipc_send(to, offset, UTEMP, PTE_U);
//  sys_page_unmap(0, UTEMP);
//
//  // Reset the heap
//  set_heap(oldHeap);
//}

void umain(int argc, char **argv) {
	Heap heap;
	init_heap(&heap, &heapBuffer, 4*PGSIZE);
	set_heap(&heap);
	int i;

	envid_t who;
	if ((who = fork()) != 0) {
		// parent


		// Simple proof
//	  Proof p = receive_proof();
//		sys_set_proof(p);

		// Delegation
	  Proof del = receive_proof();
    Formula pred = formula_pred(OK, principal_pcpl(thisenv->env_id));
    Proof perm = says_from_signed(thisenv->env_id, pred);
    Proof use_del = use_delegation(who, thisenv->env_id, thisenv->env_id, OK, del, perm);
    sys_set_proof(use_del);

    for(i = 0; i < 1500; i++){
      sys_proof_test(who);
    }
    sys_env_destroy(who);
	} else {
		// child
		Formula goal = formula_pred(OK, principal_var(0));

		// Comment this line to revert to parent/child permission checks
		sys_set_goal(goal);

		// Simple proof
//		Proof parent_ok = says_from_signed(thisenv->env_id, formula_subst(goal, 0, thisenv->env_parent_id));
//		send_proof(thisenv->env_parent_id, parent_ok);

		// Delagation
    Proof del = delegate_from_signed(thisenv->env_id, thisenv->env_parent_id, OK);
    send_proof(thisenv->env_parent_id, del);

		while (true) {
		}
	}
}

