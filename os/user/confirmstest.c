#include <inc/lib.h>
#include <inc/proof.h>
#include <inc/formula.h>

#define OK 42

static uint8_t heapBuffer[PGSIZE];


Proof receive_proof() {
  size_t offset = (size_t) ipc_recv(NULL, UTEMP, NULL);
  Proof p = proof_cp((Proof)((uint8_t *)UTEMP + offset));
  sys_page_unmap(0, UTEMP);
  return p;
}

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

bool confirm(Formula f){
  //formula_print(f);
  //cprintf("\n CONFIRMED! \n");
  return false;
}

void umain(int argc, char **argv) {
	Heap heap;
	init_heap(&heap, &heapBuffer, PGSIZE);
	set_heap(&heap);

	envid_t who;
	if ((who = fork()) != 0) {
		// parent
	  Formula goal = formula_pred(OK, principal_var(0));
		sys_set_confirms_upcall(0, (uintptr_t)&confirm, (uintptr_t)&heap);
		sys_set_goal(goal);
		
		while(true) sys_yield();
	} else {
		// child
	  Formula goal = formula_pred(OK, principal_pcpl(thisenv->env_id));
		Proof proof = says_from_confirms(thisenv->env_parent_id, goal);
		sys_set_proof(proof);

		sys_env_destroy(thisenv->env_parent_id);
	}
}
