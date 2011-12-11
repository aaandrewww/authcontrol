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

void umain(int argc, char **argv) {
	Heap heap;
	init_heap(&heap, &heapBuffer, PGSIZE);
	set_heap(&heap);

	envid_t who;
	if ((who = fork()) != 0) {
		// parent
		Proof p = receive_proof();
		proof_print(p);
		
		// Uncomment this line to allow parent to kill child
                //sys_set_proof(p);
		sys_env_destroy(who);
	} else {
		// child
		Formula goal = formula_pred(OK, principal_var(0));
		sys_set_goal(goal);
		Proof parent_ok = says_from_signed(thisenv->env_id, formula_subst(goal, 0, thisenv->env_parent_id));
		send_proof(thisenv->env_parent_id, parent_ok);

		while (true) {
			
		}
	}
}
