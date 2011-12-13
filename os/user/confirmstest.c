#include <inc/lib.h>
#include <inc/proof.h>
#include <inc/formula.h>

#define OK 42

static uint8_t heapBuffer[PGSIZE];

bool confirm(Formula f){
  return true;
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
