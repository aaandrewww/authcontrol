#include <inc/lib.h>
#include <inc/proof.h>
#include <inc/formula.h>

#define OK 42

static uint8_t heapBuffer[PGSIZE];

void umain(int argc, char **argv) {
	Heap heap;
	init_heap(&heap, &heapBuffer, PGSIZE);
	set_heap(&heap);

	envid_t who;
	if ((who = fork()) != 0) {
		// parent
		Proof p = receive_proof();
//		proof_print(p);
//		cprintf("\n");
		// Uncomment this line to allow parent to kill child w/ no proof
    sys_set_proof(p);
		sys_env_destroy(who);
	} else {
		// child
		Formula goal = formula_pred(OK, principal_var(0));
//		sys_set_goal(goal);
		Proof parent_ok = says_from_signed(thisenv->env_id, formula_subst(goal, 0, thisenv->env_parent_id));
		send_proof(thisenv->env_parent_id, parent_ok);

		while (true) {
			
		}
	}
}
