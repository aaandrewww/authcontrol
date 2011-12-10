#include <inc/lib.h>
#include <inc/proof.h>
#include <inc/formula.h>

#define OK 42

Proof receive_proof() {
	size_t offset = (size_t) ipc_recv(NULL, UTEMP, NULL);
	cprintf("Received a proof\n");
	proof_print((Proof)((uintptr_t)UTEMP + offset));
	//Proof p = proof_cp((Proof)((uint8_t *)UTEMP + (size_t)ret));
	sys_page_unmap(0, UTEMP);
	return NULL;
        //return p;
}

void send_proof(envid_t to, Proof p) {
	// Assume the proof fits on one page...
	uintptr_t page = ROUNDDOWN((uintptr_t)p, PGSIZE);
	size_t offset = (uintptr_t)p - page;
	cprintf("Sending proof at %08x on page %08x\n", offset, page);
	ipc_send(to, offset, (void *)page, PTE_U);
	proof_print((Proof)(page + offset));
}

void umain(int argc, char **argv) {
	envid_t who;
	if ((who = fork()) != 0) {
		// parent
		Proof p = receive_proof();
		proof_print(p);
	} else {
		// child
		Formula goal = formula_pred(OK, principal_var(0));
		formula_print(goal);
		cprintf("\n");
		sys_set_goal(goal);
		cprintf("Goal set.\n");
		Proof parent_ok = says_from_signed(thisenv->env_id, formula_subst(goal, 0, thisenv->env_parent_id));
		proof_print(parent_ok);
		cprintf("\n");
		cprintf("Checking:\n");
		cprintf("%d\n", proof_check(formula_says(principal_pcpl(thisenv->env_id), formula_subst(goal, 0, thisenv->env_parent_id)), parent_ok, NULL));
		send_proof(thisenv->env_parent_id, parent_ok);
	}
}
