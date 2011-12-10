// yield the processor to other environments

#include <inc/lib.h>

void
umain(int argc, char **argv)
{
	if (thisenv->env_id == 0x1000) {
		cprintf("env %08x has %d tickets\n", thisenv->env_id, 
			sys_env_inc_tickets(thisenv->env_id,2));
	} else if (thisenv->env_id == 0x1001) {
		cprintf("env %08x has %d tickets\n", thisenv->env_id, 
			sys_env_inc_tickets(thisenv->env_id,1));
	} else {
		cprintf("env %08x has %d tickets\n", thisenv->env_id,
			sys_env_inc_tickets(thisenv->env_id,0));
	}
        for (int i=0; i<10000; i++) {
		sys_yield();
		cprintf("env %08x\n", thisenv->env_id);
	}
}
