// yield the processor to other environments

#include <inc/lib.h>

void
umain(int argc, char **argv)
{
	while (true) {
		sys_yield();
		cprintf("env %08x\n", thisenv->env_id);
	}
}
