#include <inc/assert.h>
#include <inc/rand.h>

#include <kern/env.h>
#include <kern/pmap.h>
#include <kern/monitor.h>

// Choose a user environment to run and run it.
void
sched_yield(void)
{
	uint32_t current_tickets = 0;
	for (uint32_t i = 1; i < NENV; i++) {
		if (envs[i].env_status == ENV_RUNNABLE) {
			current_tickets += envs[i].tickets;
		}
	}

	// If there are no eligible processes, do something else
	if (current_tickets == 0) {
		// Run the special idle environment when nothing else is runnable
		if (envs[0].env_status == ENV_RUNNABLE)
			env_run(&envs[0]);
		else {
			cprintf("Idle loop - nothing more to do!\n");
			while (1)
				monitor(NULL);
		}
	}

	uint32_t winner = rand_beneath(current_tickets);

	// Find the winning env!
	for (uint32_t i = 1; i < NENV; i++) {
		if (envs[i].env_status == ENV_RUNNABLE) {
			if (winner < envs[i].tickets) {
				env_run(&envs[i]);
			} else {
				winner -= envs[i].tickets;
			}
		}
	}
}
