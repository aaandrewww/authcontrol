#ifndef JOS_INC_SYSCALL_H
#define JOS_INC_SYSCALL_H

/* system call numbers */
enum {
	SYS_cputs = 0,
	SYS_cgetc,
	SYS_getenvid,
	SYS_env_destroy,
	SYS_yield,
	SYS_env_set_status,
	SYS_exofork,
	SYS_page_alloc,
	SYS_page_map,
	SYS_page_unmap,
	SYS_env_inc_tickets,
	SYS_env_dec_tickets,
	SYS_env_set_trapframe,
	SYS_env_set_pgfault_upcall,
	SYS_ipc_try_send,
	SYS_ipc_recv,
	SYS_program_lookup,
	SYS_program_read,
	NSYSCALLS
};

#endif /* !JOS_INC_SYSCALL_H */
