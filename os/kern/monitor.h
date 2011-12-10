#ifndef JOS_KERN_MONITOR_H
#define JOS_KERN_MONITOR_H
#ifndef JOS_KERNEL
# error "This is a JOS kernel header; user programs should not #include it"
#endif

struct Trapframe;

// Activate the kernel monitor,
// optionally providing a trap frame indicating the current state
// (NULL if none).
void monitor(struct Trapframe *tf);
// Enter the kernel monitor in debug mode (expects Trapframe)
void mon_debug(struct Trapframe *tf);
void mon_break(struct Trapframe *tf);

// Functions implementing monitor commands.
int mon_list_break(int argc, char **argv, struct Trapframe *tf);
int mon_clear_break(int argc, char **argv, struct Trapframe *tf);
int mon_set_break(int argc, char **argv, struct Trapframe *tf);
int mon_eip_of(int argc, char **argv, struct Trapframe *tf);
int mon_step(int argc, char **argv, struct Trapframe *tf);
int mon_exit(int argc, char **argv, struct Trapframe *tf);
int mon_help(int argc, char **argv, struct Trapframe *tf);
int mon_kerninfo(int argc, char **argv, struct Trapframe *tf);
int mon_print_frame(int argc, char **argv, struct Trapframe *tf);
int mon_print_mem(int argc, char **argv, struct Trapframe *tf);
int mon_backtrace(int argc, char **argv, struct Trapframe *tf);

void mon_cmdline(struct Trapframe *tf);

#endif	// !JOS_KERN_MONITOR_H
