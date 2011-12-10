// Simple command-line kernel monitor useful for
// controlling the kernel and exploring the system interactively.

#include <inc/stdio.h>
#include <inc/string.h>
#include <inc/memlayout.h>
#include <inc/assert.h>
#include <inc/x86.h>

#include <kern/console.h>
#include <kern/monitor.h>
#include <kern/kdebug.h>
#include <kern/trap.h>
#include <kern/env.h>
#include <kern/pmap.h>

#define CMDBUF_SIZE	80	// enough for one VGA text line
#define NBREAKPOINTS    8

struct Command {
	const char *name;
	const char *desc;
	// return -1 to force monitor to exit
	int (*func)(int argc, char** argv, struct Trapframe* tf);
};

static struct Command commands[] = {
	{ "help", "Display this list of commands", mon_help },
	{ "kerninfo", "Display information about the kernel", mon_kerninfo },
	{ "backtrace", "Display a backtrace from the current eip", mon_backtrace},
	{ "setbreak", "Set a breakpoint", mon_set_break},
	{ "clearbreak", "Clear a breakpoint", mon_clear_break},
	{ "listbreak", "List current breakpoints", mon_list_break},
	{ "s", "Step one instruction", mon_step},
	{ "eipof", "Print the address of a source line", mon_eip_of},
	{ "p", "p va count: prints count words starting at va", mon_print_mem},
	{ "printframe", "Print the current trap frame", mon_print_frame},
	{ "exit", "Exit the kernel monitor", mon_exit}
};
#define NCOMMANDS ((int) (sizeof(commands)/sizeof(commands[0])))

unsigned read_eip() __attribute__((noinline));

struct Breakpoint {
	uintptr_t breakpoint;
	uint8_t   byte;
};

static int nbreaks = 0;
static struct Breakpoint breakpoints[NBREAKPOINTS];
static uintptr_t lastbreak = 0;
static int lastcommandstep = 0;

/***** Implementations of basic kernel monitor commands *****/

int
atoi(const char *string)
{
	int i = 0;
	int c = 0;
	for (; *string != '\0'; string++) {
		switch (*string) {
		case '9': c++;
		case '8': c++;
		case '7': c++;
		case '6': c++;
		case '5': c++;
		case '4': c++;
		case '3': c++;
		case '2': c++;
		case '1': c++;
		case '0':
			i = (i*10) + c;
			c = 0;
			continue;
		default: break;
		}
	}
	return i;
}

uint32_t
ahextoi(const char *string)
{
	uint32_t i = 0;
	uint32_t c = 0;
	for (; *string != '\0'; string++) {
		switch (*string) {
		case 'f': c++;
		case 'e': c++;
		case 'd': c++;
		case 'c': c++;
		case 'b': c++;
		case 'a': c++;
		case '9': c++;
		case '8': c++;
		case '7': c++;
		case '6': c++;
		case '5': c++;
		case '4': c++;
		case '3': c++;
		case '2': c++;
		case '1': c++;
		case '0':
			i = (i*16) + c;
			c = 0;
			continue;
		default: break;
		}
	}
	return i;
}

int
mon_print_mem(int argc, char **argv, struct Trapframe *tf)
{
	if (argc != 3) {
		cprintf("Usage: p va count\n");
		return 0;
	}
	uint32_t *va = (uint32_t *)ahextoi(argv[1]);
	uint32_t count = atoi(argv[2]);
	for (uint32_t i=0; i<count; i++) {
		if (!(i % 4)) cprintf("0x%08x:\t", &va[i]);
		cprintf("%08x", va[i]);
		if ((i % 4)==3) cprintf("\n");
		else cprintf("\t");
	}
	cprintf("\n");
	return 0;
}

int
mon_eip_of(int argc, char **argv, struct Trapframe *tf)
{
	if (argc != 3) {
		cprintf("Usage: eip filename linenumber\n");
		return 0;
	}
	uintptr_t eip = 0;
	int ret = debug_lineno_eip(read_eip(), argv[1], atoi(argv[2]), &eip);
	switch (ret) {
	case -1:
		cprintf("Error: invalid string table\n");
		break;
	case -2:
		cprintf("Error: file not found\n");
		break;
	case -3:
		cprintf("Error: line not found\n");
		break;
	case -4:
		cprintf("Error: no instruction address found\n");
		break;
	default:
		cprintf("%s<+%d>: 0x%08x\n", argv[1], atoi(argv[2]), eip);
	}
	return 0;
}

int
mon_print_frame(int argc, char **argv, struct Trapframe *tf)
{
	print_trapframe(tf);
	return 0;
}

int
mon_set_break(int argc, char **argv, struct Trapframe *tf)
{
	if (argc < 2 || argc > 3) {
		cprintf("Usage: setbreak filename linenumber\n");
		cprintf("       setbreak 0xADDRESS\n");
		return 0;
	}
	if (nbreaks < NBREAKPOINTS) {
		uintptr_t eip = 0;
		if (argv[1][0] == '0' && argv[1][1] == 'x') {
			eip = ahextoi(&argv[1][2]);
		} else {
			int ret = debug_lineno_eip(read_eip(), argv[1], atoi(argv[2]), &eip);
			if (ret != 0) {
				cprintf("Error finding address. Check with eipof.\n");
				return 0;
			}
		}
		uint8_t *inst = (uint8_t *) eip;
		breakpoints[nbreaks].breakpoint = eip;
		breakpoints[nbreaks].byte = *inst;
		nbreaks++;
		*inst = 0xCC;
		cprintf("Set breakpoint %d at 0x%08x\n", nbreaks-1, eip);
	} else {
		cprintf("Maximum number of breakpoints set.\n");
	}

	return 0;
}

int
mon_clear_break(int argc, char **argv, struct Trapframe *tf)
{
	if (argc != 2) {
		cprintf("Usage: clearbreak number\n");
		return 0;
	}
	int breaki = atoi(argv[1]);
	if (breaki < 0 || breaki >= nbreaks) {
		cprintf("Error: enter a valid breakpoint number\n");
	} else {
		cprintf("Removing breakpoint at 0x%08x\n", breakpoints[breaki].breakpoint);
		*((uint8_t *) breakpoints[breaki].breakpoint) = breakpoints[breaki].byte;
		for (int i = breaki; i < nbreaks-1; i++) {
			breakpoints[i] = breakpoints[i+1];
		}
		nbreaks--;
	}
	return 0;
}

int
mon_list_break(int argc, char **argv, struct Trapframe *tf)
{
	cprintf("Breakpoints:\n");
	for (int i=0; i < nbreaks; i++) {
		cprintf("%d:\t0x%08x\n", i, breakpoints[i].breakpoint);
	}
	return 0;
}

int
mon_exit(int argc, char **argv, struct Trapframe *tf)
{
	// Force an exit
	return -1;
}

int
mon_help(int argc, char **argv, struct Trapframe *tf)
{
	int i;

	for (i = 0; i < NCOMMANDS; i++)
		cprintf("\033[32m%s\033[37m - %s\n", commands[i].name, commands[i].desc);
	return 0;
}

int
mon_kerninfo(int argc, char **argv, struct Trapframe *tf)
{
	extern char _start[], entry[], etext[], edata[], end[];

	cprintf("Special kernel symbols:\n");
	cprintf("  _start                  %08x (phys)\n", _start);
	cprintf("  entry  %08x (virt)  %08x (phys)\n", entry, entry - KERNBASE);
	cprintf("  etext  %08x (virt)  %08x (phys)\n", etext, etext - KERNBASE);
	cprintf("  edata  %08x (virt)  %08x (phys)\n", edata, edata - KERNBASE);
	cprintf("  end    %08x (virt)  %08x (phys)\n", end, end - KERNBASE);
	cprintf("Kernel executable memory footprint: %dKB\n",
		ROUNDUP(end - entry, 1024) / 1024);
	return 0;
}

int
mon_step(int argc, char **argv, struct Trapframe *tf)
{
	if (tf) {
		// Set the single-step flag to cause a debug interrupt
		tf->tf_eflags = tf->tf_eflags | FL_TF;
		// Record that if we get to debug it was a step
		lastcommandstep = 1;
		// Exit the monitor (we'll be back)
		return -1;
	} else {
		cprintf("Can only single-step after entering monitor from trap!\n");
	}
	return 0;
}

int
mon_backtrace(int argc, char **argv, struct Trapframe *tf)
{
	Eipdebuginfo eipInfo;
	uint32_t level = 0;
	uint32_t ebp;
	uint32_t eip;
	if (tf) {
		eip = tf->tf_eip;
		ebp = tf->tf_regs.reg_ebp;
	} else {
		eip = read_eip();
		ebp = read_ebp();
	}
	assert(eip);
	debuginfo_eip(eip, &eipInfo);
	cprintf("Stack backtrace:\n");
	cprintf("  \033[35m%s:\033[36m%d:\033[37m %s+%x (%d arg)\n", 
			eipInfo.eip_file, 
			eipInfo.eip_line, 
			eipInfo.eip_fn_name, 
			eip-eipInfo.eip_fn_addr,
			eipInfo.eip_fn_narg);
	
	bool kernel = ((!tf) || (tf->tf_cs == GD_KT));
#define PRINT_IF_SAFE(ptr)  \
	(!kernel && (user_mem_check(curenv,(uintptr_t)ptr,sizeof(uint32_t),PTE_U) < 0)) ? \
		cprintf("?") : cprintf("%08x",*((uint32_t *)(ptr)))

	while (ebp) {
		cprintf("\033[33m  %d: ebp \033[37m%08x", level, ebp);
		cprintf("\033[33m  eip \033[37m");
		PRINT_IF_SAFE(ebp+4);
		cprintf("\033[33m  args \033[37m");
		PRINT_IF_SAFE(ebp+8);
		cprintf(" ");
		PRINT_IF_SAFE(ebp+12);
		cprintf(" ");
		PRINT_IF_SAFE(ebp+16);
		cprintf(" ");
		PRINT_IF_SAFE(ebp+20);
		cprintf("\n");

		if (!kernel && (user_mem_check(curenv,(uintptr_t)(ebp+1),sizeof(uint32_t),PTE_U) < 0)) {
			cprintf("  \033[35m?:\033[36m?:\033[37m ?+? (? arg)\n");
		} else {
			eip = *((uint32_t *)ebp+1);     
			debuginfo_eip(eip, &eipInfo);
			cprintf("  \033[35m%s:\033[36m%d:\033[37m %s+%x (%d arg)\n", 
				eipInfo.eip_file, 
				eipInfo.eip_line, 
				eipInfo.eip_fn_name, 
				eip-eipInfo.eip_fn_addr,
				eipInfo.eip_fn_narg);
		}
		if (!kernel && (user_mem_check(curenv,(uintptr_t)ebp,sizeof(uint32_t),PTE_U) < 0)) {
			return 0;
		} else {
			ebp = *((uint32_t *)ebp);
			level++;
		}
	}
	
	return 0;
}



/***** Kernel monitor command interpreter *****/

#define WHITESPACE "\t\r\n "
#define MAXARGS 16

static int
runcmd(char *buf, struct Trapframe *tf)
{
	int argc;
	char *argv[MAXARGS];
	int i;

	// Parse the command buffer into whitespace-separated arguments
	argc = 0;
	argv[argc] = 0;
	while (1) {
		// gobble whitespace
		while (*buf && strchr(WHITESPACE, *buf))
			*buf++ = 0;
		if (*buf == 0)
			break;

		// save and scan past next arg
		if (argc == MAXARGS-1) {
			cprintf("Too many arguments (max %d)\n", MAXARGS);
			return 0;
		}
		argv[argc++] = buf;
		while (*buf && !strchr(WHITESPACE, *buf))
			buf++;
	}
	argv[argc] = 0;

	// Lookup and invoke the command
	if (argc == 0)
		return 0;
	for (i = 0; i < NCOMMANDS; i++) {
		if (strcmp(argv[0], commands[i].name) == 0)
			return commands[i].func(argc, argv, tf);
	}
	cprintf("Unknown command '\033[32m%s\033[37m'\n", argv[0]);
	return 0;
}

void
monitor(struct Trapframe *tf)
{
	cprintf("\033[37;40mWelcome to the JOS kernel monitor!\n");
	cprintf("Type '\033[32mhelp\033[37m' for a list of commands.\n");

	if (tf != NULL)
		print_trapframe(tf);

	mon_cmdline(tf);
}

void
mon_break(struct Trapframe *tf)
{
	uintptr_t eip = tf->tf_eip;

	int wasBreakpoint = 0;
	for (int i=0; i < NBREAKPOINTS; i++) {
		if (breakpoints[i].breakpoint == eip-1) {
			eip = eip-1;
			tf->tf_eip = eip;
			*((uint8_t *) eip) = breakpoints[i].byte;
			lastbreak = eip;
			tf->tf_eflags = tf->tf_eflags | FL_TF;
			wasBreakpoint = 1;
			break;
		}
	}

	if (wasBreakpoint) {
		cprintf("Reached breakpoint: 0x%08x\n", eip);
		mon_cmdline(tf);
	} else {
		monitor(tf);
	}
}

void
mon_debug(struct Trapframe *tf)
{
	cprintf("Last break: %x\n", lastbreak);
	// Check if we're dealing with a breakpoint
	if (lastbreak != 0) {
		// Need to put the breakpoint back
		for (int i=0; i < NBREAKPOINTS; i++) {
			if (breakpoints[i].breakpoint == lastbreak) {
				cprintf("Writing int3 to %x\n", lastbreak);
				*((uint8_t *)lastbreak) = 0xCC;
			}
		}
		lastbreak = 0;
	}

	// Clear the TF flag
	tf->tf_eflags = tf->tf_eflags & (~FL_TF);

	if (lastcommandstep) {
		lastcommandstep = 0;
		// Print the current eip
		cprintf("=> eip 0x%08x\n", tf->tf_eip);

		// Give a prompt
		mon_cmdline(tf);
	}
}

void
mon_cmdline(struct Trapframe *tf)
{
	char *buf;
	while (1) {
		buf = readline("K> ");
		if (buf != NULL)
			if (runcmd(buf, tf) < 0)
				break;
	}	
}

// Return EIP of caller.  Does not work if inlined.
unsigned
read_eip()
{
	uint32_t callerpc;
	__asm __volatile("movl 4(%%ebp), %0" : "=r" (callerpc));
	return callerpc;
}

// Return current EIP
unsigned
read_cur_eip()
{
	uint32_t pc;
	__asm __volatile(".THE_EIP: mov %0,.THE_EIP" : "=r" (pc));
	return pc;
}
