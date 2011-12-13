#include <inc/mmu.h>
#include <inc/x86.h>
#include <inc/assert.h>

#include <kern/pmap.h>
#include <kern/trap.h>
#include <kern/console.h>
#include <kern/monitor.h>
#include <kern/env.h>
#include <kern/syscall.h>
#include <kern/sched.h>
#include <kern/kclock.h>
#include <kern/picirq.h>

static uint32_t totalTime = 0;
static size_t count = 0;

// Global descriptor table.
//
// The kernel and user segments are identical except for the DPL.
// To load the SS register, the CPL must equal the DPL.  Thus,
// we must duplicate the segments for the user and the kernel.
// The last segment, the "task state segment", is used for grody x86
// purposes.
//
static struct Taskstate ts;

static struct Segdesc gdt[] = {
	SEG_NULL,				// 0x0 - unused (always faults)
	SEG(STA_X | STA_R, 0x0, 0xffffffff, 0), // 0x8 - kernel code segment
	SEG(STA_W, 0x0, 0xffffffff, 0),		// 0x10 - kernel data segment
	SEG(STA_X | STA_R, 0x0, 0xffffffff, 3), // 0x18 - user code segment
	SEG(STA_W, 0x0, 0xffffffff, 3),		// 0x20 - user data segment
	SYSSEG16(STS_T32A, (uint32_t)(&ts), sizeof(struct Taskstate), 0)
						// 0x28 - task state segment
						// (grody x86 internals)
};

struct Pseudodesc gdt_pd = {
	sizeof(gdt) - 1, (unsigned long) gdt
};

// Interrupt descriptor table.  (Must be built at run time because
// shifted function addresses can't be represented in relocation records.)
//
struct Gatedesc idt[256] = { { 0 } };
struct Pseudodesc idt_pd = {
	sizeof(idt) - 1, (uint32_t) idt
};


static const char *trapname(int trapno)
{
	static const char * const excnames[] = {
		"Divide error",
		"Debug",
		"Non-Maskable Interrupt",
		"Breakpoint",
		"Overflow",
		"BOUND Range Exceeded",
		"Invalid Opcode",
		"Device Not Available",
		"Double Fault",
		"Coprocessor Segment Overrun",
		"Invalid TSS",
		"Segment Not Present",
		"Stack Fault",
		"General Protection",
		"Page Fault",
		"(unknown trap)",
		"x87 FPU Floating-Point Error",
		"Alignment Check",
		"Machine-Check",
		"SIMD Floating-Point Exception"
	};

	if (trapno < (int) (sizeof(excnames)/sizeof(excnames[0])))
		return excnames[trapno];
	if (trapno == T_SYSCALL)
		return "System call";
	if (trapno >= IRQ_OFFSET && trapno < IRQ_OFFSET + 16)
		return "Hardware Interrupt";
	return "(unknown trap)";
}

#define TRAPHANDLERLINKAGE(name) asmlinkage void name(void)

TRAPHANDLERLINKAGE(th_divide);
TRAPHANDLERLINKAGE(th_debug);
TRAPHANDLERLINKAGE(th_nmi);
TRAPHANDLERLINKAGE(th_brkpt);
TRAPHANDLERLINKAGE(th_oflow);
TRAPHANDLERLINKAGE(th_bound);
TRAPHANDLERLINKAGE(th_illop);
TRAPHANDLERLINKAGE(th_device);
TRAPHANDLERLINKAGE(th_dblflt);
TRAPHANDLERLINKAGE(th_tss);
TRAPHANDLERLINKAGE(th_segnp);
TRAPHANDLERLINKAGE(th_stack);
TRAPHANDLERLINKAGE(th_gpflt);
TRAPHANDLERLINKAGE(th_pgflt);
TRAPHANDLERLINKAGE(th_fperr);
TRAPHANDLERLINKAGE(th_align);
TRAPHANDLERLINKAGE(th_mchk);
TRAPHANDLERLINKAGE(th_simderr);
TRAPHANDLERLINKAGE(th_syscall);
TRAPHANDLERLINKAGE(th_default);
TRAPHANDLERLINKAGE(th_irq0);
TRAPHANDLERLINKAGE(th_irq1);
TRAPHANDLERLINKAGE(th_irq2);
TRAPHANDLERLINKAGE(th_irq3);
TRAPHANDLERLINKAGE(th_irq4);
TRAPHANDLERLINKAGE(th_irq5);
TRAPHANDLERLINKAGE(th_irq6);
TRAPHANDLERLINKAGE(th_irq7);
TRAPHANDLERLINKAGE(th_irq8);
TRAPHANDLERLINKAGE(th_irq9);
TRAPHANDLERLINKAGE(th_irq10);
TRAPHANDLERLINKAGE(th_irq11);
TRAPHANDLERLINKAGE(th_irq12);
TRAPHANDLERLINKAGE(th_irq13);
TRAPHANDLERLINKAGE(th_irq14);
TRAPHANDLERLINKAGE(th_irq15);

void
idt_init(void)
{
	// LAB 2: Your code here.
#define INTGATE(id, name) SETGATE(idt[id], 0, GD_KT, &name, 0)
#define TRAPGATE(id, name) SETGATE(idt[id], 1, GD_KT, &name, 3)
#define USERGATE(id, name) SETGATE(idt[id], 0, GD_KT, &name, 3)
	// * should be TRAP but we always want interrupts off
	INTGATE(T_DIVIDE, th_divide);
	USERGATE(T_DEBUG, th_debug); // *
	INTGATE(T_NMI, th_nmi);
	USERGATE(T_BRKPT, th_brkpt); // *
	USERGATE(T_OFLOW, th_oflow); // *
	INTGATE(T_BOUND, th_bound);
	INTGATE(T_ILLOP, th_illop);
	INTGATE(T_DEVICE, th_device);
	INTGATE(T_DBLFLT, th_dblflt);
	INTGATE(T_TSS, th_tss);
	INTGATE(T_SEGNP, th_segnp);
	INTGATE(T_STACK, th_stack);
	INTGATE(T_GPFLT, th_gpflt);
	INTGATE(T_PGFLT, th_pgflt);
	INTGATE(T_FPERR, th_fperr);
	INTGATE(T_ALIGN, th_align);
	INTGATE(T_MCHK, th_mchk);
	INTGATE(T_SIMDERR, th_simderr);
	USERGATE(T_SYSCALL, th_syscall); // *
#define IRQGATE(id,name) SETGATE(idt[id], 0, GD_KT, &name, 3)
	IRQGATE(IRQ_OFFSET+0,th_irq0);
	IRQGATE(IRQ_OFFSET+1,th_irq1);
	IRQGATE(IRQ_OFFSET+2,th_irq2);
	IRQGATE(IRQ_OFFSET+3,th_irq3);
	IRQGATE(IRQ_OFFSET+4,th_irq4);
	IRQGATE(IRQ_OFFSET+5,th_irq5);
	IRQGATE(IRQ_OFFSET+6,th_irq6);
	IRQGATE(IRQ_OFFSET+7,th_irq7);
	IRQGATE(IRQ_OFFSET+8,th_irq8);
	IRQGATE(IRQ_OFFSET+9,th_irq9);
	IRQGATE(IRQ_OFFSET+10,th_irq10);
	IRQGATE(IRQ_OFFSET+11,th_irq11);
	IRQGATE(IRQ_OFFSET+12,th_irq12);
	IRQGATE(IRQ_OFFSET+13,th_irq13);
	IRQGATE(IRQ_OFFSET+14,th_irq14);
	IRQGATE(IRQ_OFFSET+15,th_irq15);

	struct Gatedesc defaultGate = { 0 };
	SETGATE(defaultGate, 0, GD_KT, &th_default, 0);
	// Set up default interrupt handlers
	for (int i=0; i<256; i++) {
		if (!idt[i].gd_p) idt[i] = defaultGate;
	}

	// Set a gate for the system call interrupt.
	// Hint: Must this gate be accessible from userlevel?

	// LAB 3 (Exercise 4): Your code here.

	// Load the GDT (global [segment] descriptor table).
	// Segments serve many purposes on the x86.  We don't use any of their
	// memory-mapping capabilities, but we need them to set
	// privilege levels and to point to the task state segment.
	asm volatile("lgdt gdt_pd");
	// Immediately reload segment registers.
	// The kernel never uses GS or FS, so we leave those set to
	// the user data segment.
	asm volatile("movw %%ax,%%gs" : : "a" (GD_UD|3));
	asm volatile("movw %%ax,%%fs" : : "a" (GD_UD|3));
	// The kernel does use ES, DS, and SS.  We'll change between
	// the kernel and user data segments as needed.
	asm volatile("movw %%ax,%%es" : : "a" (GD_KD));
	asm volatile("movw %%ax,%%ds" : : "a" (GD_KD));
	asm volatile("movw %%ax,%%ss" : : "a" (GD_KD));
	// Load the kernel text segment into CS.
	asm volatile("ljmp %0,$1f\n 1:\n" : : "i" (GD_KT));
	// For good measure, clear the local descriptor table (LDT),
	// since we don't use it.
	asm volatile("lldt %%ax" : : "a" (0));

	// Load the interrupt descriptor table (IDT).
	asm volatile("lidt idt_pd");

	// Setup a TSS so that we get the right stack
	// when we trap to the kernel.
	ts.ts_esp0 = KSTACKTOP;
	ts.ts_ss0 = GD_KD;

	// Load the TSS.
	ltr(GD_TSS);
}


void
print_trapframe(struct Trapframe *tf, bool trap_just_happened)
{
	cprintf("Trap frame at %p\n", tf);
	print_regs(&tf->tf_regs);
	cprintf("  es   0x----%04x\n", tf->tf_es);
	cprintf("  ds   0x----%04x\n", tf->tf_ds);
	cprintf("  trap 0x%08x %s", tf->tf_trapno, trapname(tf->tf_trapno));
	// If this trap was a page fault that just happened
	// (so %cr2 is meaningful), print the faulting linear address.
	if (trap_just_happened && tf->tf_trapno == T_PGFLT)
		cprintf(" [la 0x%08x]", rcr2());
	cprintf("\n  err  0x%08x", tf->tf_err);
	// For page faults, print unparsed fault error code:
	// U=fault occurred in user mode (K=kernel),
	// WR=a write caused the fault (R=read),
	// PR=a protection violation caused the fault (NP=page not present).
	if (tf->tf_trapno == T_PGFLT)
		cprintf(" [fault err %s,%s,%s]",
			tf->tf_err & 4 ? "U" : "K",
			tf->tf_err & 2 ? "W" : "R",
			tf->tf_err & 1 ? "PR" : "NP");
	cprintf("\n  eip  0x%08x\n", tf->tf_eip);
	cprintf("  cs   0x----%04x\n", tf->tf_cs);
	cprintf("  flag 0x%08x\n", tf->tf_eflags);
	cprintf("  esp  0x%08x\n", tf->tf_esp);
	cprintf("  ss   0x----%04x\n", tf->tf_ss);
}

void
print_regs(struct PushRegs *regs)
{
	cprintf("  edi  0x%08x\n", regs->reg_edi);
	cprintf("  esi  0x%08x\n", regs->reg_esi);
	cprintf("  ebp  0x%08x\n", regs->reg_ebp);
	cprintf("  oesp 0x%08x\n", regs->reg_oesp);
	cprintf("  ebx  0x%08x\n", regs->reg_ebx);
	cprintf("  edx  0x%08x\n", regs->reg_edx);
	cprintf("  ecx  0x%08x\n", regs->reg_ecx);
	cprintf("  eax  0x%08x\n", regs->reg_eax);
}

static void
trap_dispatch(struct Trapframe *tf)
{
	// Handle the breakpoint exception.
	switch (tf->tf_trapno) {                                       
		case T_BRKPT:  
			mon_break(tf);                                         
			return;                                                
		case T_DEBUG:                                                  
			mon_debug(tf);                                         
			return;                                                
	        case T_PGFLT:
			page_fault_handler(tf);
			return;
	        case T_SYSCALL:
			trap_syscall(tf);
			return;
		case IRQ_OFFSET+IRQ_TIMER:
			sched_yield();
	        case IRQ_OFFSET+1:
			kbd_intr();
	        default:
			break;
	}
	// Handle page faults by calling page_fault_handler.

	// LAB 3 (Exercise 3): Your code here.

	// Handle system calls.
	// Extract the system call number and arguments from 'tf',
	// call 'syscall', and arrange for the return value to be passed
	// back to the caller.
	// LAB 3 (Exercise 4): Your code here.

	// Handle clock interrupts.
	// LAB 4: Your code here.


	// Handle keyboard interrupts.
	// LAB 5: Your code here.

	// Handle spurious interrupts
	// The hardware sometimes raises these because of noise on the
	// IRQ line or other reasons. We don't care.
	if (tf->tf_trapno == IRQ_OFFSET + IRQ_SPURIOUS) {
		cprintf("Spurious interrupt on irq 7\n");
		print_trapframe(tf, true);
		return;
	}


	// Unexpected trap: The user process or the kernel has a bug.
	print_trapframe(tf, true);
	if (tf->tf_cs == GD_KT)
		panic("unhandled trap in kernel");
	else {
		env_destroy(curenv);
		return;
	}
}

asmlinkage void
trap(struct Trapframe *tf)
{
	// The environment may have set DF and some versions
	// of GCC rely on DF being clear
	asm volatile("cld" : : : "cc");

	// Check that interrupts are disabled.  If this assertion
	// fails, DO NOT be tempted to fix it by inserting a "cli" in
	// the interrupt path.
	assert(!(read_eflags() & FL_IF));

	if ((tf->tf_cs & 3) == 3) {
		// Trapped from user mode.
		// Copy trap frame (which is currently on the stack)
		// into 'curenv->env_tf', so that running the environment
		// will restart at the trap point.
		assert(curenv);
		curenv->env_tf = *tf;
		// The trapframe on the stack should be ignored from here on.
		tf = &curenv->env_tf;
	}

	// Dispatch based on what type of trap occurred
	trap_dispatch(tf);

	// If we made it to this point, then no other environment was
	// scheduled, so we should return to the current environment
	// if doing so makes sense.
	if (curenv && curenv->env_status == ENV_RUNNABLE)
		env_run(curenv);
	else
		sched_yield();
}

void
trap_syscall(struct Trapframe *tf)
{
	// Pull the arguments out of the trapframe
	uint32_t *regs = (uint32_t *)&tf->tf_regs;
	uint32_t callno = regs[7]; // %eax
	uint32_t a1 = regs[5];     // %edx
	uint32_t a2 = regs[6];	   // %ecx
	uint32_t a3 = regs[4];     // %ebx
	uint32_t a4 = regs[0];	   // %edi
	uint32_t a5 = regs[1];	   // %esi
	// Call syscall and store the result in %eax
//	uint32_t x = read_tsc();
	regs[7] = syscall(callno, a1, a2, a3, a4, a5);
//	x = read_tsc() - x;
//	if(callno == 3){
//	  totalTime += x;
//	  count ++;
//	  if((count % 1500)  == 0 && count != 0)
//	    cprintf("count %u, syscall #%u, avg %u, total %llllu\n", count, callno, totalTime/count, totalTime);
//	}
}


void
page_fault_handler(struct Trapframe *tf)
{
	uint32_t fault_va;

	// Read processor's CR2 register to find the faulting address
	fault_va = rcr2();

	// Page faults in the kernel should cause a panic.
	// LAB 3 (Exercise 8): Your code here.
	if (tf->tf_cs == GD_KT) {
		print_trapframe(tf, true);
		panic("Kernel page fault");
	}

	// If we get here, the page fault happened in user mode.

	// Call the environment's page fault upcall, if one exists.  Set up a
	// page fault stack frame on the user exception stack (below
	// UXSTACKTOP), then branch to curenv->env_pgfault_upcall.
	//
	// The page fault upcall might cause another page fault, in which case
	// we branch to the page fault upcall recursively, pushing another
	// page fault stack frame on top of the user exception stack.
	//
	// In both cases, leave an extra 4 bytes of padding, just below the
	// UTrapframe, to agree with the C calling convention. (What is this
	// padding?)
	//
	// If there's no page fault upcall, the environment didn't allocate a
	// page for its exception stack, the environment can't write to its
	// exception stack page, or the exception stack overflows, then destroy
	// the environment that caused the fault.
	// The grade script assumes you will first check for the page fault
	// upcall and print the "user fault va" message below if there is
	// none.
	//
	// Note that when this function runs, 'tf == &curenv->env_tf'.

	// LAB 4: Your code here.
	if (curenv->env_pgfault_upcall) {
		uintptr_t esp; // Exception stack esp

		//cprintf("Fault at eip 0x%08x\n", tf->tf_eip);
		
		// Check for rentrant exception
		if (tf->tf_esp >= UXSTACKTOP-PGSIZE && tf->tf_esp < UXSTACKTOP) {
			esp = tf->tf_esp;
			//	cprintf("Recursive pgfault!\n");
		} else {
			esp = UXSTACKTOP;
		}

		// Try to make space for the trap frame
		esp = esp - sizeof(struct UTrapframe) - sizeof(uintptr_t);

		// Make sure we can write to the user exception stack, panic and destroy if not
		user_mem_assert(curenv, esp, sizeof(struct UTrapframe) + sizeof(uintptr_t), PTE_U | PTE_W);

		struct UTrapframe *trapframe = (struct UTrapframe *)(esp+sizeof(uintptr_t));
		trapframe->utf_fault_va = fault_va;
		trapframe->utf_err = tf->tf_err;
		trapframe->utf_regs = tf->tf_regs;
		trapframe->utf_eflags = tf->tf_eflags;
		trapframe->utf_esp = tf->tf_esp;
		trapframe->utf_eip = tf->tf_eip;

		tf->tf_esp = esp;
		tf->tf_eip = curenv->env_pgfault_upcall;
		//	cprintf("about to return to pgfault handler at %p\n", tf->tf_eip);
		// Make sure that bad things don't happen when we continue?
	} else {
		// Destroy the environment that caused the fault.
		cprintf("[%08x] user fault va %08x ip %08x\n",
		curenv->env_id, fault_va, tf->tf_eip);
		print_trapframe(tf, true);
		env_destroy(curenv);
	}
}
