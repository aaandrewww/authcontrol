/* See COPYRIGHT for copyright information. */

#include <inc/mmu.h>
#include <inc/memlayout.h>
#include <inc/trap.h>

#include <kern/picirq.h>


###################################################################
# exceptions/interrupts
###################################################################

/* The TRAPHANDLER macro defines a globally-visible function for handling
 * a trap.
 * The function can be referenced from C++ after you declare it, for
 * instance using "asmlinkage FUNCTIONNAME()".
 * It pushes a trap number onto the stack, then jumps to _alltraps.
 * Use TRAPHANDLER for traps where the CPU automatically pushes an error code.
 */
#define TRAPHANDLER(name, num)						\
	.globl name;		/* define global symbol for 'name' */	\
	.type name, @function;	/* symbol type is function */		\
	.align 2;		/* align function definition */		\
	name:			/* function starts here */		\
	pushl $(num);							\
	jmp _alltraps

/* Use TRAPHANDLER_NOEC for traps where the CPU doesn't push an error code.
 * It pushes a 0 in place of the error code, so the trap frame has the same
 * format in either case.
 */
#define TRAPHANDLER_NOEC(name, num)					\
	.globl name;							\
	.type name, @function;						\
	.align 2;							\
	name:								\
	pushl $0;							\
	pushl $(num);							\
	jmp _alltraps

#define TRAPHANDLER_DEBUG(name, num)					\
	.global name		;					\
	.type name, @function	;					\
	.align 2		;					\
name:									\
	pushf			;					\
	andl	$0xFEFF,(%esp)	;					\
	popf			;					\
	pushl	$0		;					\
	pushl	$(num)		;					\
	jmp	_alltraps	;
	
.text

/*
 * Lab 2: Your code here for generating entry points for the different traps.
 */
	TRAPHANDLER_NOEC(th_divide, T_DIVIDE) ;
	TRAPHANDLER_DEBUG(th_debug, T_DEBUG)   ;
	TRAPHANDLER_NOEC(th_nmi, T_NMI)	      ;
	TRAPHANDLER_NOEC(th_brkpt, T_BRKPT)   ;
	TRAPHANDLER_NOEC(th_oflow, T_OFLOW)   ;
	TRAPHANDLER_NOEC(th_bound, T_BOUND)   ;
	TRAPHANDLER_NOEC(th_illop, T_ILLOP)   ;
	TRAPHANDLER_NOEC(th_device, T_DEVICE) ;
	TRAPHANDLER(th_dblflt, T_DBLFLT)      ;
	TRAPHANDLER(th_tss, T_TSS)	      ;
	TRAPHANDLER(th_segnp, T_SEGNP)	      ;
	TRAPHANDLER(th_stack, T_STACK)	      ;
	TRAPHANDLER(th_gpflt, T_GPFLT)	      ;
	TRAPHANDLER(th_pgflt, T_PGFLT)	      ;
	TRAPHANDLER_NOEC(th_fperr, T_FPERR)   ;
	TRAPHANDLER(th_align, T_ALIGN)	      ;
	TRAPHANDLER_NOEC(th_mchk, T_MCHK)     ;
	TRAPHANDLER_NOEC(th_simderr, T_SIMDERR) ;
	TRAPHANDLER_NOEC(th_syscall, T_SYSCALL) ;
	TRAPHANDLER_NOEC(th_default, T_DEFAULT) ;
	TRAPHANDLER_NOEC(th_irq0, 32)		;
	TRAPHANDLER_NOEC(th_irq1, 33)		;
	TRAPHANDLER_NOEC(th_irq2, 34)		;
	TRAPHANDLER_NOEC(th_irq3, 35)		;
	TRAPHANDLER_NOEC(th_irq4, 36)		;
	TRAPHANDLER_NOEC(th_irq5, 37)		;
	TRAPHANDLER_NOEC(th_irq6, 38)		;
	TRAPHANDLER_NOEC(th_irq7, 39)		;
	TRAPHANDLER_NOEC(th_irq8, 40)		;
	TRAPHANDLER_NOEC(th_irq9, 41)		;
	TRAPHANDLER_NOEC(th_irq10, 42)		;
	TRAPHANDLER_NOEC(th_irq11, 43)		;
	TRAPHANDLER_NOEC(th_irq12, 44)		;
	TRAPHANDLER_NOEC(th_irq13, 45)		;
	TRAPHANDLER_NOEC(th_irq14, 46)		;
	TRAPHANDLER_NOEC(th_irq15, 47)		;
/*
 * Lab 2: Your code here for _alltraps
 */
_alltraps:
	/* Start pushing Trapframe (finishing what processor started) */
	/* addl	$-0x02, %esp	; */
	pushw 	$0x0		;
	pushw	%ds		;
	/* addl	$-0x02, %esp	; */
	pushw	$0x0		;
	pushw	%es		;
	/* Push current processor registers (in reverse order) */
	/* We could do all of these:
	 *	pushl	%eax		;
	 *	pushl	%ecx		;
	 *	pushl	%edx		;
	 *	pushl	%ebx		;
	 *	pushl	%esp		;
	 *	pushl	%ebp		;
	 *	pushl	%esi		;
	 *	pushl	%edi		;
	 * or just one of these: */
	pushal			;
	/* Set up segment registers */
	pushw	$GD_KD		;
	popw	%es		;
	pushw	$GD_KD		;
	popw	%ds		;
	/* Push a pointer to the Trapframe onto the stack */
	pushl	%esp		;
	/* Call our C trap handler */
	call	trap		;
_aftertrap:	/* breakpoint */
	/* Restore process state */
	popl	%esp
	/* Again, we could do all of these:
	 *	popl	%edi		;
	 *	popl	%esi		;
	 *	popl	%ebp		;
	 *	popl	%esp		;
	 *	popl	%ebx		;
	 *	popl	%edx		;
	 *	popl	%ecx		;
	 *	popl	%eax		;
	 * or just one of these: */
	popal			;
	/* Restore the segment registers */
	popw	%es		;
	addl	$0x02, %esp	;
	popw	%ds		;
	addl	$0x02, %esp	;
	/* Clean up the old processor state
	 * Remember processor pushed:
	 * 	old EFLAGS
	 *	0x0000 | old CS
	 *	old EIP
	 *	error code (or we did if the processor didn't)
	 * We pushed:
	 *	interupt number
	 * IRET will remove the EFLAGS, CS, and EIP,
	 *   but we have to take care of the rest */
	addl	$0x8, %esp	;
	iret			;
