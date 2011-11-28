#ifndef PROOF_H
#define PROOF_H

#include <formula.h>

typedef struct proof* Proof;
typedef struct signed_rule Signed_r;
typedef struct confirms_rule Confirms_r;
typedef struct assump_rule Assump_r;
typedef struct tauto_rule Tauto_r;
typedef struct weaken_impl_rule Weaken_Impl_r;
typedef struct impl_rule Impl_r;
typedef struct says_confirms_rule Says_Confirms_r;
typedef struct says_signed_rule Says_Signed_r;
typedef struct says_says_rule Says_Says_r;
typedef struct says_spec_rule Says_Spec_r;

enum rule_type{
	SIGNED_R,
	CONFIRMS_R,
	ASSUMP_R,
	TAUTO_R,
	WEAKEN_IMPL_R,
	IMPL_R,
	SAYS_CONFIRMS_R,
	SAYS_SIGNED_R,
	SAYS_SAYS_R,
	SAYS_SPEC_R
};

struct signed_rule {
	// Signed_f
	Formula goal;
};

struct confirms_rule {
	// Confirms_f
	Formula goal;
};

struct assump_rule {
	// Assumption
	Formula goal;
};

struct tauto_rule {
	// Says_f a f
	Formula goal;
	// Proof of f
	Proof proof;
};

struct weaken_impl_rule {
	// Impl_f f1 f2
	Formula goal;
	// Proof of f2 (with f1 in context)
	Proof proof;
};

struct impl_rule {
	// f2
	Formula goal;
	// Proof of f1
	Proof pf1;
	// Proof of Impl_f f1 f2
	Proof pf2;
};

struct says_confirms_rule {
	// Says_f a f2
	Formula goal;
	// Proof of Confirms_f a f1
	Proof pf1;
	// Proof of Says_f a f2 (with f1 in context)
	Proof pf2;
};

struct says_signed_rule {
	// Says_f a f2
	Formula goal;
	// Proof of Signed_f a f1
	Proof pf1;
	// Proof of Says_f a f2 (with f1 in context)
	Proof pf2;
};

struct says_says_rule {
	// Says_f a f2
	Formula goal;
	// Proof of Says_f a f1
	Proof pf1;
	// Proof of Says_f a f2 (with f1 in context)
	Proof pf2;
};

struct says_spec_rule {
	// Says a f2
	Formula goal;
	// Principal p (already substituted)
	Pcpl p;
	// Proof of Says a Abs_f f1
	Proof pf1;
	// Proof of Says a f2 (with formula_subst(f1 0 p) in context)
	Proof pf2;
};

struct proof{
	enum rule_type type;
	union {
		Signed_r signed_r;
		Confirms_r confirms_r;
		Assump_r assump_r;
		Tauto_r tauto_r;
		Weaken_Impl_r weaken_impl_r;
		Impl_r impl_r;
		Says_Confirms_r says_confirms_r;
		Says_Signed_r says_signed_r;
		Says_Says_r says_says_r;
		Says_Spec_r says_spec_r;
	} r;
};

void proof_print(Proof pf);
bool proof_check(Formula f, Proof pf);
Proof proof_cp(Proof pf);
Formula proof_goal(Proof pf);

#endif
