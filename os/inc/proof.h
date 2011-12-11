#ifndef PROOF_H
#define PROOF_H

#include <inc/formula.h>
#include <inc/context.h>

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

enum rule_type {
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

struct proof {
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
bool proof_eq(Proof pf1, Proof pf2);
Proof proof_cp(Proof pf);
Proof proof_cp_to(Proof pf, void *addr);
Formula proof_goal(Proof pf);
bool proof_check(Formula f, Proof pf, Context c);
void proof_free(Proof pf);

// Constructors
Proof proof_signed(Formula goal);
Proof proof_confirms(Formula goal);
Proof proof_assump(Formula goal);
Proof proof_tauto(Formula goal, Proof proof);
Proof proof_weaken_impl(Formula goal, Proof proof);
Proof proof_impl(Formula goal, Proof proof1, Proof proof2);
Proof proof_says_confirms(Formula goal, Proof proof1, Proof proof2);
Proof proof_says_signed(Formula goal, Proof proof1, Proof proof2);
Proof proof_says_says(Formula goal, Proof proof1, Proof proof2);
Proof proof_says_spec(Formula goal, Pcpl p, Proof proof1, Proof proof2);

Proof signed_proof(Pcpl sayer, Formula f);
Proof says_from_assump(Pcpl sayer, Formula f);
Proof says_from_signed(Pcpl sayer, Formula f);
Proof says_from_confirms(Pcpl sayer, Formula f);
Formula approve(Pcpl pcpl, Predicate pred);
Proof approval_from_signed(Pcpl approver, Predicate pred, Pcpl pcpl);
Formula delegate(Pcpl pcpl, Predicate pred);
Formula delegate_signed(Pcpl a, Pcpl b, Predicate p);
Proof delegate_from_signed(Pcpl a, Pcpl b, Predicate p);
Proof use_delegation(Pcpl a, Pcpl b, Pcpl c, Predicate p, Proof dpf, Proof apf);

#endif
