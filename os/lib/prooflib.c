#include <inc/prooflib.h>
#include <inc/mm.h>
#include <inc/env.h>
#include <inc/lib.h>

// Constructor
Proof proof_signed(Formula goal) {
  Proof p = (Proof) malloc(sizeof(struct proof));
  if (p == NULL)
    return p;

  p->type = SIGNED_R;
  p->r.signed_r.goal = formula_cp(goal);
  if (p->r.signed_r.goal == NULL)
    goto freep;

  return p;

freep: free(p);
  return NULL;
}

Proof proof_confirms(Formula goal) {
  Proof p = (Proof) malloc(sizeof(struct proof));
  if (p == NULL)
    return p;

  p->type = CONFIRMS_R;
  p->r.confirms_r.goal = formula_cp(goal);
  if (p->r.confirms_r.goal == NULL)
    goto freep;

  return p;

freep: free(p);
  return NULL;
}

Proof proof_assump(Formula goal) {
  Proof p = (Proof) malloc(sizeof(struct proof));
  if (p == NULL)
    return p;

  p->type = ASSUMP_R;
  p->r.assump_r.goal = formula_cp(goal);
  if (p->r.assump_r.goal == NULL)
    goto freep;

  return p;

freep: free(p);
  return NULL;
}

Proof proof_tauto(Formula goal, Proof proof) {
  Proof p = (Proof) malloc(sizeof(struct proof));
  if (p == NULL)
    return p;

  p->type = TAUTO_R;
  p->r.tauto_r.goal = formula_cp(goal);
  if (p->r.tauto_r.goal == NULL)
    goto freep;

  p->r.tauto_r.proof = proof_cp(proof);
  if (p->r.tauto_r.proof == NULL)
    goto freegoal;

  return p;

freegoal: free(p->r.tauto_r.goal);
freep: free(p);
  return NULL;
}

Proof proof_weaken_impl(Formula goal, Proof proof) {
  Proof p = (Proof) malloc(sizeof(struct proof));
  if (p == NULL)
    return p;

  p->type = WEAKEN_IMPL_R;
  p->r.weaken_impl_r.goal = formula_cp(goal);
  if (p->r.weaken_impl_r.goal == NULL)
    goto freep;

  p->r.weaken_impl_r.proof = proof_cp(proof);
  if (p->r.weaken_impl_r.proof == NULL)
    goto freegoal;

  return p;

freegoal: free(p->r.weaken_impl_r.goal);
freep: free(p);
  return NULL;
}

Proof proof_impl(Formula goal, Proof proof1, Proof proof2) {
  Proof p = (Proof) malloc(sizeof(struct proof));
  if (p == NULL)
    return p;

  p->type = IMPL_R;
  p->r.impl_r.goal = formula_cp(goal);
  if (p->r.impl_r.goal == NULL)
    goto freep;

  p->r.impl_r.pf1 = proof_cp(proof1);
  if (p->r.impl_r.pf1 == NULL)
    goto freegoal;

  p->r.impl_r.pf2 = proof_cp(proof2);
  if (p->r.impl_r.pf2 == NULL)
    goto freeproof1;

  return p;

freeproof1: free(p->r.impl_r.pf1);
freegoal: free(p->r.impl_r.goal);
freep: free(p);
  return NULL;
}

Proof proof_says_confirms(Formula goal, Proof proof1, Proof proof2) {
  Proof p = (Proof) malloc(sizeof(struct proof));
  if (p == NULL)
    return p;

  p->type = SAYS_CONFIRMS_R;
  p->r.says_confirms_r.goal = formula_cp(goal);
  if (p->r.says_confirms_r.goal == NULL)
    goto freep;

  p->r.says_confirms_r.pf1 = proof_cp(proof1);
  if (p->r.says_confirms_r.pf1 == NULL)
    goto freegoal;

  p->r.says_confirms_r.pf2 = proof_cp(proof2);
  if (p->r.says_confirms_r.pf2 == NULL)
    goto freeproof1;

  return p;

freeproof1: free(p->r.says_confirms_r.pf1);
freegoal: free(p->r.says_confirms_r.goal);
freep: free(p);
  return NULL;
}

Proof proof_says_signed(Formula goal, Proof proof1, Proof proof2) {
  Proof p = (Proof) malloc(sizeof(struct proof));
  if (p == NULL)
    return p;

  p->type = SAYS_SIGNED_R;
  p->r.says_signed_r.goal = formula_cp(goal);
  if (p->r.says_signed_r.goal == NULL)
    goto freep;

  p->r.says_signed_r.pf1 = proof_cp(proof1);
  if (p->r.says_signed_r.pf1 == NULL)
    goto freegoal;

  p->r.says_signed_r.pf2 = proof_cp(proof2);
  if (p->r.says_signed_r.pf2 == NULL)
    goto freeproof1;

  return p;

freeproof1: free(p->r.says_signed_r.pf1);
freegoal: free(p->r.says_signed_r.goal);
freep: free(p);
  return NULL;
}

Proof proof_says_says(Formula goal, Proof proof1, Proof proof2) {
  Proof p = (Proof) malloc(sizeof(struct proof));
  if (p == NULL)
    return p;

  p->type = SAYS_SAYS_R;
  p->r.says_says_r.goal = formula_cp(goal);
  if (p->r.says_says_r.goal == NULL)
    goto freep;

  p->r.says_says_r.pf1 = proof_cp(proof1);
  if (p->r.says_says_r.pf1 == NULL)
    goto freegoal;

  p->r.says_says_r.pf2 = proof_cp(proof2);
  if (p->r.says_says_r.pf2 == NULL)
    goto freeproof1;

  return p;

freeproof1: free(p->r.says_says_r.pf1);
freegoal: free(p->r.says_says_r.goal);
freep: free(p);
  return NULL;
}

Proof proof_says_spec(Formula goal, Pcpl pcpl, Proof proof1, Proof proof2) {
  Proof p = (Proof) malloc(sizeof(struct proof));
  if (p == NULL)
    return p;

  p->type = SAYS_SPEC_R;
  p->r.says_spec_r.goal = formula_cp(goal);
  if (p->r.says_spec_r.goal == NULL)
    goto freep;

  p->r.says_spec_r.p = pcpl;

  p->r.says_spec_r.pf1 = proof_cp(proof1);
  if (p->r.says_spec_r.pf1 == NULL)
    goto freegoal;

  p->r.says_spec_r.pf2 = proof_cp(proof2);
  if (p->r.says_spec_r.pf2 == NULL)
    goto freeproof1;

  return p;

freeproof1: free(p->r.says_says_r.pf1);
freegoal: free(p->r.says_says_r.goal);
freep: free(p);
  return NULL;
}

// Helper proof constructor functions
Proof signed_proof(Pcpl sayer, Formula f) {
  Principal p = principal_pcpl(sayer);
  Formula goal = formula_signed(p, f);
  if((envid_t)sayer == thisenv->env_id)
    sys_sign_formula(f);

  Proof proof = proof_signed(goal);

  formula_free(goal);
  free(p);
  return proof;
}

Proof confirms_proof(Pcpl confirmer, Formula f) {
  Principal p = principal_pcpl(confirmer);
  Formula goal = formula_confirms(p, f);
  Proof proof = proof_confirms(goal);

  formula_free(goal);
  free(p);
  return proof;
}

Proof says_from_assump(Pcpl sayer, Formula f) {
  Principal p = principal_pcpl(sayer);
  Formula goal = formula_says(p, f);
  Proof assumpp = proof_assump(f);
  Proof tauto = proof_tauto(goal, assumpp);

  proof_free(assumpp);
  formula_free(goal);
  free(p);
  return tauto;
}

Proof says_from_signed(Pcpl sayer, Formula f) {
  Principal p = principal_pcpl(sayer);
  Formula goal = formula_says(p, f);
  Proof signedp = signed_proof(sayer, f);
  Proof assumpp = says_from_assump(sayer, f);
  Proof sayssigned = proof_says_signed(goal, signedp, assumpp);

  proof_free(assumpp);
  proof_free(signedp);
  formula_free(goal);
  free(p);
  return sayssigned;
}

Proof says_from_confirms(Pcpl confirmer, Formula f) {
  Principal p = principal_pcpl(confirmer);
  Formula goal = formula_says(p, f);
  Proof confirmsp = confirms_proof(confirmer, f);
  Proof assumpp = says_from_assump(confirmer, f);
  Proof saysconfirms = proof_says_confirms(goal, confirmsp, assumpp);

  proof_free(assumpp);
  proof_free(confirmsp);
  formula_free(goal);
  free(p);
  return saysconfirms;
}

Formula approve(Pcpl pcpl, Predicate pred) {
  Principal p = principal_pcpl(pcpl);
  Formula a = formula_pred(pred, p);

  free(p);
  return a;
}

Proof approval_from_signed(Pcpl approver, Predicate pred, Pcpl pcpl) {
  Formula a = approve(pcpl, pred);
  Proof p = says_from_signed(approver, a);

  formula_free(a);
  return p;
}

Formula delegate(Pcpl pcpl, Predicate pred) {
  Principal v = principal_var(0);
  Principal p = principal_pcpl(pcpl);
  Formula predf = formula_pred(pred, v);
  Formula says = formula_says(p, predf);
  Formula impl = formula_impl(says, predf);
  Formula abs = formula_abs(impl);

  formula_free(impl);
  formula_free(says);
  formula_free(predf);
  free(p);
  free(v);
  return abs;
}

Formula delegate_signed(Pcpl a, Pcpl b, Predicate p) {
  Formula d = delegate(b, p);
  Principal ap = principal_pcpl(a);
  Formula signedf = formula_signed(ap, d);
  free(ap);
  formula_free(d);
  return signedf;
}

Proof delegate_from_signed(Pcpl a, Pcpl b, Predicate p) {
  Formula d = delegate(b, p);
  Proof pf = says_from_signed(a, d);
  free(d);
  return pf;
}

Proof use_delegation(Pcpl a, Pcpl b, Pcpl c, Predicate p, Proof dpf, Proof apf) {
  Principal ap = principal_pcpl(a);
  Principal bp = principal_pcpl(b);
  Principal cp = principal_pcpl(c);
  Formula approval = approve(c, p);
  Formula goal = formula_says(ap, approval);
  Formula bsays = formula_says(bp, approval);
  Formula delegation = formula_impl(bsays, approval);
  Proof assump = proof_assump(delegation);
  Proof impl = proof_impl(approval, apf, assump);
  Proof rightside = proof_tauto(goal, impl);
  Proof final = proof_says_spec(goal, c, dpf, rightside);

  free(ap);
  free(bp);
  free(cp);
  formula_free(approval);
  formula_free(goal);
  formula_free(bsays);
  formula_free(delegation);
  proof_free(assump);
  proof_free(impl);
  proof_free(rightside);
  return final;
}


