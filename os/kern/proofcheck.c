#include <kern/proofcheck.h>
#include <kern/pmap.h>
#include <kern/env.h>
#include <inc/proof.h>
#include <inc/stdio.h>
#include <inc/mm.h>
#include <inc/x86.h>

bool check_confirms(Confirms_f f){
  // If the principal has not been substituted we cannot check so return false
  if(f.principal->type != PCPL)
    return false;

  envid_t envid = f.principal->prin.pcpl;

  const volatile struct Env *env = &envs[ENVX(envid)];

  if (env->confirms_upcall == 0) return false;

  lcr3(PADDR(env->env_pgdir));

  Heap *oldHeap = set_heap(env->confirms_heap);
  Formula formula = formula_cp(f.formula);
  if (formula == NULL) {
    set_heap(oldHeap);
    lcr3(PADDR(curenv->env_pgdir));
    return false;
  }
  bool result = ((bool (*)(Formula)) (env->confirms_upcall))(formula);
  set_heap(oldHeap);
  lcr3(PADDR(curenv->env_pgdir));

  return result;
}

// Check that Proof, pf, is a valid proof of Formula, f, given Context, c
bool proof_check(Formula f, Proof pf, Context c) {
  Proof p1;
  Proof p2;
  Formula pg1;
  Formula f1, f1_subst, f3, f4, impl;
  Pcpl pcpl;
  bool b;

  // Check if the formula is the same as the proof goal
  if (!formula_goal_check(f, proof_goal(pf), pf))
    return false;

  switch (pf->type) {
  case SIGNED_R:
    if (f->type != SIGNED_F)
      goto invalid_proof;
    b = member(c,f);
    if(!b){
      cprintf("Signed formula: \n");
      formula_print(f);
      cprintf("\n not in context:\n");
      context_print(c);
      cprintf("\n");
    }
    return b;
  case CONFIRMS_R:
    if (f->type != CONFIRMS_F)
      goto invalid_proof;
    b = check_confirms(f->form.confirms_f); // only for the lib version
    if(!b){
      cprintf("Confirmation failed\n");
      goto invalid_proof;
    }
    return true;
  case TAUTO_R:
    if (f->type != SAYS_F)
      goto invalid_proof;
    return proof_check(f->form.says_f.formula, pf->r.tauto_r.proof, c);
  case WEAKEN_IMPL_R:
    if (f->type != IMPL_F)
      goto invalid_proof;
    // Check the proof with f1 added to the context
    if (!c)
      c = context_alloc(10);
    push(c, f->form.impl_f.formula2);
    b = proof_check(f->form.impl_f.formula2, pf->r.weaken_impl_r.proof, c);
    pop(c);
    return b;
  case IMPL_R:
    p1 = pf->r.impl_r.pf1;
    pg1 = proof_goal(p1);

    // Check that we have a valid proof of the implicant
    if (!proof_check(pg1, p1, c))
      return false;

    // Check that pf2 is a proof of f1->f2
    p2 = pf->r.impl_r.pf2;
    impl = proof_goal(p2);
    if (impl->type != IMPL_F)
      goto invalid_proof;

    // impl = f3->f4
    f3 = impl->form.impl_f.formula1;
    f4 = impl->form.impl_f.formula2;

    // The goal of the first proof is the implicant
    if (!formula_goal_check(f3, pg1, p1))
      goto invalid_proof;

    // The checked formula is the implicand
    if (!formula_eq(f4, f))
      goto invalid_proof;

    // Check the proof of the implication
    return proof_check(impl, p2, c);
  case SAYS_CONFIRMS_R:
    if (f->type != SAYS_F)
      goto invalid_proof;

    p1 = pf->r.says_confirms_r.pf1;
    p2 = pf->r.says_confirms_r.pf2;
    pg1 = proof_goal(p1);
    // The first proof is proof of Confirms
    if (pg1->type != CONFIRMS_F)
      goto invalid_proof;

    // The principal in the Says is the same as the one in Confirms
    if (!principal_eq(f->form.says_f.principal, pg1->form.confirms_f.principal))
      goto invalid_proof;

    // Check that the first proof is valid
    if (!proof_check(pg1, p1, c))
      return false;

    // Check the proof in the context with f1 added
    if (!c)
      c = context_alloc(10);
    push(c, pg1->form.confirms_f.formula);
    b = proof_check(f, p2, c);
    pop(c);
    return b;
  case SAYS_SIGNED_R:
    if (f->type != SAYS_F)
      goto invalid_proof;

    p1 = pf->r.says_signed_r.pf1;
    p2 = pf->r.says_signed_r.pf2;
    pg1 = proof_goal(p1);
    // The first proof is proof of Signed
    if (pg1->type != SIGNED_F)
      goto invalid_proof;

    // The principal in the Says is the same as the one in Signed
    if (!principal_eq(f->form.says_f.principal, pg1->form.signed_f.principal))
      goto invalid_proof;

    // Check that the first proof is valid
    if (!proof_check(pg1, p1, c))
      return false;

    // Check the proof in the context with f1 added
    if (!c)
      c = context_alloc(10);
    push(c, pg1->form.signed_f.formula);
    b = proof_check(f, p2, c);
    pop(c);
    return b;
  case SAYS_SAYS_R:
    if (f->type != SAYS_F)
      goto invalid_proof;

    p1 = pf->r.says_says_r.pf1;
    p2 = pf->r.says_says_r.pf2;
    pg1 = proof_goal(p1);
    // The first proof is proof of Says
    if (pg1->type != SAYS_F)
      goto invalid_proof;

    // The principal in the Says is the same as the one in the other Says
    if (!principal_eq(f->form.says_f.principal, pg1->form.says_f.principal))
      goto invalid_proof;

    // Check that the first proof is valid
    if (!proof_check(pg1, p1, c))
      return false;

    // Check the proof in the context with f1 added
    if (!c)
      c = context_alloc(10);
    push(c, pg1->form.says_f.formula);
    b = proof_check(f, p2, c);
    pop(c);
    return b;
  case SAYS_SPEC_R:
    if (f->type != SAYS_F)
      goto invalid_proof;

    p1 = pf->r.says_spec_r.pf1;
    p2 = pf->r.says_spec_r.pf2;
    pg1 = proof_goal(p1);
    // The first proof is proof of Says
    if (pg1->type != SAYS_F)
      goto invalid_proof;

    // The Formula in Says is an abstraction
    if (pg1->form.says_f.formula->type != ABS_F)
      goto invalid_proof;

    // The principal in the Says is the same as the one in the Says Abstraction
    if (!principal_eq(f->form.says_f.principal, pg1->form.says_f.principal))
      goto invalid_proof;

    // The first proof is valid
    if (!proof_check(pg1, p1, c))
      return false;

    // Check the proof with f1[p/0] added to the context
    pcpl = pf->r.says_spec_r.p;
    f1 = pg1->form.says_f.formula->form.abs_f.formula;
    f1_subst = formula_subst(f1, 0, pcpl);
    if (!c)
      c = context_alloc(10);
    push(c, f1_subst);
    b = proof_check(f, p2, c);
    pop(c);
    return b;

  case ASSUMP_R:
    b = member(c,f);
    if(!b){
      cprintf("Formula: \n");
      formula_print(f);
      cprintf("\n not in context:\n");
      context_print(c);
      cprintf("\n");
    }
    return b;

  default:
    cprintf("PROOF TYPE UNDEFINED IN CHECKER");
    return false;
  }

  invalid_proof: cprintf("ERROR: invalid proof\n");
  cprintf("Formula:\n");
  formula_print(f);
  cprintf("\n");
  cprintf("Proof:\n");
  proof_print(pf);
  cprintf("\n");
  return false;
}
