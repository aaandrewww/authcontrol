#include <inc/stdio.h>
#include <inc/string.h>
#include <inc/proof.h>
#include <inc/formula.h>
#include <inc/context.h>
#include <inc/mm.h>

// Check that Proof, pf, is a valid proof of Formula, f, given Context, c
bool proof_check_lib(Formula f, Proof pf, Context c) {
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
    return true; // only for the lib version
  case CONFIRMS_R:
    if (f->type != CONFIRMS_F)
      goto invalid_proof;
    return true; // only for the lib version
  case TAUTO_R:
    if (f->type != SAYS_F)
      goto invalid_proof;
    return proof_check_lib(f->form.says_f.formula, pf->r.tauto_r.proof, c);
  case WEAKEN_IMPL_R:
    if (f->type != IMPL_F)
      goto invalid_proof;
    // Check the proof with f1 added to the context
    if (!c)
      c = context_alloc(10);
    push(c, f->form.impl_f.formula2);
    b = proof_check_lib(f->form.impl_f.formula2, pf->r.weaken_impl_r.proof, c);
    pop(c);
    return b;
  case IMPL_R:
    p1 = pf->r.impl_r.pf1;
    pg1 = proof_goal(p1);

    // Check that we have a valid proof of the implicant
    if (!proof_check_lib(pg1, p1, c))
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
    return proof_check_lib(impl, p2, c);
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
    if (!proof_check_lib(pg1, p1, c))
      return false;

    // Check the proof in the context with f1 added
    if (!c)
      c = context_alloc(10);
    push(c, pg1->form.confirms_f.formula);
    b = proof_check_lib(f, p2, c);
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
    if (!proof_check_lib(pg1, p1, c))
      return false;

    // Check the proof in the context with f1 added
    if (!c)
      c = context_alloc(10);
    push(c, pg1->form.signed_f.formula);
    b = proof_check_lib(f, p2, c);
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
    if (!proof_check_lib(pg1, p1, c))
      return false;

    // Check the proof in the context with f1 added
    if (!c)
      c = context_alloc(10);
    push(c, pg1->form.says_f.formula);
    b = proof_check_lib(f, p2, c);
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
    if (!proof_check_lib(pg1, p1, c))
      return false;

    // Check the proof with f1[p/0] added to the context
    pcpl = pf->r.says_spec_r.p;
    f1 = pg1->form.says_f.formula->form.abs_f.formula;
    f1_subst = formula_subst(f1, 0, pcpl);
    if (!c)
      c = context_alloc(10);
    push(c, f1_subst);
    b = proof_check_lib(f, p2, c);
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

// Debugging wrapper around formula_eq that prints out a message when fails
bool formula_goal_check(Formula formula, Formula goal, Proof pf) {
  if (!formula_eq(formula, goal)) {
    cprintf("ERROR: formula does not match goal \n");
    cprintf("Formula:\n");
    formula_print(formula);
    cprintf("\n");
    cprintf("Proof:\n");
    proof_print(pf);
    cprintf("\n");
    return false;
  }
  return true;
}

void signed_r_print(Signed_r signed_r) {
  cprintf("\\trfrac[\\;signed]{\\rtcheck}{");
  formula_print(signed_r.goal);
  cprintf("}");
}

void confirms_r_print(Confirms_r confirms_r) {
  cprintf("\\trfrac[\\;confirms]{\\rtcheck}{");
  formula_print(confirms_r.goal);
  cprintf("}");
}

void assump_r_print(Assump_r assump_r) {
  cprintf("\\trfrac[\\;init]{\\rtcheck}{");
  formula_print(assump_r.goal);
  cprintf("}");
}

void tauto_r_print(Tauto_r tauto_r) {
  cprintf("\\trfrac[\\;tauto]{");
  proof_print(tauto_r.proof);
  cprintf("}{");
  formula_print(tauto_r.goal);
  cprintf("}");
}

void weaken_impl_r_print(Weaken_Impl_r weaken_impl_r) {
  cprintf("\\trfrac[\\;weaken impl]{");
  proof_print(weaken_impl_r.proof);
  cprintf("}{");
  formula_print(weaken_impl_r.goal);
  cprintf("}");
}

void impl_r_print(Impl_r impl_r) {
  cprintf("\\trfrac[\\;impl]{");
  proof_print(impl_r.pf1);
  cprintf(" \\quad ");
  proof_print(impl_r.pf2);
  cprintf("}{");
  formula_print(impl_r.goal);
  cprintf("}");
}

void says_confirms_r_print(Says_Confirms_r says_confirms_r) {
  cprintf("\\trfrac[\\;conf]{");
  proof_print(says_confirms_r.pf1);
  cprintf(" \\quad ");
  proof_print(says_confirms_r.pf2);
  cprintf("}{");
  formula_print(says_confirms_r.goal);
  cprintf("}");
}

void says_signed_r_print(Says_Signed_r says_signed_r) {
  cprintf("\\trfrac[\\;sign]{");
  proof_print(says_signed_r.pf1);
  cprintf(" \\quad ");
  proof_print(says_signed_r.pf2);
  cprintf("}{");
  formula_print(says_signed_r.goal);
  cprintf("}");
}

void says_says_r_print(Says_Says_r says_says_r) {
  cprintf("\\trfrac[\\;says]{");
  proof_print(says_says_r.pf1);
  cprintf(" \\quad ");
  proof_print(says_says_r.pf2);
  cprintf("}{");
  formula_print(says_says_r.goal);
  cprintf("}");
}

void says_spec_r_print(Says_Spec_r says_spec_r) {
  cprintf("\\trfrac[\\;spec]{");
  proof_print(says_spec_r.pf1);
  cprintf(" \\quad %u \\quad", says_spec_r.p);
  proof_print(says_spec_r.pf2);
  cprintf("}{");
  formula_print(says_spec_r.goal);
  cprintf("}");
}

void proof_print(Proof pf) {
  switch (pf->type) {
  case SIGNED_R: signed_r_print(pf->r.signed_r); return;
  case CONFIRMS_R: confirms_r_print(pf->r.confirms_r); return;
  case ASSUMP_R: assump_r_print(pf->r.assump_r); return;
  case TAUTO_R: tauto_r_print(pf->r.tauto_r); return;
  case WEAKEN_IMPL_R: weaken_impl_r_print(pf->r.weaken_impl_r); return;
  case IMPL_R: impl_r_print(pf->r.impl_r); return;
  case SAYS_CONFIRMS_R: says_confirms_r_print(pf->r.says_confirms_r); return;
  case SAYS_SIGNED_R: says_signed_r_print(pf->r.says_signed_r); return;
  case SAYS_SAYS_R: says_says_r_print(pf->r.says_says_r); return;
  case SAYS_SPEC_R: says_spec_r_print(pf->r.says_spec_r); return;
  default: cprintf("PROOF TYPE UNDEFINED"); return;
  }
}

Proof proof_cp(Proof pf) {
	Proof newr = (Proof) malloc(sizeof(struct proof));
  if (newr == NULL)
    return newr;
  newr->type = pf->type;

  switch (pf->type) {
  case SIGNED_R:
    newr->r.signed_r.goal = formula_cp(pf->r.signed_r.goal);
    if (newr->r.signed_r.goal == NULL)
      goto freenewr;
    return newr;
  case CONFIRMS_R:
    newr->r.confirms_r.goal = formula_cp(pf->r.confirms_r.goal);
    if (newr->r.confirms_r.goal == NULL)
      goto freenewr;
    return newr;
  case ASSUMP_R:
    newr->r.assump_r.goal = formula_cp(pf->r.assump_r.goal);
    if (newr->r.assump_r.goal == NULL)
      goto freenewr;
    return newr;
  case TAUTO_R:
    newr->r.tauto_r.goal = formula_cp(pf->r.tauto_r.goal);
    if (newr->r.tauto_r.goal == NULL)
      goto freenewr;

    newr->r.tauto_r.proof = proof_cp(pf->r.tauto_r.proof);
    if (newr->r.tauto_r.proof == NULL) {
      free(newr->r.tauto_r.goal);
      goto freenewr;
    }
    return newr;
  case WEAKEN_IMPL_R:
    newr->r.weaken_impl_r.goal = formula_cp(pf->r.weaken_impl_r.goal);
    if (newr->r.weaken_impl_r.goal == NULL)
      goto freenewr;

    newr->r.weaken_impl_r.proof = proof_cp(pf->r.weaken_impl_r.proof);
    if (newr->r.weaken_impl_r.proof == NULL) {
      free(newr->r.weaken_impl_r.goal);
      goto freenewr;
    }
    return newr;
  case IMPL_R:
    newr->r.impl_r.goal = formula_cp(pf->r.impl_r.goal);
    if (newr->r.impl_r.goal == NULL)
      goto freenewr;

    newr->r.impl_r.pf1 = proof_cp(pf->r.impl_r.pf1);
    if (newr->r.impl_r.pf1 == NULL) {
      free(newr->r.impl_r.goal);
      goto freenewr;
    }

    newr->r.impl_r.pf2 = proof_cp(pf->r.impl_r.pf2);
    if (newr->r.impl_r.pf2 == NULL) {
      free(newr->r.impl_r.pf1);
      free(newr->r.impl_r.goal);
      goto freenewr;
    }
    return newr;
  case SAYS_CONFIRMS_R:
    newr->r.says_confirms_r.goal = formula_cp(pf->r.says_confirms_r.goal);
    if (newr->r.says_confirms_r.goal == NULL)
      goto freenewr;

    newr->r.impl_r.pf1 = proof_cp(pf->r.impl_r.pf1);
    if (newr->r.impl_r.pf1 == NULL) {
      free(newr->r.impl_r.goal);
      goto freenewr;
    }

    newr->r.impl_r.pf2 = proof_cp(pf->r.impl_r.pf2);
    if (newr->r.impl_r.pf2 == NULL) {
      free(newr->r.impl_r.pf1);
      free(newr->r.impl_r.goal);
      goto freenewr;
    }
    return newr;
  case SAYS_SIGNED_R:
    newr->r.says_signed_r.goal = formula_cp(pf->r.says_signed_r.goal);
    if (newr->r.says_signed_r.goal == NULL)
      goto freenewr;

    newr->r.says_signed_r.pf1 = proof_cp(pf->r.says_signed_r.pf1);
    if (newr->r.says_signed_r.pf1 == NULL) {
      free(newr->r.says_signed_r.goal);
      goto freenewr;
    }

    newr->r.says_signed_r.pf2 = proof_cp(pf->r.says_signed_r.pf2);
    if (newr->r.says_signed_r.pf2 == NULL) {
      free(newr->r.says_signed_r.pf1);
      free(newr->r.says_signed_r.goal);
      goto freenewr;
    }
    return newr;
  case SAYS_SAYS_R:
    newr->r.says_says_r.goal = formula_cp(pf->r.says_says_r.goal);
    if (newr->r.says_says_r.goal == NULL)
      goto freenewr;

    newr->r.says_says_r.pf1 = proof_cp(pf->r.says_says_r.pf1);
    if (newr->r.says_says_r.pf1 == NULL) {
      free(newr->r.says_says_r.goal);
      goto freenewr;
    }

    newr->r.says_says_r.pf2 = proof_cp(pf->r.says_says_r.pf2);
    if (newr->r.says_says_r.pf2 == NULL) {
      free(newr->r.says_says_r.pf1);
      free(newr->r.says_says_r.goal);
      goto freenewr;
    }
    return newr;
  case SAYS_SPEC_R:
    newr->r.says_spec_r.goal = formula_cp(pf->r.says_spec_r.goal);
    if (newr->r.says_spec_r.goal == NULL)
      goto freenewr;

    newr->r.says_spec_r.p = pf->r.says_spec_r.p;

    newr->r.says_spec_r.pf1 = proof_cp(pf->r.says_spec_r.pf1);
    if (newr->r.says_spec_r.pf1 == NULL) {
      free(newr->r.says_spec_r.goal);
      goto freenewr;
    }

    newr->r.says_spec_r.pf2 = proof_cp(pf->r.says_spec_r.pf2);
    if (newr->r.says_spec_r.pf2 == NULL) {
      free(newr->r.says_spec_r.pf1);
      free(newr->r.says_spec_r.goal);
      goto freenewr;
    }
    return newr;
  default:
    return NULL;
  }

freenewr: free(newr);
  return NULL;
}

bool proof_eq(Proof pf1, Proof pf2) {
  if (pf1->type != pf2->type)
    return false;

  switch (pf1->type) {
  case SIGNED_R:
    return formula_eq(pf1->r.signed_r.goal, pf2->r.signed_r.goal);
  case CONFIRMS_R:
    return formula_eq(pf1->r.confirms_r.goal, pf2->r.confirms_r.goal);
  case ASSUMP_R:
    return formula_eq(pf1->r.confirms_r.goal, pf2->r.confirms_r.goal);
  case TAUTO_R:
    if (!formula_eq(pf1->r.tauto_r.goal, pf2->r.tauto_r.goal))
      return false;
    return proof_eq(pf1->r.tauto_r.proof, pf2->r.tauto_r.proof);
  case WEAKEN_IMPL_R:
    if (!formula_eq(pf1->r.weaken_impl_r.goal, pf2->r.weaken_impl_r.goal))
      return false;
    return proof_eq(pf1->r.weaken_impl_r.proof, pf2->r.weaken_impl_r.proof);
  case IMPL_R:
    if (!formula_eq(pf1->r.impl_r.goal, pf2->r.impl_r.goal))
      return false;
    if (!proof_eq(pf1->r.impl_r.pf1, pf2->r.impl_r.pf1))
      return false;
    return proof_eq(pf1->r.impl_r.pf2, pf2->r.impl_r.pf2);
  case SAYS_CONFIRMS_R:
    if (!formula_eq(pf1->r.says_confirms_r.goal, pf2->r.says_confirms_r.goal))
      return false;
    if (!proof_eq(pf1->r.says_confirms_r.pf1, pf2->r.says_confirms_r.pf1))
      return false;
    return proof_eq(pf1->r.says_confirms_r.pf2, pf2->r.says_confirms_r.pf2);
  case SAYS_SIGNED_R:
    if (!formula_eq(pf1->r.says_signed_r.goal, pf2->r.says_signed_r.goal))
      return false;
    if (!proof_eq(pf1->r.says_signed_r.pf1, pf2->r.says_signed_r.pf1))
      return false;
    return proof_eq(pf1->r.says_signed_r.pf2, pf2->r.says_signed_r.pf2);
  case SAYS_SAYS_R:
    if (!formula_eq(pf1->r.says_says_r.goal, pf2->r.says_says_r.goal))
      return false;
    if (!proof_eq(pf1->r.says_says_r.pf1, pf2->r.says_says_r.pf1))
      return false;
    return proof_eq(pf1->r.says_says_r.pf2, pf2->r.says_says_r.pf2);
  case SAYS_SPEC_R:
    if (pf1->r.says_spec_r.p != pf2->r.says_spec_r.p)
      return false;
    if (!formula_eq(pf1->r.says_spec_r.goal, pf2->r.says_spec_r.goal))
      return false;
    if (!proof_eq(pf1->r.says_spec_r.pf1, pf2->r.says_spec_r.pf1))
      return false;
    return proof_eq(pf1->r.says_spec_r.pf2, pf2->r.says_spec_r.pf2);
  }
  return false;
}

Formula proof_goal(Proof pf) {
  switch (pf->type) {
  case SIGNED_R: return formula_cp(pf->r.signed_r.goal);
  case CONFIRMS_R: return formula_cp(pf->r.confirms_r.goal);
  case ASSUMP_R: return formula_cp(pf->r.assump_r.goal);
  case TAUTO_R: return formula_cp(pf->r.tauto_r.goal);
  case WEAKEN_IMPL_R: return formula_cp(pf->r.weaken_impl_r.goal);
  case IMPL_R: return formula_cp(pf->r.impl_r.goal);
  case SAYS_CONFIRMS_R: return formula_cp(pf->r.says_confirms_r.goal);
  case SAYS_SIGNED_R: return formula_cp(pf->r.says_signed_r.goal);
  case SAYS_SAYS_R: return formula_cp(pf->r.says_says_r.goal);
  case SAYS_SPEC_R: return formula_cp(pf->r.says_spec_r.goal);
  default: return NULL;
  }
}

void proof_free(Proof p) {
  switch (p->type) {
  case SIGNED_R:
    formula_free(p->r.signed_r.goal);
    break;
  case CONFIRMS_R:
    formula_free(p->r.assump_r.goal);
    break;
  case ASSUMP_R:
    formula_free(p->r.assump_r.goal);
    break;
  case TAUTO_R:
    formula_free(p->r.tauto_r.goal);
    proof_free(p->r.tauto_r.proof);
    break;
  case WEAKEN_IMPL_R:
    formula_free(p->r.weaken_impl_r.goal);
    proof_free(p->r.weaken_impl_r.proof);
    break;
  case IMPL_R:
    formula_free(p->r.impl_r.goal);
    proof_free(p->r.impl_r.pf1);
    proof_free(p->r.impl_r.pf2);
    break;
  case SAYS_CONFIRMS_R:
    formula_free(p->r.says_confirms_r.goal);
    proof_free(p->r.says_confirms_r.pf1);
    proof_free(p->r.says_confirms_r.pf2);
    break;
  case SAYS_SIGNED_R:
    formula_free(p->r.says_signed_r.goal);
    proof_free(p->r.says_signed_r.pf1);
    proof_free(p->r.says_signed_r.pf2);
    break;
  case SAYS_SAYS_R:
    formula_free(p->r.says_says_r.goal);
    proof_free(p->r.says_says_r.pf1);
    proof_free(p->r.says_says_r.pf2);
    break;
  case SAYS_SPEC_R:
    formula_free(p->r.says_spec_r.goal);
    proof_free(p->r.says_spec_r.pf1);
    proof_free(p->r.says_spec_r.pf2);
    break;
  }
  free(p);
}
