#include <inc/lib.h>
#include <inc/stdio.h>
#include <inc/string.h>
#include <inc/formula.h>

bool principal_eq(Principal p1, Principal p2) {
  switch (p1->type) {
  case VAR: return ((p2->type == VAR) && (p1->prin.var == p2->prin.var));
  case PCPL: return ((p2->type == PCPL) && (p1->prin.pcpl == p2->prin.pcpl));
  default: return false;
  }
}

Principal principal_cp(Principal p) {
  Principal newp = (Principal) malloc(sizeof(struct principal));
  if (newp == NULL)
    return newp;

  newp->type = p->type;
  newp->prin = p->prin;

  return newp;
}

Principal principal_subst(Principal prin, Var v, Pcpl p) {
	Principal newp = (Principal) principal_cp(prin);
  if (newp == NULL)
    return newp;

  if (newp->type == VAR) {
    if (newp->prin.var == v) {
      newp->type = PCPL;
      newp->prin.pcpl = p;
    } else if (newp->prin.var > v) {
      newp->prin.var = newp->prin.var - 1;
    }
  }

  return newp;
}

void principal_print(Principal prin) {
  switch (prin->type) {
  case VAR: cprintf("v_{%u}", prin->prin.var); return;
  case PCPL: cprintf("%u", prin->prin.pcpl); return;
  default: cprintf("UNDEFINED"); return;
  }
}

void pred_print(Pred_f pred) {
  cprintf("\\pred{%u}{", pred.pred);
  principal_print(pred.principal);
  cprintf("}");
}

void impl_print(Impl_f impl) {
  cprintf("\\imp{");
  formula_print(impl.formula1);
  cprintf("}{");
  formula_print(impl.formula2);
  cprintf("}");
}

void signed_print(Signed_f sign) {
  cprintf("\\sign{");
  principal_print(sign.principal);
  cprintf("}{");
  formula_print(sign.formula);
  cprintf("}");
}

void says_print(Says_f says) {
  cprintf("\\says{");
  principal_print(says.principal);
  cprintf("}{");
  formula_print(says.formula);
  cprintf("}");
}

void confirms_print(Confirms_f conf) {
  cprintf("\\confirms{");
  principal_print(conf.principal);
  cprintf("}{");
  formula_print(conf.formula);
  cprintf("}");
}

void abs_print(Abs_f abs) {
  cprintf("\\abs{");
  formula_print(abs.formula);
  cprintf("}");
}

void formula_print(Formula f) {
  switch (f->type) {
  case PRED_F: pred_print(f->form.pred_f); return;
  case IMPL_F: impl_print(f->form.impl_f);  return;
  case SIGNED_F: signed_print(f->form.signed_f); return;
  case SAYS_F: says_print(f->form.says_f); return;
  case CONFIRMS_F: confirms_print(f->form.confirms_f); return;
  case ABS_F: abs_print(f->form.abs_f); return;
  default: cprintf("FORMULA UNDEFINED"); return;
  }
}

bool pred_eq(Pred_f p1, Formula f) {
  if (f->type != PRED_F)
    return false;
  Pred_f p2 = f->form.pred_f;
  return principal_eq(p1.principal, p2.principal) && (p1.pred == p2.pred);
}

bool impl_eq(Impl_f i1, Formula f) {
  if (f->type != IMPL_F)
    return false;
  Impl_f i2 = f->form.impl_f;
  return formula_eq(i1.formula1, i2.formula1)
      && formula_eq(i1.formula2, i2.formula2);
}

bool signed_eq(Signed_f s1, Formula f) {
  if (f->type != SIGNED_F)
    return false;
  Signed_f s2 = f->form.signed_f;
  return principal_eq(s1.principal, s2.principal)
      && formula_eq(s1.formula, s2.formula);
}

bool says_eq(Says_f s1, Formula f) {
  if (f->type != SAYS_F)
    return false;
  Says_f s2 = f->form.says_f;
  return principal_eq(s1.principal, s2.principal)
      && formula_eq(s1.formula, s2.formula);
}

bool confirms_eq(Confirms_f c1, Formula f) {
  if (f->type != CONFIRMS_F)
    return false;
  Confirms_f c2 = f->form.confirms_f;
  return principal_eq(c1.principal, c2.principal)
      && formula_eq(c1.formula, c2.formula);
}

bool abs_eq(Abs_f a1, Formula f) {
  if (f->type != ABS_F)
    return false;
  Abs_f a2 = f->form.abs_f;
  return formula_eq(a1.formula, a2.formula);
}

bool formula_eq(Formula f1, Formula f2) {
  switch (f1->type) {
  case PRED_F: return pred_eq(f1->form.pred_f, f2);
  case IMPL_F: return impl_eq(f1->form.impl_f, f2);
  case SIGNED_F: return signed_eq(f1->form.signed_f, f2);
  case SAYS_F: return says_eq(f1->form.says_f, f2);
  case CONFIRMS_F: return confirms_eq(f1->form.confirms_f, f2);
  case ABS_F: return abs_eq(f1->form.abs_f, f2);
  default: return false;
  }
}

Formula pred_cp(Pred_f p) {
	Formula newf = (Formula) malloc(sizeof(struct formula));
  if (newf == NULL)
    return newf;

  newf->type = PRED_F;
  newf->form.pred_f.pred = p.pred;

  Principal newPrin = principal_cp(p.principal);
  if (newPrin == NULL)
    goto freenewf;
  newf->form.pred_f.principal = newPrin;

  return newf;

  freenewf: free(newf);
  return NULL;
}

Formula impl_cp(Impl_f i) {
	Formula newf, newf1, newf2;
	newf = (Formula) malloc(sizeof(struct formula));
  if (newf == NULL)
    return newf;

  newf->type = IMPL_F;

  newf1 = formula_cp(i.formula1);
  if (newf1 == NULL)
    goto freenewf;
  newf->form.impl_f.formula1 = newf1;

  newf2 = formula_cp(i.formula2);
  if (newf2 == NULL)
    goto freenewf1;
  newf->form.impl_f.formula2 = newf2;

  return newf;

  freenewf1: free(newf1);
  freenewf: free(newf);
  return NULL;
}

Formula signed_cp(Signed_f s) {
	Formula newf, newForm;
	Principal newPrin;
	newf = (Formula) malloc(sizeof(struct formula));
  if (newf == NULL)
    return newf;

  newf->type = SIGNED_F;

  newPrin = principal_cp(s.principal);
  if (newPrin == NULL)
    goto freenewf;
  newf->form.signed_f.principal = newPrin;

  newForm = formula_cp(s.formula);
  if (newForm == NULL)
    goto freenewprin;
  newf->form.signed_f.formula = newForm;

  return newf;

  freenewprin: free(newPrin);
  freenewf: free(newForm);
  return NULL;
}

Formula says_cp(Says_f s) {
  Formula newf, newForm;
  Principal newPrin;
  newf = (Formula) malloc(sizeof(struct formula));
  if (newf == NULL)
    return newf;

  newf->type = SAYS_F;

  newPrin = principal_cp(s.principal);
  if (newPrin == NULL)
    goto freenewf;
  newf->form.says_f.principal = newPrin;

  newForm = formula_cp(s.formula);
  if (newForm == NULL)
    goto freenewprin;
  newf->form.says_f.formula = newForm;

  return newf;

  freenewprin: free(newPrin);
  freenewf: free(newForm);
  return NULL;
}

Formula confirms_cp(Confirms_f c) {
  Formula newf, newForm;
  Principal newPrin;
  newf = (Formula) malloc(sizeof(struct formula));
  if (newf == NULL)
    return newf;

  newf->type = CONFIRMS_F;

  newPrin = principal_cp(c.principal);
  if (newPrin == NULL)
    goto freenewf;
  newf->form.confirms_f.principal = newPrin;

  newForm = formula_cp(c.formula);
  if (newForm == NULL)
    goto freenewprin;
  newf->form.confirms_f.formula = newForm;

  return newf;

  freenewprin: free(newPrin);
  freenewf: free(newForm);
  return NULL;
}

Formula abs_cp(Abs_f a) {
  Formula newf, newForm;
  newf = (Formula) malloc(sizeof(struct formula));
  if (newf == NULL)
    return newf;

  newf->type = ABS_F;

  newForm = formula_cp(a.formula);
  if (newForm == NULL)
    goto freenewf;
  newf->form.abs_f.formula = newForm;

  return newf;

  freenewf: free(newf);
  return NULL;
}

Formula formula_cp(Formula f) {
  switch (f->type) {
  case PRED_F: return pred_cp(f->form.pred_f);
  case IMPL_F: return impl_cp(f->form.impl_f);
  case SIGNED_F: return signed_cp(f->form.signed_f);
  case SAYS_F: return says_cp(f->form.says_f);
  case CONFIRMS_F: return confirms_cp(f->form.confirms_f);
  case ABS_F: return abs_cp(f->form.abs_f);
  default: return NULL;
  }
}

Formula formula_subst(Formula f, Var v, Pcpl p) {
  Formula retf = formula_cp(f);
  switch (f->type) {
  case PRED_F:
    retf->form.pred_f.principal = principal_subst(f->form.pred_f.principal, v,
        p);
    if (retf->form.pred_f.principal == NULL)
      goto freeretf;
    return retf;
  case IMPL_F:
    retf->form.impl_f.formula1 = formula_subst(f->form.impl_f.formula1, v, p);
    if (retf->form.impl_f.formula1 == NULL)
      goto freeretf;

    retf->form.impl_f.formula2 = formula_subst(f->form.impl_f.formula2, v, p);
    if (retf->form.impl_f.formula2 == NULL) {
      free(retf->form.impl_f.formula1);
      goto freeretf;
    }
    return retf;
  case SAYS_F:
    retf->form.says_f.principal = principal_subst(f->form.says_f.principal, v,
        p);
    if (retf->form.says_f.principal == NULL)
      goto freeretf;

    retf->form.says_f.formula = formula_subst(f->form.says_f.formula, v, p);
    if (retf->form.says_f.formula == NULL) {
      free(retf->form.says_f.principal);
      goto freeretf;
    }
    return retf;
  case SIGNED_F:
    retf->form.signed_f.principal = principal_subst(f->form.signed_f.principal,
        v, p);
    if (retf->form.signed_f.principal == NULL)
      goto freeretf;

    retf->form.signed_f.formula = formula_subst(f->form.signed_f.formula, v, p);
    if (retf->form.signed_f.formula == NULL) {
      free(retf->form.signed_f.principal);
      goto freeretf;
    }
    return retf;
  case CONFIRMS_F:
    retf->form.confirms_f.principal = principal_subst(
        f->form.confirms_f.principal, v, p);
    if (retf->form.confirms_f.principal == NULL)
      goto freeretf;

    retf->form.confirms_f.formula = formula_subst(f->form.confirms_f.formula, v,
        p);
    if (retf->form.confirms_f.formula == NULL) {
      free(retf->form.confirms_f.principal);
      goto freeretf;
    }
    return retf;
  case ABS_F:
    retf->form.abs_f.formula = formula_subst(f->form.abs_f.formula, v + 1, p);
    if (retf->form.abs_f.formula == NULL)
      goto freeretf;
    return retf;
  default:
    return NULL;
  }

  freeretf: free(retf);
  return NULL;
}

Principal principal_pcpl(Pcpl pcpl) {
  Principal newp = (Principal) malloc(sizeof(struct principal));
  if (newp == NULL)
    return newp;

  newp->type = PCPL;
  newp->prin.pcpl = pcpl;

  return newp;
}

Principal principal_var(Var var) {
  Principal newp = (Principal) malloc(sizeof(struct principal));
  if (newp == NULL)
    return newp;

  newp->type = VAR;
  newp->prin.var = var;

  return newp;
}

Formula formula_pred(Predicate predicate, Principal principal) {
  Formula newf = (Formula) malloc(sizeof(struct formula));
  if (newf == NULL)
    return newf;

  newf->type = PRED_F;
  newf->form.pred_f.pred = predicate;
  newf->form.pred_f.principal = principal_cp(principal);
  if (newf->form.pred_f.principal == NULL)
    goto freenewf;

  return newf;

  freenewf: free(newf);
  return NULL;
}

Formula formula_impl(Formula f1, Formula f2) {
  Formula newf = (Formula) malloc(sizeof(struct formula));
  if (newf == NULL)
    return newf;

  newf->type = IMPL_F;
  newf->form.impl_f.formula1 = formula_cp(f1);
  if (newf->form.impl_f.formula1 == NULL)
    goto freenewf;
  newf->form.impl_f.formula2 = formula_cp(f2);
  if (newf->form.impl_f.formula2 == NULL)
    goto freef1;

  return newf;

  freef1: free(newf->form.impl_f.formula1);
  freenewf: free(newf);
  return NULL;
}

Formula formula_signed(Principal p, Formula f) {
  Formula newf = (Formula) malloc(sizeof(struct formula));
  if (newf == NULL)
    return newf;

  newf->type = SIGNED_F;
  newf->form.signed_f.principal = principal_cp(p);
  if (newf->form.signed_f.principal == NULL)
    goto freenewf;
  newf->form.signed_f.formula = formula_cp(f);
  if (newf->form.signed_f.formula == NULL)
    goto freenewp;

  return newf;

  freenewp: free(newf->form.signed_f.principal);
  freenewf: free(newf);
  return NULL;
}

Formula formula_says(Principal p, Formula f) {
  Formula newf = (Formula) malloc(sizeof(struct formula));
  if (newf == NULL)
    return newf;

  newf->type = SAYS_F;
  newf->form.says_f.principal = principal_cp(p);
  if (newf->form.says_f.principal == NULL)
    goto freenewf;
  newf->form.says_f.formula = formula_cp(f);
  if (newf->form.says_f.formula == NULL)
    goto freenewp;

  return newf;

  freenewp: free(newf->form.says_f.principal);
  freenewf: free(newf);
  return NULL;
}

Formula formula_confirms(Principal p, Formula f) {
  Formula newf = (Formula) malloc(sizeof(struct formula));
  if (newf == NULL)
    return newf;

  newf->type = CONFIRMS_F;
  newf->form.confirms_f.principal = principal_cp(p);
  if (newf->form.confirms_f.principal == NULL)
    goto freenewf;
  newf->form.confirms_f.formula = formula_cp(f);
  if (newf->form.confirms_f.formula == NULL)
    goto freenewp;

  return newf;

  freenewp: free(newf->form.confirms_f.principal);
  freenewf: free(newf);
  return NULL;
}

Formula formula_abs(Formula f) {
  Formula newf = (Formula) malloc(sizeof(struct formula));
  if (newf == NULL)
    return newf;

  newf->type = ABS_F;
  newf->form.abs_f.formula = formula_cp(f);
  if (newf->form.abs_f.formula == NULL)
    goto freenewf;

  return newf;

  freenewf: free(newf);
  return NULL;
}

void formula_free(Formula f) {
  switch (f->type) {
  case PRED_F:
    free(f->form.pred_f.principal);
    break;
  case IMPL_F:
    formula_free(f->form.impl_f.formula1);
    formula_free(f->form.impl_f.formula2);
    break;
  case SAYS_F:
    free(f->form.says_f.principal);
    formula_free(f->form.says_f.formula);
    break;
  case SIGNED_F:
    free(f->form.signed_f.principal);
    formula_free(f->form.signed_f.formula);
    break;
  case CONFIRMS_F:
    free(f->form.confirms_f.principal);
    formula_free(f->form.confirms_f.formula);
    break;
  case ABS_F:
    formula_free(f->form.abs_f.formula);
    break;
  }
  free(f);
}
