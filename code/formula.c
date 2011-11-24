#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <formula.h>

bool principal_eq(Principal p1, Principal p2) {
  switch (p1->type) {
  case VAR:
    return ((p2->type == VAR) && (p1->prin.var == p2->prin.var));
  case PCPL:
    return ((p2->type == PCPL) && (strcmp(p1->prin.pcpl, p2->prin.pcpl) == 0));
  default:
    return false;
  }
}

Principal principal_cp(Principal p) {
  Principal newp = malloc(sizeof(struct principal));
  if (newp == NULL) return newp;

  newp->type = p->type;
  newp->prin = p->prin;

  return newp;
}

Principal principal_subst(Principal prin, Var v, Pcpl p) {
  Principal newp = principal_cp(prin);
  if (newp == NULL) return newp;

  if (newp->type == VAR) {
    if (newp->prin.var == v) {
      newp->type = PCPL;
      char *newstring = malloc(strlen(p)+1);
      if (newstring == NULL) {
	free(newp);
	return NULL;
      }
      newp->prin.pcpl = newstring;
      strcpy(newstring, p);
    } else if (newp->prin.var > v) {
      newp->prin.var = newp->prin.var - 1;
    }
  }

  return newp;
}

void principal_print(Principal prin) {
  switch (prin->type) {
  case VAR:
      printf("v_{%u}", prin->prin.var);
      break;
  case PCPL: 
      printf("%s", prin->prin.pcpl);
      break;
  default:
      printf("UNDEFINED");
  }
}

void pred_print(Pred_f pred) {
  printf("\\pred{%s}{", pred.pred);
  principal_print(pred.principal);
  printf("}");
}

void impl_print(Impl_f impl) {
  printf("\\imp{");
  formula_print(impl.formula1);
  printf("}{");
  formula_print(impl.formula2);
  printf("}");
}

void signed_print(Signed_f sign) {
  printf("\\sign{");
  principal_print(sign.principal);
  printf("}{");
  formula_print(sign.formula);
  printf("}");
}

void says_print(Says_f says) {
  printf("\\says{");
  principal_print(says.principal);
  printf("}{");
  formula_print(says.formula);
  printf("}");
}

void confirms_print(Confirms_f conf) {
  printf("\\confirms{");
  principal_print(conf.principal);
  printf("}{");
  formula_print(conf.formula);
  printf("}");
}

void abs_print(Abs_f abs) {
  printf("\\abs{");
  formula_print(abs.formula);
  printf("}");
}

void formula_print(Formula f){
  switch (f->type) {
  case PRED_F: pred_print(f->form.pred_f); break;
  case IMPL_F: impl_print(f->form.impl_f); break;
  case SIGNED_F: signed_print(f->form.signed_f); break;
  case SAYS_F: says_print(f->form.says_f); break;
  case CONFIRMS_F: confirms_print(f->form.confirms_f); break;
  case ABS_F: abs_print(f->form.abs_f); break;
  default: printf("FORMULA UNDEFINED");
  }
}

bool pred_eq(Pred_f p1, Formula f) {
  if (f->type != PRED_F) return false;
  Pred_f p2 = f->form.pred_f;
  return principal_eq(p1.principal,p2.principal) && (strcmp(p1.pred,p2.pred) == 0);
}

bool impl_eq(Impl_f i1, Formula f) {
  if (f->type != IMPL_F) return false;
  Impl_f i2 = f->form.impl_f;
  return formula_eq(i1.formula1,i2.formula1) && formula_eq(i1.formula2,i2.formula2);
}

bool signed_eq(Signed_f s1, Formula f) {
  if (f->type != SIGNED_F) return false;
  Signed_f s2 = f->form.signed_f;
  return principal_eq(s1.principal,s2.principal) && formula_eq(s1.formula,s2.formula);
}

bool says_eq(Says_f s1, Formula f) {
  if (f->type != SAYS_F) return false;
  Says_f s2 = f->form.says_f;
  return principal_eq(s1.principal,s2.principal) && formula_eq(s1.formula,s2.formula);
}

bool confirms_eq(Confirms_f c1, Formula f) {
  if (f->type != CONFIRMS_F) return false;
  Confirms_f c2 = f->form.confirms_f;
  return principal_eq(c1.principal,c2.principal) && formula_eq(c1.formula,c2.formula);
}

bool abs_eq(Abs_f a1, Formula f) {
  if (f->type != ABS_F) return false;
  Abs_f a2 = f->form.abs_f;
  return formula_eq(a1.formula,a2.formula);
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
  Formula newf = malloc(sizeof(struct formula));
  if (newf == NULL) return newf;

  newf->type = PRED_F;

  char *newstring = malloc(strlen(p.pred)+1);
  if (newstring == NULL) goto freenewf;
  newf->form.pred_f.pred = newstring;
  strcpy(newstring,p.pred);

  Principal newPrin = principal_cp(p.principal);
  if (newPrin == NULL) goto freenewstring;
  newf->form.pred_f.principal = newPrin;

  return newf;

freenewstring:
  free(newstring);
freenewf:
  free(newf);
  return NULL;
}

Formula impl_cp(Impl_f i) {
  Formula newf = malloc(sizeof(struct formula));
  if (newf == NULL) return newf;

  newf->type = IMPL_F;

  Formula newf1 = formula_cp(i.formula1);
  if (newf1 == NULL) goto freenewf;
  newf->form.impl_f.formula1 = newf1;

  Formula newf2 = formula_cp(i.formula2);
  if (newf2 == NULL) goto freenewf1;
  newf->form.impl_f.formula2 = newf2;

  return newf;

freenewf1:
  free(newf1);
freenewf:
  free(newf);
  return NULL;
}

Formula signed_cp(Signed_f s) {
  Formula newf = malloc(sizeof(struct formula));
  if (newf == NULL) return newf;

  newf->type = SIGNED_F;

  Principal newPrin = principal_cp(s.principal);
  if (newPrin == NULL) goto freenewf;
  newf->form.signed_f.principal = newPrin;

  Formula newForm = formula_cp(s.formula);
  if (newForm == NULL) goto freenewprin;
  newf->form.signed_f.formula = newForm;

  return newf;

freenewprin:
  free(newPrin);
freenewf:
  free(newForm);
  return NULL;
}

Formula says_cp(Says_f s) {
  Formula newf = malloc(sizeof(struct formula));
  if (newf == NULL) return newf;

  newf->type = SAYS_F;

  Principal newPrin = principal_cp(s.principal);
  if (newPrin == NULL) goto freenewf;
  newf->form.says_f.principal = newPrin;

  Formula newForm = formula_cp(s.formula);
  if (newForm == NULL) goto freenewprin;
  newf->form.says_f.formula = newForm;

  return newf;

freenewprin:
  free(newPrin);
freenewf:
  free(newForm);
  return NULL;
}

Formula confirms_cp(Confirms_f c) {
  Formula newf = malloc(sizeof(struct formula));
  if (newf == NULL) return newf;

  newf->type = CONFIRMS_F;

  Principal newPrin = principal_cp(c.principal);
  if (newPrin == NULL) goto freenewf;
  newf->form.confirms_f.principal = newPrin;

  Formula newForm = formula_cp(c.formula);
  if (newForm == NULL) goto freenewprin;
  newf->form.confirms_f.formula = newForm;

  return newf;

freenewprin:
  free(newPrin);
freenewf:
  free(newForm);
  return NULL;
}

Formula abs_cp(Abs_f a) {
  Formula newf = malloc(sizeof(struct formula));
  if (newf == NULL) return newf;

  newf->type = ABS_F;

  Formula newForm = formula_cp(a.formula);
  if (newForm == NULL) goto freenewf;
  newf->form.abs_f.formula = newForm;

  return newf;

freenewf:
  free(newf);
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

Formula formula_subst(Formula prin, Var v, Pcpl p);
