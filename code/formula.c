#include <stdio.h>
#include <string.h>
#include <formula.h>

void pcpl_print(Principal prin) {
  switch (prin.type) {
  case VAR:
      printf("v_{%u}", prin.prin.var);
      break;
  case PCPL: 
      printf("%s", prin.prin.pcpl);
      break;
  default:
      printf("UNDEFINED");
  }
}

void pred_print(Pred_f pred) {
  printf("\\pred{%s}{", pred.pred);
  pcpl_print(pred.principal);
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
  pcpl_print(sign.principal);
  printf("}{");
  formula_print(sign.formula);
  printf("}");
}

void says_print(Says_f says) {
  printf("\\says{");
  pcpl_print(says.principal);
  printf("}{");
  formula_print(says.formula);
  printf("}");
}

void confirms_print(Confirms_f conf) {
  printf("\\confirms{");
  pcpl_print(conf.principal);
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

