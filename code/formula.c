#include <stdio.h>
#include <string.h>
#include <formula.h>

void formula_print(Formula f){
	char name[10];
	char prin[10];

	switch (f->type) {

	case PRED_F:
		strcpy(name, "Pred_f");
		switch(f->form.pred_f.principal->type) {

		case VAR:
			printf("Pred_f %s %u", f->form.pred_f.pred, f->form.pred_f.principal->prin.var);
			break;
		case PCPL:
			printf("Pred_f %s %s", f->form.pred_f.pred, f->form.pred_f.principal->prin.pcpl);
			break;
		default:
			strcpy(prin, "PRINCIPAL UNDEFINED");
			printf("Pred_f %s %s", f->form.pred_f.pred, prin);
			break;
		}
		break;
	case IMPL_F:
		printf("Impl_f f1 f2");
		printf("\n     f1 = ");
		formula_print(f->form.impl_f.formula1);
		printf("\n     f2 = ");
		formula_print(f->form.impl_f.formula2);
		break;
	case SIGNED_F:
		printf("Signed_f %s f", f->form.signed_f.pcpl);
		printf("\n     f = ");
		formula_print(f->form.signed_f.formula);
		break;
	case SAYS_F:
		printf("Says_f %s f", f->form.signed_f.pcpl);
		printf("\n     f = ");
		formula_print(f->form.says_f.formula);
		break;
	case CONFIRMS_F:
		printf("Confirms_f %s f", f->form.signed_f.pcpl);
		printf("\n     f = ");
		formula_print(f->form.confirms_f.formula);
		break;
	case ABS_F:
		printf("Abs_f f");
		printf("\n     f = ");
		formula_print(f->form.abs_f.formula);
		break;
	default:
		printf("FORMULA UNDEFINED");
		break;
	}
}
