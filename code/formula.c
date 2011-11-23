#include <stdio.h>
#include <string.h>
#include <formula.h>

void formula_print(Formula f){
	char name[10];
	char prin[10];

	switch (f->type) {

	case PRED:
		strcpy(name, "Pred_f");
		switch(f->form.pred_f.principal->type) {

		case VAR:
			printf("Pred_f %s %u\n", f->form.pred_f.pred, f->form.pred_f.principal->prin.var);
			break;
		case PCPL:
			printf("Pred_f %s %s\n", f->form.pred_f.pred, f->form.pred_f.principal->prin.pcpl);
			break;
		default:
			strcpy(prin, "UNDEFINED");
			printf("Pred_f %s %s\n", f->form.pred_f.pred, prin);
			break;
		}
		break;
	case IMPL:
		strcpy(name, "Impl_f");
		break;
	case SIGNED:
		strcpy(name, "Signed_f");
		break;
	case SAYS:
		strcpy(name, "Says_f");
		break;
	case CONFIRMS:
		strcpy(name, "Confirms_f");
		break;
	case ABS:
		strcpy(name, "Abs_f");
		break;
	default:
		strcpy(name, "UNDEFINED");
		break;
	}
	printf("Formula is of type %s\n", name);
}
