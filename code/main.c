#include <stdio.h>
#include <proof.h>
#include <formula.h>

void print_pred(){
	Pred_f pred;
	pred.principal.prin.pcpl = "A\0";
	pred.principal.type = PCPL;
	pred.pred = "OK\0";

	struct formula f;
	f.type = PRED_F;
	f.form.pred_f = pred;
	formula_print(&f);
}

void print_impl(){
	Pred_f pred1;
	pred1.principal.prin.pcpl = "A\0";
	pred1.principal.type = PCPL;
	pred1.pred = "OK\0";

	struct formula f1;
	f1.type = PRED_F;
	f1.form.pred_f = pred1;

	Pred_f pred2;
	pred2.principal.prin.pcpl = "B\0";
	pred2.principal.type = PCPL;
	pred2.pred = "ALRIGHT\0";

	struct formula f2;
	f2.type = PRED_F;
	f2.form.pred_f = pred2;

	Impl_f impl;
	impl.formula1 = &f1;
	impl.formula2 = &f2;

	struct formula f;
	f.type = IMPL_F;
	f.form.impl_f = impl;

	formula_print(&f);
}

void print_signed(){
	Pred_f pred1;
	pred1.principal.prin.pcpl = "A\0";
	pred1.principal.type = PCPL;
	pred1.pred = "OK\0";

	struct formula f1;
	f1.type = PRED_F;
	f1.form.pred_f = pred1;

	Signed_f signed_f;
	signed_f.principal.prin.pcpl = "B\0";
	signed_f.principal.type = PCPL;
	signed_f.formula = &f1;

	struct formula f2;
	f2.type = SIGNED_F;
	f2.form.signed_f = signed_f;

	formula_print(&f2);
}

void print_says(){
	Pred_f pred1;
	pred1.principal.prin.pcpl = "A\0";
	pred1.principal.type = PCPL;
	pred1.pred = "OK\0";

	struct formula f1;
	f1.type = PRED_F;
	f1.form.pred_f = pred1;

	Says_f says_f;
	says_f.principal.prin.pcpl = "B\0";
	says_f.principal.type = PCPL;
	says_f.formula = &f1;

	struct formula f2;
	f2.type = SAYS_F;
	f2.form.says_f = says_f;

	formula_print(&f2);
}

void print_confirms(){
	Pred_f pred1;
	pred1.principal.prin.pcpl = "A\0";
	pred1.principal.type = PCPL;
	pred1.pred = "OK\0";

	struct formula f1;
	f1.type = PRED_F;
	f1.form.pred_f = pred1;

	Confirms_f confirms_f;
	confirms_f.principal.prin.pcpl = "B\0";
	confirms_f.principal.type = PCPL;
	confirms_f.formula = &f1;

	struct formula f2;
	f2.type = CONFIRMS_F;
	f2.form.confirms_f = confirms_f;

	formula_print(&f2);
}

void print_abs(){
	Pred_f pred1;
	pred1.principal.prin.pcpl = "A\0";
	pred1.principal.type = PCPL;
	pred1.pred = "OK\0";

	struct formula f1;
	f1.type = PRED_F;
	f1.form.pred_f = pred1;

	Abs_f abs_f;
	abs_f.formula = &f1;

	struct formula f2;
	f2.type = ABS_F;
	f2.form.abs_f = abs_f;

	formula_print(&f2);
}

int main()
{
	print_pred();
	printf("\n");
	print_impl();
	printf("\n");
	print_signed();
	printf("\n");
	print_says();
	printf("\n");
	print_confirms();
	printf("\n");
	print_abs();
	printf("\n");
	return 0;
}
