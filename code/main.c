#include <stdio.h>
#include <proof.h>
#include <formula.h>

#define A 0
#define B 1
#define OK 99
#define ALRIGHT 100

void print_pred(){
        struct principal pcpl;
	pcpl.type = PCPL;
	pcpl.prin.pcpl = A;

	Pred_f pred;
	pred.principal = &pcpl;
	pred.pred = OK;

	struct formula f;
	f.type = PRED_F;
	f.form.pred_f = pred;
	formula_print(&f);
}

void print_impl(){
        struct principal pcpl1;
	pcpl1.type = PCPL;
	pcpl1.prin.pcpl = A;

	Pred_f pred1;
	pred1.principal = &pcpl1;
	pred1.pred = OK;

	struct formula f1;
	f1.type = PRED_F;
	f1.form.pred_f = pred1;

        struct principal pcpl2;
	pcpl2.type = PCPL;
	pcpl2.prin.pcpl = B;

	Pred_f pred2;
	pred2.principal = &pcpl2;
	pred2.pred = ALRIGHT;

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
        struct principal pcpl1;
	pcpl1.prin.pcpl = A;
	pcpl1.type = PCPL;

	Pred_f pred1;
	pred1.principal = &pcpl1;
	pred1.pred = OK;

	struct formula f1;
	f1.type = PRED_F;
	f1.form.pred_f = pred1;

	struct principal pcpl2;
	pcpl2.prin.pcpl = B;
	pcpl2.type = PCPL;

	Signed_f signed_f;
	signed_f.principal = &pcpl2;
	signed_f.formula = &f1;

	struct formula f2;
	f2.type = SIGNED_F;
	f2.form.signed_f = signed_f;

	formula_print(&f2);
}

void print_says(){
        struct principal pcpl1;
	pcpl1.prin.pcpl = A;
	pcpl1.type = PCPL;
	
	Pred_f pred1;
	pred1.principal = &pcpl1;
	pred1.pred = OK;

	struct formula f1;
	f1.type = PRED_F;
	f1.form.pred_f = pred1;

	struct principal pcpl2;
	pcpl2.prin.pcpl = B;
	pcpl2.type = PCPL;

	Says_f says_f;
	says_f.principal = &pcpl2;
	says_f.formula = &f1;

	struct formula f2;
	f2.type = SAYS_F;
	f2.form.says_f = says_f;

	formula_print(&f2);
}

void print_confirms(){
        struct principal pcpl1;
	pcpl1.prin.pcpl = A;
	pcpl1.type = PCPL;

	Pred_f pred1;
	pred1.principal = &pcpl1;
	pred1.pred = OK;

	struct formula f1;
	f1.type = PRED_F;
	f1.form.pred_f = pred1;

	struct principal pcpl2;
	pcpl2.prin.pcpl = B;
	pcpl2.type = PCPL;

	Confirms_f confirms_f;
	confirms_f.principal = &pcpl2;
	confirms_f.formula = &f1;

	struct formula f2;
	f2.type = CONFIRMS_F;
	f2.form.confirms_f = confirms_f;

	formula_print(&f2);
}

void print_abs(){
        struct principal pcpl1;
	pcpl1.prin.pcpl = A;
	pcpl1.type = PCPL;

	Pred_f pred1;
	pred1.principal = &pcpl1;
	pred1.pred = OK;

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
