#include <stdio.h>
#include <proof.h>
#include <formula.h>

#define A 0
#define B 1
#define C 2
#define OK 99
#define ALRIGHT 100

void print_pred(){
  Principal pcpl = principal_pcpl(A);
  Formula pred = formula_pred(OK, pcpl);
  formula_print(pred);
}

void print_impl(){
  Principal pcpl1 = principal_pcpl(A);
  Formula f1 = formula_pred(OK,pcpl1);
  Principal pcpl2 = principal_pcpl(B);
  Formula f2 = formula_pred(ALRIGHT,pcpl2);
  Formula impl = formula_impl(f1,f2);
  formula_print(impl);
}

void print_signed(){
  Principal pcpl1 = principal_pcpl(A);
  Formula f1 = formula_pred(OK,pcpl1);
  Principal pcpl2 = principal_pcpl(B);
  Formula signedf = formula_signed(pcpl2, f1);
  formula_print(signedf);
}

void print_says(){
  Principal pcpl1 = principal_pcpl(A);
  Formula f1 = formula_pred(OK,pcpl1);
  Principal pcpl2 = principal_pcpl(B);
  Formula says = formula_says(pcpl2, f1);
  formula_print(says);
}

void print_confirms(){
  Principal pcpl1 = principal_pcpl(A);
  Formula f1 = formula_pred(OK,pcpl1);
  Principal pcpl2 = principal_pcpl(B);
  Formula conf = formula_confirms(pcpl2, f1);
  formula_print(conf);
}

void print_abs(){
  Principal pcpl1 = principal_var(0);
  Formula f1 = formula_pred(OK,pcpl1);
  Formula abs = formula_abs(f1);
  formula_print(abs);
}

void print_signed_p(){
  Principal pcpl = principal_pcpl(A);
  Formula pred = formula_pred(OK, pcpl);

  Principal pcpl2 = principal_pcpl(B);
  Formula f2 = formula_signed(pcpl2, pred);

  Proof signedp = proof_signed(pred);
  proof_print(signedp);
}

void print_confirms_p() {
	Principal pcpl = principal_pcpl(A);
	Formula pred = formula_pred(OK, pcpl);
	Proof confirms = proof_confirms(pred);
	proof_print(confirms);
}

void print_assump_p(){
	Principal pcpl = principal_pcpl(A);
	Formula pred = formula_pred(OK, pcpl);
	Proof assump = proof_assump(pred);
	proof_print(assump);
}

void print_tauto_p() {
	Principal pcpl1 = principal_pcpl(A);
	Formula f1 = formula_pred(OK, pcpl1);
	Principal pcpl2 = principal_pcpl(B);
	Formula says = formula_says(pcpl2, f1);

	Proof assump = proof_assump(f1);

	Proof tauto = proof_tauto(says, assump);
	proof_print(tauto);
}

void print_weaken_impl_p() {
	Principal pcpl1 = principal_pcpl(A);
	Formula f1 = formula_pred(OK, pcpl1);
	Principal pcpl2 = principal_pcpl(B);
	Formula f2 = formula_pred(ALRIGHT, pcpl2);
	Formula impl = formula_impl(f1, f2);

	Proof assump = proof_assump(f1);

	Proof weaken = proof_weaken_impl(impl, assump);
	proof_print(weaken);
}

void print_impl_p(){
	Principal pcpl1 = principal_pcpl(A);
	Formula f1 = formula_pred(OK, pcpl1);
	Principal pcpl2 = principal_pcpl(B);
	Formula f2 = formula_pred(ALRIGHT, pcpl2);
	Formula impl = formula_impl(f1, f2);

	Proof assump1 = proof_assump(f1);
	Proof assump2 = proof_assump(impl);

	Proof impl_p = proof_impl(f2, assump1, assump2);
	proof_print(impl_p);
}

void print_says_confirms(){
	Principal pcpl2 = principal_pcpl(B);
	Formula f1 = formula_pred(ALRIGHT, pcpl2);

	Principal pcpl1 = principal_pcpl(A);
	Formula f2 = formula_pred(OK, pcpl1);
	Formula says = formula_says(pcpl1, f2);

	Proof confirms = proof_confirms(f1);
	Proof assump = proof_assump(says);

	Proof says_confirms_p = proof_says_confirms(says, confirms, assump);
	proof_print(says_confirms_p);
}

void print_says_signed(){
	Principal pcpl2 = principal_pcpl(B);
	Formula f1 = formula_pred(ALRIGHT, pcpl2);

	Principal pcpl1 = principal_pcpl(A);
	Formula f2 = formula_pred(OK, pcpl1);
	Formula says = formula_says(pcpl1, f2);

	Proof signedp = proof_signed(f1);
	Proof assump = proof_assump(says);

	Proof says_signed_p = proof_says_signed(says, signedp, assump);
	proof_print(says_signed_p);
}

void print_says_says(){
	Principal pcpl1 = principal_pcpl(A);
	Principal pcpl2 = principal_pcpl(B);
	Formula f1 = formula_pred(ALRIGHT, pcpl2);
	Formula says1 = formula_says(pcpl1, f1);

	Formula f2 = formula_pred(OK, pcpl1);
	Formula says2 = formula_says(pcpl1, f2);

	Proof assump1 = proof_assump(says1);
	Proof assump2 = proof_assump(says2);

	Proof says_says_p = proof_says_says(says2, assump1, assump2);
	proof_print(says_says_p);
}

void print_says_spec(){
	Principal pcpl1 = principal_pcpl(A);
	Principal pcpl2 = principal_pcpl(B);
	Formula f2 = formula_pred(ALRIGHT, pcpl2);
	Formula says = formula_says(pcpl1, f2);

	Formula f1 = formula_pred(OK, pcpl1);
	Formula abs_f = formula_abs(f1);
	Formula says_abs = formula_says(pcpl1, abs_f);

	Proof assump_says = proof_assump(says);
	Proof assump_abs = proof_assump(says_abs);

	Pcpl pcpl = C;

	Proof says_spec = proof_says_spec(says, pcpl, assump_abs, assump_says);
	proof_print(says_spec);
}

void print_delegation() {
  Proof dpf = delegate_from_signed(A,B,OK);
  Proof apf = approval_from_signed(B,OK,C);
  Proof delegation = use_delegation(A,B,C,OK,dpf,apf);
  proof_print(delegation);
  proof_free(delegation);
  proof_free(apf);
  proof_free(dpf);
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
	print_signed_p();
	printf("\n");
	print_confirms_p();
	printf("\n");
	print_signed_p();
	printf("\n");
	print_assump_p();
	printf("\n");
	print_tauto_p();
	printf("\n");
	print_weaken_impl_p();
	printf("\n");
	print_impl_p();
	printf("\n");
	print_says_confirms();
	printf("\n");
	print_says_signed();
	printf("\n");
	print_says_says();
	printf("\n");
	print_says_spec();
	printf("\n");
	print_delegation();
	printf("\n");
	return 0;
}
