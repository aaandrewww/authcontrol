#include <stdio.h>
#include <proof.h>
#include <formula.h>
#include <context.h>

#define A 1
#define B 2
#define C 3
#define D 4
#define E 5
#define F 6
#define G 7
#define OK 99
#define ALRIGHT 100

void print_pred() {
  Principal pcpl = principal_pcpl(A);
  Formula pred = formula_pred(OK, pcpl);
  formula_print(pred);
}

void print_impl() {
  Principal pcpl1 = principal_pcpl(A);
  Formula f1 = formula_pred(OK, pcpl1);
  Principal pcpl2 = principal_pcpl(B);
  Formula f2 = formula_pred(ALRIGHT, pcpl2);
  Formula impl = formula_impl(f1, f2);
  formula_print(impl);
}

void print_signed() {
  Principal pcpl1 = principal_pcpl(A);
  Formula f1 = formula_pred(OK, pcpl1);
  Principal pcpl2 = principal_pcpl(B);
  Formula signedf = formula_signed(pcpl2, f1);
  formula_print(signedf);
}

void print_says() {
  Principal pcpl1 = principal_pcpl(A);
  Formula f1 = formula_pred(OK, pcpl1);
  Principal pcpl2 = principal_pcpl(B);
  Formula says = formula_says(pcpl2, f1);
  formula_print(says);
}

void print_confirms() {
  Principal pcpl1 = principal_pcpl(A);
  Formula f1 = formula_pred(OK, pcpl1);
  Principal pcpl2 = principal_pcpl(B);
  Formula conf = formula_confirms(pcpl2, f1);
  formula_print(conf);
}

void print_abs() {
  Principal pcpl1 = principal_var(0);
  Formula f1 = formula_pred(OK, pcpl1);
  Formula abs = formula_abs(f1);
  formula_print(abs);
}

void print_signed_p() {
  Principal pcpl = principal_pcpl(A);
  Formula pred = formula_pred(OK, pcpl);

  Principal pcpl2 = principal_pcpl(B);
  Formula f2 = formula_signed(pcpl2, pred);

  Proof signedp = proof_signed(f2);
  proof_print(signedp);
}

void print_confirms_p() {
  Principal pcpl = principal_pcpl(A);
  Formula pred = formula_pred(OK, pcpl);

  Principal pcpl2 = principal_pcpl(B);
  Formula f2 = formula_confirms(pcpl2, pred);
  Proof confirms = proof_confirms(f2);
  proof_print(confirms);
}

void print_assump_p() {
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

void print_impl_p() {
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

void print_says_confirms() {
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

void print_says_signed() {
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

void print_says_says() {
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

void print_says_spec() {
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
  Proof dpf = delegate_from_signed(A, B, OK);
  Proof apf = approval_from_signed(B, OK, C);
  Proof delegation = use_delegation(A, B, C, OK, dpf, apf);
  proof_print(delegation);
  proof_free(delegation);
  proof_free(apf);
  proof_free(dpf);
}

void print_context() {
  Principal p1 = principal_pcpl(A);
  Formula f1 = formula_pred(OK, p1);

  Principal p2 = principal_pcpl(B);
  Formula f2 = formula_pred(ALRIGHT, p2);

  Principal p3 = principal_pcpl(C);
  Formula f3 = formula_pred(OK, p3);

  Principal p4 = principal_pcpl(D);
  Formula f4 = formula_pred(ALRIGHT, p4);

  Principal p5 = principal_pcpl(E);
  Formula f5 = formula_pred(OK, p5);

  Principal p6 = principal_pcpl(F);
  Formula f6 = formula_pred(ALRIGHT, p6);

  Principal p7 = principal_pcpl(G);
  Formula f7 = formula_pred(OK, p7);

  Context c = context_alloc(7);
  printf("\\text{Loading context} \\\\ \n");
  printf("1");
  push(c, f1);
  printf("2");
  push(c, f2);
  printf("3");
  push(c, f3);
  printf("4");
  push(c, f4);
  printf("5");
  push(c, f5);
  printf("6");
  push(c, f6);
  printf("7");
  push(c, f7);
  printf("8 \\\\ \n");
  push(c, f1);

  printf("\\\\ \n \\text{Printing context} \\\\ \n");
  context_print(c);
}

void printall() {
  printf("$ \n");
  printf("\\text{Principal } 1 == A \\\\ \n");
  printf("\\text{Principal } 2 == B \\\\ \n");
  printf("\\text{Principal } 3 == C \\\\ \n");
  printf("\\text{Principal } 4 == D \\\\ \n");
  printf("\\text{Principal } 5 == E \\\\ \n");
  printf("\\text{Principal } 6 == F \\\\ \n");
  printf("\\text{Principal } 7 == G \\\\ \n");
  printf("\\text{Predicate } 99 == OK \\\\ \n");
  printf("\\text{Predicate } 100 == ALRIGHT \\\\ \n");
  print_pred();
  printf(" \\\\\\\\ \n");
  print_impl();
  printf(" \\\\\\\\ \n");
  print_signed();
  printf(" \\\\\\\\ \n");
  print_says();
  printf(" \\\\\\\\ \n");
  print_confirms();
  printf(" \\\\\\\\ \n");
  print_abs();
  printf(" \\\\\\\\ \n");
  print_context();
  printf(" \\\\\\\\ \n");
  print_signed_p();
  printf(" \\\\\\\\\\\\\\\\ \n");
  print_confirms_p();
  printf(" \\\\\\\\\\\\\\\\ \n");
  print_assump_p();
  printf(" \\\\\\\\\\\\\\\\ \n");
  print_tauto_p();
  printf(" \\\\\\\\\\\\\\\\ \n");
  print_weaken_impl_p();
  printf(" \\\\\\\\\\\\\\\\ \n");
  print_impl_p();
  printf(" \\\\\\\\\\\\\\\\ \n");
  print_says_confirms();
  printf(" \\\\\\\\\\\\\\\\ \n");
  print_says_signed();
  printf(" \\\\\\\\\\\\\\\\ \n");
  print_says_says();
  printf(" \\\\\\\\\\\\\\\\ \n");
  print_says_spec();
  printf(" \\\\\\\\\\\\\\\\ \n");
  printf("$ \n");
  printf("\\begin{landscape} \n $");
  print_delegation();
  printf("$ \n \\end{landscape} \n ");
}

void test_principal_eq() {
  Principal p1;
  Principal p2;
  bool b;

  p1 = principal_pcpl(A);
  p2 = principal_pcpl(A);
  b = principal_eq(p1, p2);

  if (b != 1)
    printf("ERROR: Equal pcpl: 1 == %u\n", b);

  p1 = principal_pcpl(A);
  p2 = principal_pcpl(B);
  b = principal_eq(p1, p2);
  if (b != 0)
    printf("ERROR: Unequal pcpl: 0 == %u\n", b);

  p1 = principal_var(0);
  p2 = principal_var(0);
  b = principal_eq(p1, p2);
  if (b != 1)
    printf("ERROR: Equal var: 1 == %u\n", b);

  p1 = principal_var(0);
  p2 = principal_var(1);
  b = principal_eq(p1, p2);
  if (b != 0)
    printf("ERROR: Unqual var: 0 == %u\n", b);

  p1 = principal_pcpl(A);
  p2 = principal_var(0);
  b = principal_eq(p1, p2);
  if (b != 0)
    printf("ERROR: Unqual pcpl and var: 0 == %u\n", b);

  p2 = principal_pcpl(A);
  p1 = principal_var(0);
  b = principal_eq(p1, p2);
  if (b != 0)
    printf("ERROR: Unqual var and pcpl: 0 == %u\n", b);
}

void test_principal_cp() {
  Principal p1;
  Principal p2;
  bool b;

  p1 = principal_pcpl(A);
  p2 = principal_cp(p1);
  b = principal_eq(p1, p2);
  if (b != 1)
    printf("ERROR: Copy pcpl: 1 == %u\n", b);

  p1 = principal_var(0);
  p2 = principal_cp(p1);
  b = principal_eq(p1, p2);
  if (b != 1)
    printf("ERROR: Copy var: 1 == %u\n", b);
}

void test_principal_subst() {
  Principal p1;
  Principal p2;
  Principal p3;
  bool b;
  Var v0 = 0;
  Var v1 = 1;
  Pcpl pcpl1 = A;
  Pcpl pcpl2 = B;

  p1 = principal_pcpl(pcpl1);
  p2 = principal_subst(p1, v0, pcpl2);
  b = principal_eq(p1, p2);
  if (b != 1) {
    printf("ERROR: Subst pcpl: 1 == %u\n", b);
    printf("Before: ");
    principal_print(p1);
    printf("\n");
    printf("After: ");
    principal_print(p2);
    printf("\n");
  }

  p1 = principal_var(v0);
  p2 = principal_subst(p1, v0, pcpl1);
  p3 = principal_pcpl(pcpl1);
  b = principal_eq(p2, p3);
  if (b != 1) {
    printf("ERROR: Subst correct var: 1 == %u\n", b);
    printf("Before: ");
    principal_print(p1);
    printf("\n");
    printf("After: ");
    principal_print(p2);
    printf("\n");
  }

  p1 = principal_var(v0);
  p2 = principal_subst(p1, v1, pcpl1);
  b = principal_eq(p1, p2);
  if (b != 1) {
    printf("ERROR: Subst bigger var: 1 == %u\n", b);
    printf("Before: ");
    principal_print(p1);
    printf("\n");
    printf("After: ");
    principal_print(p2);
    printf("\n");
  }

  p1 = principal_var(v1);
  p2 = principal_subst(p1, v0, pcpl1);
  p3 = principal_var(v0);
  b = principal_eq(p2, p3);
  if (b != 1) {
    printf("ERROR: Subst smaller var: 1 == %u\n", b);
    printf("Before: ");
    principal_print(p1);
    printf("\n");
    printf("After: ");
    principal_print(p2);
    printf("\n");
  }
}

void test_formula_eq() {
  Formula f1;
  Formula f2;
  Formula f3;
  Formula f4;
  Formula f5;
  Formula f6;
  Predicate pred1 = OK;
  Predicate pred2 = ALRIGHT;
  Principal prinA = principal_pcpl(A);
  Principal prinB = principal_pcpl(B);
  bool b;

  f1 = formula_pred(pred1, prinA);
  f2 = formula_pred(pred1, prinA);
  b = formula_eq(f1, f2);
  if (b != 1)
    printf("ERROR: Pred equal: 1 == %u\n", b);

  f1 = formula_pred(pred1, prinA);
  f2 = formula_pred(pred2, prinA);
  b = formula_eq(f1, f2);
  if (b != 0)
    printf("ERROR: Pred unequal: 0 == %u\n", b);

  f1 = formula_pred(pred1, prinA);
  f2 = formula_pred(pred1, prinB);
  b = formula_eq(f1, f2);
  if (b != 0)
    printf("ERROR: Pred unequal: 0 == %u\n", b);

  f1 = formula_pred(pred1, prinA);
  f2 = formula_pred(pred2, prinB);
  f3 = formula_impl(f1, f2);
  f4 = formula_pred(pred1, prinA);
  f5 = formula_pred(pred2, prinB);
  f6 = formula_impl(f4, f5);
  b = formula_eq(f3, f6);
  if (b != 1)
    printf("ERROR: Impl equal: 1 == %u\n", b);

  f1 = formula_pred(pred1, prinA);
  f2 = formula_pred(pred2, prinB);
  f4 = formula_pred(pred1, prinA);
  f5 = formula_pred(pred2, prinB);

  f3 = formula_impl(f1, f4);
  f6 = formula_impl(f4, f5);
  b = formula_eq(f3, f6);
  if (b != 0)
    printf("ERROR: Impl unequal: 0 == %u\n", b);

  f3 = formula_impl(f1, f2);
  f6 = formula_impl(f2, f5);
  b = formula_eq(f3, f6);
  if (b != 0)
    printf("ERROR: Impl unequal: 0 == %u\n", b);

  b = formula_eq(f1, f6);
  if (b != 0)
    printf("ERROR: Impl//Pred unequal: 0 == %u\n", b);

  f3 = formula_signed(prinA, f1);
  f6 = formula_signed(prinA, f4);
  b = formula_eq(f3, f6);
  if (b != 1)
    printf("ERROR: Signed equal: 1 == %u\n", b);

  f3 = formula_signed(prinA, f1);
  f6 = formula_signed(prinB, f4);
  b = formula_eq(f3, f6);
  if (b != 0)
    printf("ERROR: Signed unequal: 0 == %u\n", b);

  f3 = formula_signed(prinA, f1);
  f6 = formula_signed(prinA, f2);
  b = formula_eq(f3, f6);
  if (b != 0)
    printf("ERROR: Signed unequal: 0 == %u\n", b);

  f3 = formula_confirms(prinA, f1);
  f6 = formula_confirms(prinA, f4);
  b = formula_eq(f3, f6);
  if (b != 1)
    printf("ERROR: Confirms equal: 1 == %u\n", b);

  f3 = formula_confirms(prinA, f1);
  f6 = formula_confirms(prinB, f4);
  b = formula_eq(f3, f6);
  if (b != 0)
    printf("ERROR: Confirms unequal: 0 == %u\n", b);

  f3 = formula_confirms(prinA, f1);
  f6 = formula_confirms(prinA, f2);
  b = formula_eq(f3, f6);
  if (b != 0)
    printf("ERROR: Confirms unequal: 0 == %u\n", b);

  f3 = formula_says(prinA, f1);
  f6 = formula_says(prinA, f4);
  b = formula_eq(f3, f6);
  if (b != 1)
    printf("ERROR: Says equal: 1 == %u\n", b);

  f3 = formula_says(prinA, f1);
  f6 = formula_says(prinB, f4);
  b = formula_eq(f3, f6);
  if (b != 0)
    printf("ERROR: Says unequal: 0 == %u\n", b);

  f3 = formula_says(prinA, f1);
  f6 = formula_says(prinA, f2);
  b = formula_eq(f3, f6);
  if (b != 0)
    printf("ERROR: Says unequal: 0 == %u\n", b);

  f3 = formula_abs(f1);
  f6 = formula_abs(f4);
  b = formula_eq(f3, f6);
  if (b != 1)
    printf("ERROR: Abs equal: 1 == %u\n", b);

  f3 = formula_abs(f1);
  f6 = formula_abs(f2);
  b = formula_eq(f3, f6);
  if (b != 0)
    printf("ERROR: Abs unequal: 0 == %u\n", b);
}

void test_formula_cp() {
  Formula f1;
  Formula f2;
  Formula f3;
  Formula f4;
  Predicate pred1 = OK;
  Predicate pred2 = ALRIGHT;
  Principal prinA = principal_pcpl(A);
  Principal prinB = principal_pcpl(B);
  bool b;

  f1 = formula_pred(pred1, prinA);
  f2 = formula_cp(f1);
  b = formula_eq(f1, f2);
  if (b != 1)
    printf("ERROR: Pred cp: 1 == %u\n", b);

  f1 = formula_pred(pred1, prinA);
  f2 = formula_pred(pred2, prinB);
  f3 = formula_impl(f1, f2);
  f4 = formula_cp(f3);
  b = formula_eq(f3, f4);
  if (b != 1)
    printf("ERROR: Impl cp: 1 == %u\n", b);

  f3 = formula_signed(prinA, f1);
  f4 = formula_cp(f3);
  b = formula_eq(f3, f4);
  if (b != 1)
    printf("ERROR: Signed cp: 1 == %u\n", b);

  f3 = formula_confirms(prinA, f1);
  f4 = formula_cp(f3);
  b = formula_eq(f3, f4);
  if (b != 1)
    printf("ERROR: Confirms cp: 1 == %u\n", b);

  f3 = formula_says(prinA, f1);
  f4 = formula_cp(f3);
  b = formula_eq(f3, f4);
  if (b != 1)
    printf("ERROR: Says cp: 1 == %u\n", b);

  f3 = formula_abs(f1);
  f4 = formula_cp(f3);
  b = formula_eq(f3, f4);
  if (b != 1)
    printf("ERROR: Abs cp: 1 == %u\n", b);
}

void test_formula_subst() {
  Formula f1;
  Formula f2;
  Formula f3;
  Formula f4;
  Formula f5;
  Formula f6;
  Formula f7;
  Predicate pred1 = OK;
  Predicate pred2 = ALRIGHT;
  Var v0 = 0;
  Var v1 = 1;
  Pcpl pcplA = A;
  Pcpl pcplB = B;
  Principal prinA = principal_pcpl(pcplA);
  Principal prinB = principal_pcpl(pcplB);
  Principal prin0 = principal_var(v0);
  Principal prin1 = principal_var(v1);
  bool b;

  f1 = formula_pred(pred1, prin0);
  f2 = formula_subst(f1, v0, pcplA);
  f3 = formula_pred(pred1, prinA);
  b = formula_eq(f2, f3);
  if (b != 1)
    printf("ERROR: Pred subst: 1 == %u\n", b);

  f1 = formula_pred(pred1, prin0);
  f2 = formula_pred(pred2, prin1);
  f3 = formula_impl(f1, f2);
  f4 = formula_subst(f3, v0, pcplA);
  f5 = formula_pred(pred1, prinA);
  f6 = formula_pred(pred2, prin0);
  f7 = formula_impl(f5, f6);
  b = formula_eq(f4, f7);
  if (b != 1)
    printf("ERROR: Impl subst: 1 == %u\n", b);

  f3 = formula_signed(prin1, f1);
  f4 = formula_subst(f3, v1, pcplA);
  f5 = formula_signed(prinA, f1);
  b = formula_eq(f4, f5);
  if (b != 1)
    printf("ERROR: Signed subst: 1 == %u\n", b);

  f3 = formula_confirms(prin1, f1);
  f4 = formula_subst(f3, v1, pcplA);
  f5 = formula_confirms(prinA, f1);
  b = formula_eq(f4, f5);
  if (b != 1)
    printf("ERROR: Confirms subst: 1 == %u\n", b);

  f3 = formula_says(prin1, f1);
  f4 = formula_subst(f3, v1, pcplA);
  f5 = formula_says(prinA, f1);
  b = formula_eq(f4, f5);
  if (b != 1)
    printf("ERROR: Says subst: 1 == %u\n", b);

  f3 = formula_abs(f2);
  f4 = formula_subst(f3, v0, pcplA);
  f5 = formula_pred(pred2, prinA);
  f6 = formula_abs(f5);
  b = formula_eq(f4, f6);
  if (b != 1)
    printf("ERROR: Abs cp: 1 == %u\n", b);
}

void test_proof_eq() {
  Principal prinA = principal_pcpl(A);
  Principal prinB = principal_pcpl(B);
  Predicate pred = OK;
  Predicate pred2 = ALRIGHT;
  Formula fpred = formula_pred(pred, prinA);
  Formula fpred2 = formula_pred(pred2, prinB);
  Formula fsays1 = formula_says(prinA, fpred);
  Formula fsays2 = formula_says(prinA, fpred2);
  Formula f1;
  Formula f2;
  Proof p1;
  Proof p2;
  Proof p3;
  Proof p4;
  Proof p5;
  Proof p6;
  bool b;

  f1 = formula_signed(prinA, fpred);
  p1 = proof_signed(f1);
  p2 = proof_signed(f1);
  b = proof_eq(p1, p2);
  if (b != 1)
    printf("ERROR: signed proof eq: 1 == %u\n", b);

  f1 = formula_confirms(prinA, fpred);
  p3 = proof_confirms(f1);
  p4 = proof_confirms(f1);
  b = proof_eq(p3, p4);
  if (b != 1)
    printf("ERROR: confirms proof eq: 1 == %u\n", b);

  b = proof_eq(p1, p4);
  if (b != 0)
    printf("ERROR: confirms/signed proof eq: 0 == %u\n", b);

  p1 = proof_assump(fpred);
  p2 = proof_assump(fpred);
  b = proof_eq(p1, p2);
  if (b != 1)
    printf("ERROR: assump proof eq: 1 == %u\n", b);

  f1 = formula_says(prinB, fpred);
  p1 = proof_assump(fpred);
  p2 = proof_tauto(f1, p1);
  p3 = proof_assump(fpred);
  p4 = proof_tauto(f1, p3);
  b = proof_eq(p2, p4);
  if (b != 1)
    printf("ERROR: tauto proof eq: 1 == %u\n", b);

  f1 = formula_impl(fpred, fpred2);
  p1 = proof_assump(fpred2);
  p2 = proof_weaken_impl(f1, p1);
  p3 = proof_assump(fpred2);
  p4 = proof_weaken_impl(f1, p3);
  b = proof_eq(p2, p4);
  if (b != 1)
    printf("ERROR: weaken_impl proof eq: 1 == %u\n", b);

  f1 = formula_impl(fpred, fpred2);
  p1 = proof_assump(fpred);
  p2 = proof_assump(f1);
  p3 = proof_impl(fpred2, p1, p2);
  p4 = proof_assump(fpred);
  p5 = proof_assump(f1);
  p6 = proof_impl(fpred2, p4, p5);
  b = proof_eq(p3, p6);
  if (b != 1)
    printf("ERROR: impl proof eq: 1 == %u\n", b);

  f1 = formula_confirms(prinA, fpred);
  p1 = proof_assump(f1);
  p2 = proof_assump(fsays1);
  p3 = proof_says_confirms(fsays2, p1, p2);
  p4 = proof_assump(f1);
  p5 = proof_assump(fsays1);
  p6 = proof_says_confirms(fsays2, p4, p5);
  b = proof_eq(p3, p6);
  if (b != 1)
    printf("ERROR: says confirms proof eq: 1 == %u\n", b);

  f1 = formula_says(prinA, fpred);
  p1 = proof_assump(f1);
  p2 = proof_assump(fsays1);
  p3 = proof_says_says(fsays2, p1, p2);
  p4 = proof_assump(f1);
  p5 = proof_assump(fsays1);
  p6 = proof_says_says(fsays2, p4, p5);
  b = proof_eq(p3, p6);
  if (b != 1)
    printf("ERROR: says says proof eq: 1 == %u\n", b);

  f1 = formula_signed(prinA, fpred);
  p1 = proof_assump(f1);
  p2 = proof_assump(fsays1);
  p3 = proof_says_signed(fsays2, p1, p2);
  p4 = proof_assump(f1);
  p5 = proof_assump(fsays1);
  p6 = proof_says_signed(fsays2, p4, p5);
  b = proof_eq(p3, p6);
  if (b != 1)
    printf("ERROR: says signed proof eq: 1 == %u\n", b);

  Pcpl pcplB = B;
  f1 = formula_abs(fpred);
  f2 = formula_says(prinA, f1);
  p1 = proof_assump(f2);
  p2 = proof_assump(fsays2);
  p3 = proof_says_spec(fsays2, pcplB, p1, p2);
  p4 = proof_assump(f2);
  p5 = proof_assump(fsays2);
  p6 = proof_says_spec(fsays2, pcplB, p4, p5);
  b = proof_eq(p3, p6);
  if (b != 1)
    printf("ERROR: says spec proof eq: 1 == %u\n", b);
}
void test_proof_cp() {
  Principal prinA = principal_pcpl(A);
  Principal prinB = principal_pcpl(B);
  Predicate pred = OK;
  Predicate pred2 = ALRIGHT;
  Formula fpred = formula_pred(pred, prinA);
  Formula fpred2 = formula_pred(pred2, prinB);
  Formula fsays1 = formula_says(prinA, fpred);
  Formula fsays2 = formula_says(prinA, fpred2);
  Formula f1;
  Formula f2;
  Proof p1;
  Proof p2;
  Proof p3;
  Proof p4;
  bool b;

  f1 = formula_signed(prinA, fpred);
  p1 = proof_signed(f1);
  p2 = proof_cp(p1);
  b = proof_eq(p1, p2);
  if (b != 1)
    printf("ERROR: signed proof cp: 1 == %u\n", b);

  f1 = formula_confirms(prinA, fpred);
  p1 = proof_confirms(f1);
  p2 = proof_cp(p1);
  b = proof_eq(p1, p2);
  if (b != 1)
    printf("ERROR: confirms proof cp: 1 == %u\n", b);

  p1 = proof_assump(fpred);
  p2 = proof_cp(p1);
  b = proof_eq(p1, p2);
  if (b != 1)
    printf("ERROR: assump proof cp: 1 == %u\n", b);

  f1 = formula_says(prinB, fpred);
  p1 = proof_assump(fpred);
  p2 = proof_tauto(f1, p1);
  p3 = proof_cp(p2);
  b = proof_eq(p2, p3);
  if (b != 1)
    printf("ERROR: tauto proof cp: 1 == %u\n", b);

  f1 = formula_impl(fpred, fpred2);
  p1 = proof_assump(fpred2);
  p2 = proof_weaken_impl(f1, p1);
  p3 = proof_cp(p2);
  b = proof_eq(p2, p3);
  if (b != 1)
    printf("ERROR: weaken_impl proof cp: 1 == %u\n", b);

  f1 = formula_impl(fpred, fpred2);
  p1 = proof_assump(fpred);
  p2 = proof_assump(f1);
  p3 = proof_impl(fpred2, p1, p2);
  p4 = proof_cp(p3);
  b = proof_eq(p3, p4);
  if (b != 1)
    printf("ERROR: impl proof cp: 1 == %u\n", b);

  f1 = formula_confirms(prinA, fpred);
  p1 = proof_assump(f1);
  p2 = proof_assump(fsays1);
  p3 = proof_says_confirms(fsays2, p1, p2);
  p4 = proof_cp(p3);
  b = proof_eq(p3, p4);
  if (b != 1)
    printf("ERROR: says confirms proof cp: 1 == %u\n", b);

  f1 = formula_says(prinA, fpred);
  p1 = proof_assump(f1);
  p2 = proof_assump(fsays1);
  p3 = proof_says_says(fsays2, p1, p2);
  p4 = proof_cp(p3);
  b = proof_eq(p3, p4);
  if (b != 1)
    printf("ERROR: says says proof cp: 1 == %u\n", b);

  f1 = formula_signed(prinA, fpred);
  p1 = proof_assump(f1);
  p2 = proof_assump(fsays1);
  p3 = proof_says_signed(fsays2, p1, p2);
  p4 = proof_cp(p3);
  b = proof_eq(p3, p4);
  if (b != 1)
    printf("ERROR: says signed proof cp: 1 == %u\n", b);

  Pcpl pcplB = B;
  f1 = formula_abs(fpred);
  f2 = formula_says(prinA, f1);
  p1 = proof_assump(f2);
  p2 = proof_assump(fsays2);
  p3 = proof_says_spec(fsays2, pcplB, p1, p2);
  p4 = proof_cp(p3);
  b = proof_eq(p3, p4);
  if (b != 1)
    printf("ERROR: says spec proof cp: 1 == %u\n", b);
}
void test_proof_goal() {
  Principal prinA = principal_pcpl(A);
  Principal prinB = principal_pcpl(B);
  Predicate predOK = OK;
  Predicate predALRIGHT = ALRIGHT;
  Formula fpred1 = formula_pred(predOK, prinA);
  Formula fpred2 = formula_pred(predALRIGHT, prinB);
  Formula fsays1 = formula_says(prinA, fpred1);
  Formula fsays2 = formula_says(prinA, fpred2);
  Formula f1;
  Formula f2;
  Formula f3;
  Proof p1;
  Proof p2;
  Proof p3;
  bool b;

  f1 = formula_signed(prinA, fpred1);
  p1 = proof_signed(f1);
  f2 = proof_goal(p1);
  b = formula_eq(f1, f2);
  if (b != 1)
    printf("ERROR: signed proof goal: 1 == %u\n", b);

  f1 = formula_confirms(prinA, fpred1);
  p1 = proof_confirms(f1);
  f2 = proof_goal(p1);
  b = formula_eq(f1, f2);
  if (b != 1)
    printf("ERROR: confirms proof goal: 1 == %u\n", b);

  p1 = proof_assump(fpred1);
  f2 = proof_goal(p1);
  b = formula_eq(f1, f2);
  if (b != 1)
    printf("ERROR: assump proof goal: 1 == %u\n", b);

  f1 = formula_says(prinB, fpred1);
  p1 = proof_assump(fpred1);
  p2 = proof_tauto(f1, p1);
  f2 = proof_goal(p2);
  b = formula_eq(f1, f2);
  if (b != 1)
    printf("ERROR: tauto proof goal: 1 == %u\n", b);

  f1 = formula_impl(fpred1, fpred2);
  p1 = proof_assump(fpred2);
  p2 = proof_weaken_impl(f1, p1);
  f2 = proof_goal(p2);
  b = formula_eq(f1, f2);
  if (b != 1)
    printf("ERROR: weaken_impl proof cp: 1 == %u\n", b);

  f1 = formula_impl(fpred1, fpred2);
  p1 = proof_assump(fpred1);
  p2 = proof_assump(f1);
  p3 = proof_impl(fpred2, p1, p2);
  f2 = proof_goal(p3);
  b = formula_eq(fpred2, f2);
  if (b != 1)
    printf("ERROR: impl proof cp: 1 == %u\n", b);

  f1 = formula_confirms(prinA, fpred1);
  p1 = proof_assump(f1);
  p2 = proof_assump(fsays1);
  p3 = proof_says_confirms(fsays2, p1, p2);
  f2 = proof_goal(p3);
  b = formula_eq(fsays2, f2);
  if (b != 1)
    printf("ERROR: says confirms proof cp: 1 == %u\n", b);

  f1 = formula_says(prinA, fpred1);
  p1 = proof_assump(f1);
  p2 = proof_assump(fsays1);
  p3 = proof_says_says(fsays2, p1, p2);
  f2 = proof_goal(p3);
  b = formula_eq(fsays2, f2);
  if (b != 1)
    printf("ERROR: says says proof cp: 1 == %u\n", b);

  f1 = formula_signed(prinA, fpred1);
  p1 = proof_assump(f1);
  p2 = proof_assump(fsays1);
  p3 = proof_says_signed(fsays2, p1, p2);
  f2 = proof_goal(p3);
  b = formula_eq(fsays2, f2);
  if (b != 1)
    printf("ERROR: says signed proof cp: 1 == %u\n", b);

  Pcpl pcplB = B;
  f1 = formula_abs(fpred1);
  f2 = formula_says(prinA, f1);
  p1 = proof_assump(f2);
  p2 = proof_assump(fsays2);
  p3 = proof_says_spec(fsays2, pcplB, p1, p2);
  f3 = proof_goal(p3);
  b = formula_eq(fsays2, f3);
  if (b != 1)
    printf("ERROR: says spec proof cp: 1 == %u\n", b);
}

void test_proof_check_assump() {
  Context c = context_alloc(1);
  Principal prinA = principal_pcpl(A);
  Predicate pred = OK;
  Formula fpred = formula_pred(pred, prinA);
  Proof pf = proof_assump(fpred);
  bool b;

  push(c, fpred);
  b = proof_check(fpred, pf, c);
  if (b != 1)
    printf("ERROR: assump proof check: 1 == %u\n", b);

  b = proof_check(fpred, pf, NULL);
  if (b != 0)
    printf("ERROR: assump proof check (bad context): 0 == %u\n", b);
}

void test_proof_check_signed() {
  Principal prinA = principal_pcpl(A);
  Principal prinB = principal_pcpl(B);
  Predicate pred = OK;
  Formula fpred = formula_pred(pred, prinA);
  Formula f = formula_signed(prinA, fpred);
  Proof p = proof_signed(f);
  bool b = proof_check(f, p, NULL);
  if (b != 1)
    printf("ERROR: signed proof check: 1 == %u\n", b);

  Formula f2 = formula_signed(prinB, fpred);
  p = proof_signed(f2);
  printf("Expected error:\n");
  b = proof_check(f, p, NULL);
  printf(":End expected\n\n");
  if (b != 0)
    printf("ERROR: signed proof check (bad): 0 == %u\n", b);
}

void test_proof_check_confirms() {
  Principal prinA = principal_pcpl(A);
  Predicate pred = OK;
  Formula fpred = formula_pred(pred, prinA);
  Formula f = formula_confirms(prinA, fpred);
  Proof p = proof_confirms(f);
  bool b = proof_check(f, p, NULL);
  if (b != 1)
    printf("ERROR: confirms proof check: 1 == %u\n", b);

  Formula f2 = formula_signed(prinA, fpred);
  printf("Expected error:\n");
  b = proof_check(f2, p, NULL);
  printf(":End expected\n\n");
  if (b != 0)
    printf("ERROR: signed/confirms proof check: 0 == %u\n", b);
}

void test_proof_check_tauto() {
  Principal prinA = principal_pcpl(A);
  Principal prinB = principal_pcpl(B);
  Predicate pred = OK;
  Formula fpred = formula_pred(pred, prinA);
  Formula f1 = formula_says(prinB, fpred);
  Proof p1 = proof_assump(fpred);
  Proof p2 = proof_tauto(f1, p1);

  Context c = context_alloc(1);
  push(c, fpred);

  bool b = proof_check(f1, p2, c);
  if (b != 1)
    printf("ERROR: tauto proof check: 1 == %u\n", b);

  Formula fpred2 = formula_pred(pred, prinB);
  f1 = formula_says(prinB, fpred2);
  p1 = proof_assump(fpred);
  p2 = proof_tauto(f1, p1);
  printf("Expected error:\n");
  b = proof_check(fpred, p2, c);
  printf(":End expected\n\n");
  if (b != 0)
    printf("ERROR: tauto proof check (bad): 0 == %u\n", b);
}

void test_proof_check_weaken_impl() {
  Principal prinA = principal_pcpl(A);
  Principal prinB = principal_pcpl(B);
  Predicate predOK = OK;
  Predicate predALRIGHT = ALRIGHT;
  Formula fpred1 = formula_pred(predOK, prinA);
  Formula fpred2 = formula_pred(predALRIGHT, prinB);
  Formula f1 = formula_impl(fpred1, fpred1);
  Proof p1 = proof_assump(fpred1);
  Proof p2 = proof_weaken_impl(f1, p1);
  bool b = proof_check(f1, p2, NULL);
  if (b != 1)
    printf("ERROR: weaken_impl proof check: 1 == %u\n", b);
}

void test_proof_check_impl() {
  Principal prinA = principal_pcpl(A);
  Principal prinB = principal_pcpl(B);
  Predicate predOK = OK;
  Predicate predALRIGHT = ALRIGHT;
  Formula fpred1 = formula_pred(predOK, prinA);
  Formula fpred2 = formula_pred(predALRIGHT, prinB);
  Formula f1 = formula_impl(fpred1, fpred2);
  Proof p1 = proof_assump(fpred1);
  Proof p2 = proof_assump(f1);
  Proof p3 = proof_impl(fpred2, p1, p2);
  Context c = context_alloc(10);
  push(c, f1);
  push(c, fpred1);
  bool b = proof_check(fpred2, p3, c);
  if (b != 1)
    printf("ERROR: impl proof check: 1 == %u\n", b);
}

void test_proof_check_says_confirms() {
  Principal prinA = principal_pcpl(A);
  Principal prinB = principal_pcpl(B);
  Predicate predOK = OK;
  Predicate predALRIGHT = ALRIGHT;
  Formula f1 = formula_pred(predOK, prinA);
  Formula f2 = formula_cp(f1);

  Formula Asays1 = formula_says(prinA, f1);
  Formula Asays2 = formula_says(prinA, f2);
  Formula Aconfirms1 = formula_confirms(prinA, f1);
  Proof p1 = proof_confirms(Aconfirms1);
  Proof p_f1 = proof_assump(f1);
  Proof p2 = proof_tauto(Asays2, p_f1);
  Proof p3 = proof_says_confirms(Asays2, p1, p2);
  Context c = context_alloc(10);
  bool b = proof_check(Asays2, p3, NULL);
  if (b != 1)
    printf("ERROR: says_confirms proof check: 1 == %u\n", b);
}

void test_proof_check_says_signed() {
  Principal prinA = principal_pcpl(A);
  Principal prinB = principal_pcpl(B);
  Predicate predOK = OK;
  Predicate predALRIGHT = ALRIGHT;
  Formula f1 = formula_pred(predOK, prinA);
  Formula f2 = formula_cp(f1);

  Formula Asays1 = formula_says(prinA, f1);
  Formula Asays2 = formula_says(prinA, f2);
  Formula Asigned1 = formula_signed(prinA, f1);
  Proof p1 = proof_signed(Asigned1);
  Proof p_f1 = proof_assump(f1);
  Proof p2 = proof_tauto(Asays2, p_f1);
  Proof p3 = proof_says_signed(Asays2, p1, p2);
  bool b = proof_check(Asays2, p3, NULL);
  if (b != 1)
    printf("ERROR: says_signed proof check: 1 == %u\n", b);
}

void test_proof_check_says_says() {

}

void test_proof_check_says_spec() {

}

void test_proof_check() {
  test_proof_check_assump();
  test_proof_check_signed();
  test_proof_check_confirms();
  test_proof_check_tauto();
  test_proof_check_weaken_impl();
  test_proof_check_impl();
  test_proof_check_says_confirms();
  test_proof_check_says_signed();
}

int main() {
//  printall();
  printf("Starting tests\n\n");
  test_principal_eq();
  test_principal_cp();
  test_principal_subst();
  test_formula_eq();
  test_formula_cp();
  test_formula_subst();
  test_proof_eq();
  test_proof_check();
  printf("\nFinished tests\n");

  return 0;
}
