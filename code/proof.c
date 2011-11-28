#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <proof.h>
#include <formula.h>

bool proof_check(Formula f, Proof pf);

void signed_r_print(Signed_r signed_r){
	printf("$\\trfrac[\\;signed]{\\rtcheck}{");
	formula_print(signed_r.goal);
	printf("}$");
}

void confirms_r_print(Confirms_r confirms_r){
	printf("$\\trfrac[\\;confirms]{\\rtcheck}{");
	formula_print(confirms_r.goal);
	printf("}$");
}

void assump_r_print(Assump_r assump_r){
	printf("$\\trfrac[\\;init]{\\rtcheck}{");
	formula_print(assump_r.goal);
	printf("}$");
}

void tauto_r_print(Tauto_r tauto_r) {
	printf("$\\trfrac[\\;tauto]{");
	proof_print(tauto_r.proof);
	printf("}{");
	formula_print(tauto_r.goal);
	printf("}$");
}

void weaken_impl_r_print(Weaken_Impl_r weaken_impl_r){
	printf("$\\trfrac[\\;weaken impl]{");
	proof_print(weaken_impl_r.proof);
	printf("}{");
	formula_print(weaken_impl_r.goal);
	printf("}$");
}

void impl_r_print(Impl_r impl_r){
	printf("$\\trfrac[\\;impl]{");
	proof_print(impl_r.pf1);
	printf(" \\quad ");
	proof_print(impl_r.pf2);
	printf("}{");
	formula_print(impl_r.goal);
	printf("}$");
}

void says_confirms_r_print(Says_Confirms_r says_confirms_r){
	printf("$\\trfrac[\\;conf]{");
	proof_print(says_confirms_r.pf1);
	printf(" \\quad ");
	proof_print(says_confirms_r.pf2);
	printf("}{");
	formula_print(says_confirms_r.goal);
	printf("}$");
}

void says_signed_r_print(Says_Signed_r says_signed_r){
	printf("$\\trfrac[\\;sign]{");
	proof_print(says_signed_r.pf1);
	printf(" \\quad ");
	proof_print(says_signed_r.pf2);
	printf("}{");
	formula_print(says_signed_r.goal);
	printf("}$");
}

void says_says_r_print(Says_Says_r says_says_r){
	printf("$\\trfrac[\\;says]{");
	proof_print(says_says_r.pf1);
	printf(" \\quad ");
	proof_print(says_says_r.pf2);
	printf("}{");
	formula_print(says_says_r.goal);
	printf("}$");
}

void says_spec_r_print(Says_Spec_r says_spec_r){
	printf("$\\trfrac[\\;spec]{");
	proof_print(says_spec_r.pf1);
	printf(" \\quad %u \\quad", says_spec_r.p);
	proof_print(says_spec_r.pf2);
	printf("}{");
	formula_print(says_spec_r.goal);
	printf("}$");
}

void proof_print(Proof pf){
	  switch (pf->type) {
	  case SIGNED_R: signed_r_print(pf->r.signed_r); return;
	  case CONFIRMS_R: confirms_r_print(pf->r.confirms_r); return;
	  case ASSUMP_R: assump_r_print(pf->r.assump_r); return;
	  case TAUTO_R: tauto_r_print(pf->r.tauto_r); return;
	  case WEAKEN_IMPL_R: weaken_impl_r_print(pf->r.weaken_impl_r); return;
	  case IMPL_R: impl_r_print(pf->r.impl_r); return;
	  case SAYS_CONFIRMS_R: says_confirms_r_print(pf->r.says_confirms_r); return;
	  case SAYS_SIGNED_R: says_signed_r_print(pf->r. says_signed_r); return;
	  case SAYS_SAYS_R: says_says_r_print(pf->r.says_says_r); return;
	  case SAYS_SPEC_R: says_spec_r_print(pf->r.says_spec_r); return;
	  default: printf("FORMULA UNDEFINED"); return;
	  }
}

Proof proof_cp(Proof r){
	Proof newr = malloc(sizeof(struct proof));
	if(newr == NULL) return newr;
	newr->type = r->type;

	switch (r->type){
	case SIGNED_R:
		newr->r.signed_r.goal = formula_cp(r->r.signed_r.goal);
		if(newr->r.signed_r.goal == NULL) goto freenewr;
		return newr;
	case CONFIRMS_R:
		newr->r.confirms_r.goal = formula_cp(r->r.confirms_r.goal);
		if(newr->r.confirms_r.goal == NULL) goto freenewr;
		return newr;
	case ASSUMP_R:
		newr->r.assump_r.goal = formula_cp(r->r.assump_r.goal);
		if(newr->r.assump_r.goal == NULL) goto freenewr;
		return newr;
	case TAUTO_R:
		newr->r.tauto_r.goal = formula_cp(r->r.tauto_r.goal);
		if(newr->r.tauto_r.goal == NULL) goto freenewr;

		newr->r.tauto_r.proof = proof_cp(r->r.tauto_r.proof);
		if(newr->r.tauto_r.proof == NULL){
			free(newr->r.tauto_r.goal);
			goto freenewr;
		}
		return newr;
	case WEAKEN_IMPL_R:
		newr->r.weaken_impl_r.goal = formula_cp(r->r.weaken_impl_r.goal);
		if(newr->r.weaken_impl_r.goal == NULL) goto freenewr;

		newr->r.weaken_impl_r.proof = proof_cp(r->r.weaken_impl_r.proof);
		if(newr->r.weaken_impl_r.proof == NULL){
			free(newr->r.weaken_impl_r.goal);
			goto freenewr;
		}
		return newr;
	case IMPL_R:
		newr->r.impl_r.goal = formula_cp(r->r.impl_r.goal);
		if(newr->r.impl_r.goal == NULL) goto freenewr;

		newr->r.impl_r.pf1 = proof_cp(r->r.impl_r.pf1);
		if(newr->r.impl_r.pf1 == NULL){
			free(newr->r.impl_r.goal);
			goto freenewr;
		}

		newr->r.impl_r.pf2 = proof_cp(r->r.impl_r.pf2);
		if(newr->r.impl_r.pf2 == NULL){
			free(newr->r.impl_r.pf1);
			free(newr->r.impl_r.goal);
			goto freenewr;
		}
		return newr;
	case SAYS_CONFIRMS_R:
		newr->r.says_confirms_r.goal = formula_cp(r->r.says_confirms_r.goal);
		if(newr->r.says_confirms_r.goal == NULL) goto freenewr;

		newr->r.impl_r.pf1 = proof_cp(r->r.impl_r.pf1);
		if(newr->r.impl_r.pf1 == NULL){
			free(newr->r.impl_r.goal);
			goto freenewr;
		}

		newr->r.impl_r.pf2 = proof_cp(r->r.impl_r.pf2);
		if(newr->r.impl_r.pf2 == NULL){
			free(newr->r.impl_r.pf1);
			free(newr->r.impl_r.goal);
			goto freenewr;
		}
		return newr;
	case SAYS_SIGNED_R:
		newr->r.says_signed_r.goal = formula_cp(r->r.says_signed_r.goal);
		if(newr->r.says_signed_r.goal == NULL) goto freenewr;

		newr->r.says_signed_r.pf1 = proof_cp(r->r.says_signed_r.pf1);
		if(newr->r.says_signed_r.pf1 == NULL){
			free(newr->r.says_signed_r.goal);
			goto freenewr;
		}

		newr->r.says_signed_r.pf2 = proof_cp(r->r.says_signed_r.pf2);
		if(newr->r.says_signed_r.pf2 == NULL){
			free(newr->r.says_signed_r.pf1);
			free(newr->r.says_signed_r.goal);
			goto freenewr;
		}
		return newr;
	case SAYS_SAYS_R:
		newr->r.says_says_r.goal = formula_cp(r->r.says_says_r.goal);
		if(newr->r.says_says_r.goal == NULL) goto freenewr;

		newr->r.says_says_r.pf1 = proof_cp(r->r.says_says_r.pf1);
		if(newr->r.says_says_r.pf1 == NULL){
			free(newr->r.says_says_r.goal);
			goto freenewr;
		}

		newr->r.says_says_r.pf2 = proof_cp(r->r.says_says_r.pf2);
		if(newr->r.says_says_r.pf2 == NULL){
			free(newr->r.says_says_r.pf1);
			free(newr->r.says_says_r.goal);
			goto freenewr;
		}
		return newr;
	case SAYS_SPEC_R:
		newr->r.says_spec_r.goal = formula_cp(r->r.says_spec_r.goal);
		if(newr->r.says_spec_r.goal == NULL) goto freenewr;

		newr->r.says_spec_r.p = r->r.says_spec_r.p;

		newr->r.says_spec_r.pf1 = proof_cp(r->r.says_spec_r.pf1);
		if(newr->r.says_spec_r.pf1 == NULL){
			free(newr->r.says_spec_r.goal);
			goto freenewr;
		}

		newr->r.says_spec_r.pf2 = proof_cp(r->r.says_spec_r.pf2);
		if(newr->r.says_spec_r.pf2 == NULL){
			free(newr->r.says_spec_r.pf1);
			free(newr->r.says_spec_r.goal);
			goto freenewr;
		}
		return newr;
	default:
		return NULL;
	}

freenewr:
	free(newr);
	return NULL;
}

Formula proof_goal(Proof pf) {
	switch(pf->type){
	case SIGNED_R: return formula_cp(pf->r.signed_r.goal);
	case CONFIRMS_R: return formula_cp(pf->r.confirms_r.goal);
	case ASSUMP_R: return formula_cp(pf->r.assump_r.goal);
	case TAUTO_R: return formula_cp(pf->r.tauto_r.goal);
	case WEAKEN_IMPL_R: return formula_cp(pf->r.weaken_impl_r.goal);
	case IMPL_R: return formula_cp(pf->r.impl_r.goal);
	case SAYS_CONFIRMS_R: return formula_cp(pf->r.says_confirms_r.goal);
	case SAYS_SIGNED_R: return formula_cp(pf->r.says_signed_r.goal);
	case SAYS_SAYS_R: return formula_cp(pf->r.says_says_r.goal);
	case SAYS_SPEC_R:return formula_cp(pf->r.says_spec_r.goal);
	default: return NULL;
	}
}

// Constructor
Proof proof_signed(Formula goal) {
  Proof p = malloc(sizeof(struct proof));
  if (p == NULL) return p;

  p->type = SIGNED_R;
  p->r.signed_r.goal = formula_cp(goal);
  if (p->r.signed_r.goal == NULL) goto freep;

  return p;

freep:
  free(p);
  return NULL;
}

Proof proof_confirms(Formula goal) {
  Proof p = malloc(sizeof(struct proof));
  if (p == NULL) return p;

  p->type = CONFIRMS_R;
  p->r.confirms_r.goal = formula_cp(goal);
  if (p->r.confirms_r.goal == NULL) goto freep;

  return p;

freep:
  free(p);
  return NULL;
}

Proof proof_assump(Formula goal) {
  Proof p = malloc(sizeof(struct proof));
  if (p == NULL) return p;

  p->type = ASSUMP_R;
  p->r.assump_r.goal = formula_cp(goal);
  if (p->r.assump_r.goal == NULL) goto freep;

  return p;

freep:
  free(p);
  return NULL;
}

Proof proof_tauto(Formula goal, Proof proof) {
  Proof p = malloc(sizeof(struct proof));
  if (p == NULL) return p;

  p->type = TAUTO_R;
  p->r.tauto_r.goal = formula_cp(goal);
  if (p->r.tauto_r.goal == NULL) goto freep;

  p->r.tauto_r.proof = proof_cp(proof);
  if (p->r.tauto_r.proof == NULL) goto freegoal;

  return p;

freegoal:
  free(p->r.tauto_r.goal);
freep:
  free(p);
  return NULL;
}

Proof proof_weaken_impl(Formula goal, Proof proof) {
  Proof p = malloc(sizeof(struct proof));
  if (p == NULL) return p;

  p->type = WEAKEN_IMPL_R;
  p->r.weaken_impl_r.goal = formula_cp(goal);
  if (p->r.weaken_impl_r.goal == NULL) goto freep;

  p->r.weaken_impl_r.proof = proof_cp(proof);
  if (p->r.weaken_impl_r.proof == NULL) goto freegoal;

  return p;

freegoal:
  free(p->r.weaken_impl_r.goal);
freep:
  free(p);
  return NULL;
}

Proof proof_impl(Formula goal, Proof proof1, Proof proof2) {
  Proof p = malloc(sizeof(struct proof));
  if (p == NULL) return p;

  p->type = IMPL_R;
  p->r.impl_r.goal = formula_cp(goal);
  if (p->r.impl_r.goal == NULL) goto freep;

  p->r.impl_r.pf1 = proof_cp(proof1);
  if (p->r.impl_r.pf1 == NULL) goto freegoal;

  p->r.impl_r.pf2 = proof_cp(proof2);
  if (p->r.impl_r.pf2 == NULL) goto freeproof1;

  return p;

freeproof1:
  free(p->r.impl_r.pf1);
freegoal:
  free(p->r.impl_r.goal);
freep:
  free(p);
  return NULL;
}

Proof proof_says_confirms(Formula goal, Proof proof1, Proof proof2) {
  Proof p = malloc(sizeof(struct proof));
  if (p == NULL) return p;

  p->type = SAYS_CONFIRMS_R;
  p->r.says_confirms_r.goal = formula_cp(goal);
  if (p->r.says_confirms_r.goal == NULL) goto freep;

  p->r.says_confirms_r.pf1 = proof_cp(proof1);
  if (p->r.says_confirms_r.pf1 == NULL) goto freegoal;

  p->r.says_confirms_r.pf2 = proof_cp(proof2);
  if (p->r.says_confirms_r.pf2 == NULL) goto freeproof1;

  return p;

freeproof1:
  free(p->r.says_confirms_r.pf1);
freegoal:
  free(p->r.says_confirms_r.goal);
freep:
  free(p);
  return NULL;
}

Proof proof_says_signed(Formula goal, Proof proof1, Proof proof2) {

}

Proof proof_says_says(Formula goal, Proof proof1, Proof proof2) {

}

Proof proof_says_spec(Formula goal, Pcpl p, Proof proof1, Proof proof2) {

}
