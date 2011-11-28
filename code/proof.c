#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <proof.h>
#include <formula.h>

bool proof_check(Formula f, Proof pf);

void proof_print(Proof pf){

}

void signed_r_print(Proof pf){
	printf("$\trfrac[\;signed]{\rtcheck}{\sign{A}{F}}$ \hfil");
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

	    char *newstring = malloc(strlen(r->r.says_spec_r.p)+1);
	    if (newstring == NULL) {
	    	free(newr->r.says_spec_r.goal);
	    	goto freenewr;
	    }
		newr->r.says_spec_r.p = newstring;
		strcpy(newstring, r->r.says_spec_r.p);

		newr->r.says_spec_r.pf1 = proof_cp(r->r.says_spec_r.pf1);
		if(newr->r.says_spec_r.pf1 == NULL){
			free(newstring);
			free(newr->r.says_spec_r.goal);
			goto freenewr;
		}

		newr->r.says_spec_r.pf2 = proof_cp(r->r.says_spec_r.pf2);
		if(newr->r.says_spec_r.pf2 == NULL){
			free(newstring);
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
	case SIGNED_R:
		return formula_cp(pf->r.signed_r.goal);
	case CONFIRMS_R:
		return formula_cp(pf->r.confirms_r.goal);
	case ASSUMP_R:
		return formula_cp(pf->r.assump_r.goal);
	case TAUTO_R:
		return formula_cp(pf->r.tauto_r.goal);
	case WEAKEN_IMPL_R:
		return formula_cp(pf->r.weaken_impl_r.goal);
	case IMPL_R:
		return formula_cp(pf->r.impl_r.goal);
	case SAYS_CONFIRMS_R:
		return formula_cp(pf->r.says_confirms_r.goal);
	case SAYS_SIGNED_R:
		return formula_cp(pf->r.says_signed_r.goal);
	case SAYS_SAYS_R:
		return formula_cp(pf->r.says_says_r.goal);
	case SAYS_SPEC_R:
		return formula_cp(pf->r.says_spec_r.goal);
	default:
		return NULL;
	}
}

// Constructor
Proof proof_signed(Formula goal) {

}

Proof proof_confirms(Formula goal) {

}

Proof proof_assump(Formula goal) {

}

Proof proof_tauto(Formula goal, Proof proof) {

}

Proof proof_weaken_impl(Formula goal, Proof proof) {

}

Proof proof_impl(Formula goal, Proof proof1, Proof proof2) {

}

Proof proof_says_confirms(Formula goal, Proof proof1, Proof proof2) {

}

Proof proof_says_signed(Formula goal, Proof proof1, Proof proof2) {

}

Proof proof_says_says(Formula goal, Proof proof1, Proof proof2) {

}

Proof proof_says_spec(Formula goal, Pcpl p, Proof proof1, Proof proof2) {

}
