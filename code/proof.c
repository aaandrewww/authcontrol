#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <proof.h>
#include <formula.h>

void proof_print(Proof pf);
bool proof_check(Formula f, Proof pf);

Rule rule_cp(Rule r){
	Rule newr = malloc(sizeof(struct rule));
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

Proof proof_cp(Proof pf){
	Proof newProof = malloc(sizeof(struct proof));
	int i, j;
	uint32_t max = NRULES; // TODO Why is the #define not usable as an loop variable?
	if (newProof == NULL) return newProof;

	newProof->goal = formula_cp(pf->goal);

	for (i = 0; i < max; ++i) {
		if(pf->rules[i] == NULL) break;
		newProof->rules[i] = rule_cp(pf->rules[i]);
		if(newProof->rules[i] == NULL) {
			for(j = 0; j < i; j++){
				free(newProof->rules[j]);
			}
			free(newProof);
			return NULL;
		}
	}
	return newProof;
}

Formula proof_goal(Proof pf) {
	return formula_cp(pf->goal);
}
