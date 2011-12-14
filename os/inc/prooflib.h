#ifndef PROOFLIB_H_
#define PROOFLIB_H_

#include <inc/proof.h>
#include <inc/formula.h>

// Constructors
Proof proof_signed(Formula goal);
Proof proof_confirms(Formula goal);
Proof proof_assump(Formula goal);
Proof proof_tauto(Formula goal, Proof proof);
Proof proof_weaken_impl(Formula goal, Proof proof);
Proof proof_impl(Formula goal, Proof proof1, Proof proof2);
Proof proof_says_confirms(Formula goal, Proof proof1, Proof proof2);
Proof proof_says_signed(Formula goal, Proof proof1, Proof proof2);
Proof proof_says_says(Formula goal, Proof proof1, Proof proof2);
Proof proof_says_spec(Formula goal, Pcpl p, Proof proof1, Proof proof2);

Proof signed_proof(Pcpl sayer, Formula f);
Proof says_from_assump(Pcpl sayer, Formula f);
Proof says_from_signed(Pcpl sayer, Formula f);
Proof says_from_confirms(Pcpl sayer, Formula f);
Formula approve(Pcpl pcpl, Predicate pred);
Proof approval_from_signed(Pcpl approver, Predicate pred, Pcpl pcpl);
Formula delegate(Pcpl pcpl, Predicate pred);
Formula delegate_signed(Pcpl a, Pcpl b, Predicate p);
Proof delegate_from_signed(Pcpl a, Pcpl b, Predicate p);
Proof use_delegation(Pcpl a, Pcpl b, Pcpl c, Predicate p, Proof dpf, Proof apf);

#endif /* PROOFLIB_H_ */
