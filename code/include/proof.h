#ifndef PROOF_H
#define PROOF_H

#include <formula.h>

typedef struct proof* Proof;

struct proof{

};

void proof_print(Proof pf);
bool proof_check(Proof pf, Formula f);
Proof proof_cp(Proof pf);
Formula proof_goal(Proof pf);

void test();

#endif
