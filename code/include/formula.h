#ifndef FORMULA_H
#define FORMULA_H

#include <stdint.h>
#include <stdbool.h>

typedef uint32_t Var;
typedef char* Pcpl;
typedef char* Predicate;

typedef struct formula* Formula;
typedef struct principal* Principal;
typedef struct pred_formula Pred_f;
typedef struct impl_formula Impl_f;
typedef struct signed_formula Signed_f;
typedef struct says_formula Says_f;
typedef struct confirms_formula Confirms_f;
typedef struct abs_formula Abs_f;

enum prin_type{
	VAR,
	PCPL
};

struct principal{
	enum prin_type type;
	union {
	Var var;
	Pcpl pcpl;
	} prin;
};

enum formula_type{
	PRED_F,
	IMPL_F,
	SIGNED_F,
	SAYS_F,
	CONFIRMS_F,
	ABS_F
};

struct pred_formula {
	Predicate pred;
	Principal principal;
};

struct impl_formula {
	Formula formula1;
	Formula formula2;
};

struct signed_formula {
	Principal principal;
	Formula formula;
};

struct says_formula {
	Principal principal;
	Formula formula;
};

struct confirms_formula {
	Principal principal;
	Formula formula;
};

struct abs_formula {
	Formula formula;
};

struct formula{
	enum formula_type type;
	union {
		Pred_f pred_f;
		Impl_f impl_f;
		Signed_f signed_f;
		Says_f says_f;
		Confirms_f confirms_f;
		Abs_f abs_f;
	} form;
};

void principal_print(Principal p);
bool principal_eq(Principal p1, Principal p2);
Principal principal_cp(Principal p);
Principal principal_subst(Principal prin, Var v, Pcpl p);

void formula_print(Formula p);
bool formula_eq(Formula p1, Formula p2);
Formula formula_cp(Formula p);
Formula formula_subst(Formula prin, Var v, Pcpl p);

#endif
