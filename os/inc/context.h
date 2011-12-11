#ifndef CONTEXT_H_
#define CONTEXT_H_

#include <inc/types.h>
#include <inc/formula.h>

typedef struct context* Context;

struct context {
  uint32_t size;
  uint32_t topOfContext;
  Formula *contextData;
};

void push(Context c, Formula f);
Formula pop(Context c);
Context context_alloc(uint32_t size);
void context_free(Context c);
Context context_cp(Context c);
void context_print(Context c);
bool member(Context c, Formula f);

#endif /* CONTEXT_H_ */
