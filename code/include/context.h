#ifndef CONTEXT_H_
#define CONTEXT_H_

#include <stdint.h>
#include <formula.h>

typedef struct context* Context;

struct context {
  uint32_t size;
  uint32_t topOfContext;
  Formula *contextData;
};

int push(Context c, Formula f);
Formula pop(Context c);
Context context_alloc(uint32_t size);
void context_free();
Context context_cp(Context c);

#endif /* CONTEXT_H_ */
