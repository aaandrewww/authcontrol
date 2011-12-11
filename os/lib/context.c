#include <inc/stdio.h>
#include <inc/lib.h>
#include <inc/context.h>
#include <inc/string.h>

// Push a new formula onto the Context stack.  Copies the formula.
void push(Context c, Formula f) {
  // If the push will overflow the given context double the size
  if (c->topOfContext == c->size) {
    uint32_t newSize = c->size * 2;
    Formula *f = (Formula *) malloc(newSize * sizeof(Formula));
    memcpy(f, c->contextData, c->size*sizeof(Formula));
    c->size = newSize;
    free(c->contextData);
    c->contextData = f;
  }
  Formula fCopy = formula_cp(f);
  c->contextData[c->topOfContext] = fCopy;
  c->topOfContext++;
}

Formula pop(Context c) {
  if (c == NULL)
    return NULL;

  if (c->topOfContext == 0)
    return NULL;

  c->topOfContext--;
  return c->contextData[c->topOfContext];
}

Context context_alloc(uint32_t size) {
  Context c = (Context) malloc(sizeof(struct context));
  if (!c) {
    cprintf("Context allocation failed\n");
    return NULL;
  }

  c->size = size;
  c->topOfContext = 0;
  c->contextData = (Formula *) malloc(size * sizeof(Formula));
  return c;
}

// Frees the context and all the formulas below the stack pointer.
// All these formulas are copies.
void context_free(Context c) {
  Formula f;
  f = pop(c);

  while (f) {
    formula_free(f);
    f = pop(c);
  }

  free(c->contextData);
  free(c);
}

bool member(Context c, Formula f) {
  if (c == NULL)
    return false;

  uint32_t i = 0;
  while (i < c->topOfContext) {
    if (formula_eq(f, c->contextData[i]))
      return true;
    i++;
  }
  return false;
}

// Deep copy of the context. Also copies all the formulas below the stack pointer.
Context context_cp(Context c) {
  if (c == NULL)
    return NULL;

  Context cret = context_alloc(c->size);
  uint32_t i = 0;

  while (i < c->topOfContext) {
    cret->contextData[i] = formula_cp(c->contextData[i]);
    i++;
  }
  cret->topOfContext = c->topOfContext;
  return cret;
}

void context_print(Context c) {
  if (c == NULL) {
    return;
  }
  uint32_t i = 0;
  while (i < c->topOfContext) {
    formula_print(c->contextData[i]);
    cprintf("\n");
    i++;
  }
}
