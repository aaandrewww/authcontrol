#include <stdio.h>
#include <stdlib.h>
#include <context.h>

int push(Context c, Formula f) {
  if (c->topOfContext == c->size) {
    printf("Stack is full\n");
    return -1;
  }
  c->contextData[c->topOfContext] = f;
  c->topOfContext++;
  return 0;
}

Formula pop(Context c) {
  if (c->topOfContext == 0) {
    printf("Stack is empty\n");
    return NULL;
  }
  c->topOfContext--;
  return c->contextData[c->topOfContext];
}

Context context_alloc(uint32_t size) {
  Context c = malloc(sizeof(struct context));
  if (!c) {
    printf("Context allocation failed\n");
    return NULL;
  }

  c->size = size;
  c->topOfContext = 0;
  c->contextData = malloc(size * sizeof(struct formula));
  return c;
}

void context_free(Context c) {
  free(c->contextData);
  free(c);
}

bool member(Context c, Formula f){
  Formula ftemp;
  Context ctemp = context_cp(c);
  ftemp = pop(ctemp);

  while(ftemp){
    if(formula_eq(f, ftemp)){
      context_free(ctemp);
      return true;
    }
    pop(ctemp);
  }
  context_free(ctemp);
  return false;
}

Context context_cp(Context c){
  Context cret = context_alloc(c->size);
  int i = 0;

  while(i < c->topOfContext){
    cret->contextData[i] = formula_cp(c->contextData[i]);
    i++;
  }
  return cret;
}
