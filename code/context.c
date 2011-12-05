#include <stdio.h>
#include <stdlib.h>
#include <context.h>

void push(Context c, Formula f) {
  if (c->topOfContext == c->size) {
    printf("Stack is full\n");
    return;
  }
  c->contextData[c->topOfContext] = f;
  c->topOfContext++;
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

