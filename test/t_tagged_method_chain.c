// t_tagged_method_chain.c — plan 3.54 (b): terms along the receiver. A
// codec saves the method it replaces (its parent) in its state and calls
// it with the receiver (libtiff's vsetparent chain). Entering common
// through setA's parent call, t carries setA's term: t->data holds what
// installed setA. Without the channel that entry is "other" and common's
// read admits every writer (bfn too).
// PAIR: struct.TIFF+8 by +0
#include <stdlib.h>
struct TIFF { void (*vset)(struct TIFF *); void *data; };
struct S { void (*parent)(struct TIFF *); void (*fn)(void); };
void afn(void) {}
void bfn(void) {}
void common(struct TIFF *t) {
  struct S *h = t->data;
  if (h) h->fn(); // CHECK: afn CHECK-NOT: bfn
}
void setA(struct TIFF *t) {
  struct S *s = t->data;
  s->parent(t);
}
void setB(struct TIFF *t) {
  struct S *s = t->data;
  s->fn();
}
void defaultInit(struct TIFF *t) {
  t->data = NULL;
  t->vset = common;
}
void initA(struct TIFF *t) {
  struct S *s = malloc(sizeof *s);
  s->fn = afn;
  s->parent = t->vset;
  t->data = s;
  t->vset = setA;
}
void initB(struct TIFF *t) {
  struct S *s = malloc(sizeof *s);
  s->fn = bfn;
  s->parent = t->vset;
  t->data = s;
  t->vset = setB;
}
int main(int argc, char **argv) {
  struct TIFF *t = malloc(sizeof *t);
  defaultInit(t);
  if (argc > 1) initA(t); else initB(t);
  t->vset(t);
  return 0;
}
