// t_tagged_method_direct.c — plan 3.54: only the dispatch is a test. As
// t_tagged_method.c, plus a direct call decodeA(t) on an object initB may
// have set up: that entry carries no narrowing, so the read in decodeA
// admits both codecs' state.
// PAIR: struct.TIFF+8 by +0
#include <stdlib.h>
struct TIFF { void (*decoderow)(struct TIFF *); void *data; };
struct A { void (*fn)(void); };
struct B { void (*fn)(void); };
void afn(void) {}
void bfn(void) {}
void decodeA(struct TIFF *t) {
  struct A *s = t->data;
  s->fn(); // CHECK: afn bfn
}
void decodeB(struct TIFF *t) {
  struct B *s = t->data;
  s->fn();
}
void initA(struct TIFF *t) {
  struct A *s = malloc(sizeof *s);
  s->fn = afn;
  t->data = s;
  t->decoderow = decodeA;
}
void initB(struct TIFF *t) {
  struct B *s = malloc(sizeof *s);
  s->fn = bfn;
  t->data = s;
  t->decoderow = decodeB;
}
int main(int argc, char **argv) {
  struct TIFF *t = malloc(sizeof *t);
  if (argc > 1) initA(t); else initB(t);
  t->decoderow(t);
  decodeA(t);
  return 0;
}
