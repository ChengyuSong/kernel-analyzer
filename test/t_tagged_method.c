// t_tagged_method.c — plan 3.54: method-installed state. Two codecs each
// install a decode method and its state into one object (libtiff's
// tif_decoderow and tif_data); the dispatch t->decoderow(t) is the test:
// entering decodeA through it, t->data holds only what installed decodeA.
// PAIR: struct.TIFF+8 by +0
#include <stdlib.h>
struct TIFF { void (*decoderow)(struct TIFF *); void *data; };
struct A { void (*fn)(void); };
struct B { void (*fn)(void); };
void afn(void) {}
void bfn(void) {}
void decodeA(struct TIFF *t) {
  struct A *s = t->data;
  s->fn(); // CHECK: afn CHECK-NOT: bfn
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
  return 0;
}
