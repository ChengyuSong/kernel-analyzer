// t_cells_chanconst.c — plan 3.54 (b): the solver's table of channel
// arguments is built over every call; a constant argument (&gbuf[3] to a
// bodiless function: a GEP the graph never saw) must not mint a solver
// node after the graph is fixed (1a9aa7e aborted on sqlite3 there).
#include <stdlib.h>
extern void ext(char *);
char gbuf[16];
struct TIFF { void (*vset)(struct TIFF *); void *data; };
struct S { void (*parent)(struct TIFF *); void (*fn)(void); };
void afn(void) {}
void bfn(void) {}
void common(struct TIFF *t) {
  struct S *h = t->data;
  if (h) h->fn(); // CHECK: afn
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
  ext(&gbuf[3]);
  return 0;
}
