// t_cells_onelabel_whyat.c — the one-label stop runs the --cfl-cell-why-at
// report before it exits (Fable 2026-10-15, log-only): a T node threaded
// through a shared list helper is stepped as K in gc; the stop explains why
// gc's nodes hold the T object. Only nodes holding a fact are described.
// KAFLAGS: --cfl-cell-one-label --cfl-cell-one-label-object=[struct.T --cfl-cell-one-label-max=1 --cfl-cell-why=[struct.T --cfl-cell-why-at=gc:
// LOG: NAME CONFLICT at pop [0-9]+: gc: .* now stepped as struct.K
// LOG: why-at gc: .*: a class of [0-9]+ nodes
// LOG: why does gc: .* hold struct.T\+0 @0 of \{main::call malloc @[^ ]+ #[0-9]+ \[id #[0-9]+\] \[struct.T\]\}
// LOG: stopped at [0-9]+ pops \(one-label stop, 1 conflict\)
#include <stddef.h>
#include <stdlib.h>
struct node { struct node *l, *r; };
struct T { long t; struct node n; };
struct K { long s; struct node n; long k; };
struct node *R;
__attribute__((noinline)) struct node *nxt(struct node *p) { return p->r ? p->r : p->l; }
__attribute__((noinline)) void link(struct node *p) { p->r = R; R = p; }
long gc(void) {
  long s = 0;
  for (struct node *p = R; p; p = nxt(p)) {
    struct K *k = (struct K *)((char *)p - offsetof(struct K, n));
    s += k->k + k->s;
  }
  return s;
}
int main(void) {
  struct T *t = malloc(sizeof *t); t->t = 1; link(&t->n);
  struct K *k = malloc(sizeof *k); k->s = 2; link(&k->n);
  return (int)gc();
}
