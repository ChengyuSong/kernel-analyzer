// t_cells_whyat_alts.c — --cfl-cell-why-at splits on '|' (XW, Fable
// 2026-10-26): a node is asked when any alternative matches its
// description, and each alternative no node matches is named. Before XW
// the whole pattern was one substring and matched nothing. The program is
// t_cells_onelabel_whyat.c's (a T node through a shared list helper,
// stepped as K in gc); the stop asks gc's and main's nodes.
// KAFLAGS: --cfl-cell-one-label --cfl-cell-one-label-object=[struct.T --cfl-cell-one-label-max=1 --cfl-cell-why=[struct.T --cfl-cell-why-at=gc:|main:|no_such_fn:
// LOG: why-at gc: .*: a class of [0-9]+ nodes
// LOG: why-at main: .*: a class of [0-9]+ nodes
// LOG: no node matches 'no_such_fn:'
// NOLOG: no node matches 'gc:
// NOLOG: no node matches 'main:'
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
