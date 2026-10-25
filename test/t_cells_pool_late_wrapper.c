// P-ord (Fable 2026-10-24): carve candidacy runs to a fixpoint with the
// confirmer's wrapper promotions. The pool's chunk comes from xget, a
// wrapper over malloc that no file row names: the confirmer promotes it in
// round 1, after the carve check has seen p->cur refilled only by a call it
// does not know as an allocation (a cursor). Round 2 re-runs the refill
// test, finds the candidate, and certifies the pool; pool_alloc is inlined,
// so each hand-out is its own carve site and object, and the two do not
// share fn. Before P-ord a and b are one object
// (xget's chunk) and the call reads both f and g.
// CFLAGS: -O3
#include <stdlib.h>
struct pool { char *cur; char *end; };
struct pool P; // external: a static one is split into scalars at -O3
__attribute__((noinline)) static void *xget(size_t n) { return malloc(n); }
__attribute__((noinline)) static void refill(struct pool *p) {
  p->cur = xget(4096);
  p->end = p->cur + 4096;
}
static inline __attribute__((always_inline)) void *pool_alloc(struct pool *p, size_t n) {
  if ((size_t)(p->end - p->cur) < n) refill(p);
  char *r = p->cur;
  p->cur = r + n;
  return r;
}
struct ent { void (*fn)(void); long x; };
void f(void) {}
void g(void) {}
int main(void) {
  struct ent *a = pool_alloc(&P, sizeof *a);
  struct ent *b = pool_alloc(&P, sizeof *b);
  a->fn = f;
  b->fn = g;
  a->fn(); // CHECK: f CHECK-NOT: g
  return 0;
}
// LOG: carve round 2: 1 new candidates .*: pool\+0
// LOG: pool pool\+0: first judged in round 2: POOL fields pool\+0; carves before-bump 2
// LOG: carve rounds: 2
