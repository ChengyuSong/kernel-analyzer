// t_cells_scalconfjoin.c -- A3 (Fable 2026-10-21): a struct GEP on a join
// (phi, select) with the allocation among its incomings may step on the
// object: struct evidence against its scalar label (skb_ext_add: the
// refcount stored as an int, then struct skb_ext steps on a phi with the
// old extension). Evidence only, never a label: the step may be on the
// other incomings.
// CFLAGS: -O2
// LOG: 1 with conflicting labels \(of 1 allocations whose scalar label meets struct evidence, A3\)
// LOG: 0 arrays of a declared scalar
#include <stdlib.h>
typedef void (*fn)(void);
struct E { int refs; int pad; fn f; };
void efn(void) {}
struct E *old;
static inline void *newref(void) {
  int *r = malloc(sizeof(struct E));
  *r = 1;
  return r;
}
__attribute__((noinline)) struct E *ext(int fresh) {
  struct E *e = fresh ? newref() : old;
  e->f = efn;
  return e;
}
int main(int argc, char **argv) {
  struct E *e = ext(argc > 1);
  e->f(); // CHECK: efn
  return 0;
}
