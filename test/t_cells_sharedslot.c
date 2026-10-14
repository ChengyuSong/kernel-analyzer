// t_cells_sharedslot.c — receiver kind vs following (plan 3.53, Fable
// 2026-10-13): a variable declared float * receives two allocations (its
// slot holds both), so its uses are not followed for either block, but
// its declaration still makes each an array of float at mint; a struct
// written through an imprecise pointer is then the declared-scalar row,
// not a label.
// LOG: 2 arrays of a declared scalar
// LOG: 2 declared through a shared slot
#include <stdlib.h>
typedef void (*fn)(void);
struct S { long a; fn f; long b; };
void sfn(void) {}
float *t1, *t2;
struct S *obj;
__attribute__((noinline)) void *pick(int k) { return k ? (void *)t2 : (void *)obj; }
__attribute__((noinline)) void make(int n) {
  float *t = malloc(n * sizeof(float));
  t1 = t;
  t = malloc(2 * n * sizeof(float));
  t2 = t;
}
int main(int argc, char **argv) {
  make(argc + 4);
  obj = malloc(sizeof(struct S));
  struct S *p = pick(argc);
  p->f = sfn;
  obj->f(); // CHECK: sfn
  return (int)t1[0];
}
