// t_cells_scalarbuf_read.c — ruling A, the read side: an S-typed read of
// the function pointer field through a pointer to the declared-scalar
// table reads what the imprecise struct write left there (the rule (b)
// row's cost: sound, counted).
// LOG: 1 arrays of a declared scalar
// (The read is in another function: a struct read in the creating
// function is a struct use there, and the site is not scalar-only.)
#include <stdlib.h>
typedef void (*fn)(void);
struct S { long a; fn f; long b; };
void sfn(void) {}
float *table;
struct S *obj;
__attribute__((noinline)) void *pick(int k) { return k ? (void *)table : (void *)obj; }
__attribute__((noinline)) void callt(void) {
  ((struct S *)table)->f(); // CHECK: sfn
}
int main(int argc, char **argv) {
  float *t = malloc(64 * sizeof(float));
  for (int i = 0; i < 64; i++) t[i] = i * 0.5f;
  table = t;
  obj = malloc(sizeof(struct S));
  struct S *p = pick(argc);
  p->f = sfn;
  callt();
  return 0;
}
