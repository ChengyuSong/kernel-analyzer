// t_cells_scalarbuf.c — ruling A (plan 3.53, completes 1b): a buffer every
// creating site declares and uses as one scalar (a float table) is an
// array of that scalar from mint, so a struct written through an
// imprecise pointer reaching both the table and a struct does not label
// it: rule (b), "struct written into storage declared scalar", the flow
// kept (folded into the table's element cells). A call through the
// struct gives the function; an S-typed read through the table gives it
// too (the row's cost, sound).
// LOG: 1 arrays of a declared scalar
// LOG: struct written into storage declared scalar \(ruling A; folded into the array's element cells, flow kept\): [1-9]
#include <stdlib.h>
typedef void (*fn)(void);
struct S { long a; fn f; long b; };
void sfn(void) {}
float *table;
struct S *obj;
__attribute__((noinline)) void *pick(int k) { return k ? (void *)table : (void *)obj; }
int main(int argc, char **argv) {
  float *t = malloc(64 * sizeof(float));
  for (int i = 0; i < 64; i++) t[i] = i * 0.5f;
  table = t;
  obj = malloc(sizeof(struct S));
  struct S *p = pick(argc);
  p->f = sfn;          // the imprecise struct write
  obj->f();            // CHECK: sfn
  return (int)table[3];
}
