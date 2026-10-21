// t_cells_scalconffield.c -- A3 (Fable 2026-10-21): ruling A labels a
// block every creating site uses as one scalar an array of it, but a
// receiving field declared a struct pointer is struct evidence on the same
// object (coffcode.h:1121 at -O3: comdat = bfd_alloc(16), ->symbol stored
// through the result, ->name through a reload of the field, in an IR
// struct the linker merged coff_comdat_info into): a conflict,
// the site unlabeled with both candidates; never a label (row 3).
// CFLAGS: -O2
// LOG: 1 with conflicting labels \(of 1 allocations whose scalar label meets struct evidence, A3; 0 whose size is k x their label
// LOG: 0 arrays of a declared scalar
#include <stdlib.h>
typedef void (*fn)(void);
struct C { long sym; fn f; };     // the field's declared pointee (debug info only)
struct D { long a; fn g; };       // the same layout, the type the IR steps by
struct H { long k; struct C *c; };
void sfn(void) {}
struct H h, *hp = &h;
__attribute__((noinline)) void touch(void) { hp->k++; }
__attribute__((noinline)) void attach(void) {
  long *p = malloc(16);
  *p = 5;
  hp->c = (struct C *)p;
  touch(); // hp is reloaded after the call: another address for the field
  ((struct D *)hp->c)->g = sfn;
}
__attribute__((noinline)) void call(void) {
  ((struct D *)hp->c)->g(); // CHECK: sfn
}
int main(void) {
  attach();
  call();
  return 0;
}
