// t_cells_union_voidptr_write.c — Fable 2026-10-17: a union member declared
// `void *` is the program's generic view of the slot (bfd's tdata.any). C
// makes void * assignment-compatible with every object pointer, so its
// writes are compatible with every member's reads. Here the object arrives
// only through `any` (as `abfd->tdata.any = bfd_zalloc (...)`) and is
// filled and called through `a`. At the commit before, the census keyed the
// write by member any and the reads of a (no tag test: UNCHECKED, keyed by
// their own member) did not see it: no f1. The write of b still reaches no
// read of a.
// LOG: UnionKeys:   struct.bfd\+8.any: 1 writes, 0 reads
#include <stdlib.h>
struct A { void (*fp)(void); };
struct B { void (*gp)(void); };
struct bfd {
  int x;
  union { void *any; struct A *a; struct B *b; } tdata;
};
void f1(void) {}
void f2(void) {}
void *zalloc(size_t n) { return calloc(1, n); } // as bfd_zalloc: a body, void *
void mk(struct bfd *d) { d->tdata.any = zalloc(sizeof(struct A)); }
void fill(struct bfd *d) { d->tdata.a->fp = f1; }
void call(struct bfd *d) {
  d->tdata.a->fp(); // CHECK: f1 CHECK-NOT: f2
}
void setb(struct bfd *d) {
  struct B *n = malloc(sizeof *n);
  n->gp = f2;
  d->tdata.b = n;
}
int main(int argc, char **argv) {
  struct bfd *d = malloc(sizeof *d);
  if (argc > 1) { mk(d); fill(d); call(d); }
  else setb(d);
  return 0;
}
