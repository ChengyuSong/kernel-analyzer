// t_cells_union_voidptr_read.c — Fable 2026-10-17: a union member declared
// `void *` is the program's generic view of the slot (bfd's tdata.any). C
// makes void * assignment-compatible with every object pointer, so its
// reads are compatible with every member's writes. Here a read of `any`
// (as bfd_preserve_save's `preserve->tdata = abfd->tdata.any`) returns an
// object written only through `b`. At the commit before, the read was
// UNCHECKED, keyed by its own member any, and did not see the write of b:
// no f2.
// LOG: UnionKeys:   struct.bfd\+8.any: 0 writes, 1 reads
#include <stdlib.h>
struct A { void (*fp)(void); };
struct B { void (*gp)(void); };
struct bfd {
  int x;
  union { void *any; struct A *a; struct B *b; } tdata;
};
void f1(void) {}
void f2(void) {}
void seta(struct bfd *d) {
  struct A *n = malloc(sizeof *n);
  n->fp = f1;
  d->tdata.a = n;
}
void setb(struct bfd *d) {
  struct B *n = malloc(sizeof *n);
  n->gp = f2;
  d->tdata.b = n;
}
void callany(struct bfd *d) {
  void *p = d->tdata.any;
  ((struct B *)p)->gp(); // CHECK: f2
}
int main(int argc, char **argv) {
  struct bfd *d = malloc(sizeof *d);
  if (argc > 1) seta(d); else setb(d);
  callany(d);
  return 0;
}
