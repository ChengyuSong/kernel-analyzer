// t_cells_union_embed_typed.c — R2 (Fable 2026-10-17): a pointer to a struct
// that embeds the field's pointee at offset 0 (`(struct E *) x`, x a
// struct XE * whose first member is a struct E: binutils' `(struct
// bfd_link_hash_entry *) hi`) types the store as the member whose field
// points to E (i). Before, no member's field there points to XE: a write
// of no member (#?), read by every read of the slot, so the XE object
// reached the d read and its first word (root.cb = f2) was called.
// KAFLAGS: --cfl-rule-report=/dev/stdout
// LOG: T ASSUMPTION a store over union E.u typed member i by its value's type XE \*, which embeds E at offset 0: wi: store ptr
#include <stdlib.h>
struct S1 { void (*f)(void); };
struct E {
  void (*cb)(void);
  int type;
  union {
    struct { void *n; struct E *link; } i;
    struct { void *n; struct S1 *sec; } d;
  } u;
};
struct XE { struct E root; int extra; };
void f1(void) {}
void f2(void) {}
struct S1 s1 = {f1};
__attribute__((noinline)) void wd(struct E *e, struct S1 *s) { e->u.d.sec = s; }
__attribute__((noinline)) void wi(struct E *e, struct XE *x) { e->u.i.link = (struct E *)x; }
__attribute__((noinline)) void use(struct E *e) {
  struct S1 *s = e->u.d.sec;
  s->f(); // CHECK: f1 CHECK-NOT: f2
}
int main(int argc, char **argv) {
  struct E *e = malloc(sizeof *e);
  struct XE *x = malloc(sizeof *x);
  (void)argv;
  x->root.cb = f2;
  if (argc > 1) wd(e, &s1); else wi(e, x);
  use(e);
  return 0;
}
