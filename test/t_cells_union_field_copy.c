// t_cells_union_field_copy.c — (C'', Fable 2026-10-17): a store whose value
// is a load of the same union field of another object is a per-key copy:
// each fact keeps the member key it had at the source. cp copies u.def.sec
// from a to b (elfxx-x86.c:1934's shape); the census cannot type the
// stored value (a load from a union) and before the copy was a write of no
// member, read by every read: the S1 (f1) reached the i read through b.
// Now it keeps a's def key, and the i read (keyed by its own member)
// excludes it.
// KAFLAGS: --cfl-rule-report=/dev/stdout
// LOG: T ASSUMPTION a copy of union E.u\+8 between two objects keeps the source's member key under the store's own tag keys: cp: store ptr
#include <stdlib.h>
struct S1 { void (*f)(void); };
struct S2 { void (*g)(void); };
struct E {
  int type;
  union {
    struct { void *next; struct S1 *sec; } def;
    struct { void *next; struct S2 *link; } i;
  } u;
};
void f1(void) {}
void f2(void) {}
struct S1 s1 = {f1};
struct S2 s2 = {f2};
__attribute__((noinline)) void wdef(struct E *e, struct S1 *s) { e->u.def.sec = s; }
__attribute__((noinline)) void wi(struct E *e, struct S2 *s) { e->u.i.link = s; }
__attribute__((noinline)) void cp(struct E *a, struct E *b) { b->u.def.sec = a->u.def.sec; }
__attribute__((noinline)) void use(struct E *e) {
  struct S2 *s = e->u.i.link;
  s->g(); // CHECK: f2 CHECK-NOT: f1
}
int main(int argc, char **argv) {
  struct E *a = malloc(sizeof *a), *b = malloc(sizeof *b);
  (void)argv;
  wdef(a, &s1);
  if (argc > 1) wi(b, &s2); else cp(a, b);
  use(b);
  return 0;
}
