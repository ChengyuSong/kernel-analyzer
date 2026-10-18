// t_cells_union_addr_typed.c — (C', Fable 2026-10-17): a store into a union
// whose value is a constant address inside a global with debug info
// (&tab1[1], an S1) is typed by the address's debug type: the one member
// with an S1 * there (a). The read of member b (typed by its local) then
// excludes it by name. At the commit before the store was of no member
// (#?) and every read of the slot read it: f1 reached the b read.
// KAFLAGS: --cfl-rule-report=/dev/stdout
// LOG: T ASSUMPTION a store over union E.u typed as member a by its value's debug type \(S1 \*, a constant address inside tab1\): wa: store ptr getelementptr
#include <stdlib.h>
struct S1 { void (*f)(void); };
struct S2 { void (*g)(void); };
struct E {
  int kind;
  union {
    struct { void *next; struct S1 *p; } a;
    struct { void *next; struct S2 *q; } b;
  } u;
};
void f1(void) {}
void f2(void) {}
struct S1 tab1[2] = {{f1}, {f1}};
struct S2 tab2[2] = {{f2}, {f2}};
__attribute__((noinline)) void wa(struct E *e) { e->u.a.p = &tab1[1]; }
__attribute__((noinline)) void wb(struct E *e, struct S2 *s) { e->u.b.q = s; }
__attribute__((noinline)) void use(struct E *e) {
  struct S2 *s = e->u.b.q;
  s->g(); // CHECK: f2 CHECK-NOT: f1
}
int main(int argc, char **argv) {
  struct E *e = malloc(sizeof *e);
  (void)argv;
  if (argc > 1) wa(e); else wb(e, &tab2[0]);
  use(e);
  return 0;
}
