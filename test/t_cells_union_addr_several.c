// t_cells_union_addr_several.c — (C'): a constant address whose debug type
// (an S1 *) fits two members at the store's offset (a.p and c.r) types no
// member: the store stays of no member (#?), read by every read of the
// slot, the b read included.
#include <stdlib.h>
struct S1 { void (*f)(void); };
struct S2 { void (*g)(void); };
struct E {
  int kind;
  union {
    struct { void *next; struct S1 *p; } a;
    struct { void *next; struct S2 *q; } b;
    struct { void *next; struct S1 *r; } c;
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
  s->g(); // CHECK: f1 f2
}
int main(int argc, char **argv) {
  struct E *e = malloc(sizeof *e);
  (void)argv;
  if (argc > 1) wa(e); else wb(e, &tab2[0]);
  use(e);
  return 0;
}
