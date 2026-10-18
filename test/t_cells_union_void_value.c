// t_cells_union_void_value.c — (C', Fable 2026-10-17): a void * value names
// no member by layout. `e->u.b.q = mk(i)` stores a void * (C converts it to
// struct S2 *). The census types a store by its value, and member a has a
// void * field at that offset, so before it was typed a; the b read, typed
// b and keyed by its own member (wb's store is a b), excluded it: f3 lost,
// unsound. Now the store is of no member (#?), which every read reads.
#include <stdlib.h>
struct S2 { void (*g)(void); };
struct E {
  int kind;
  union {
    struct { void *next; void *p; } a;
    struct { void *next; struct S2 *q; } b;
  } u;
};
void f2(void) {}
void f3(void) {}
struct S2 tab2[2] = {{f2}, {f2}};
struct S2 tab3[2] = {{f3}, {f3}};
__attribute__((noinline)) void *mk(int i) { return &tab3[i & 1]; }
__attribute__((noinline)) void wb(struct E *e, struct S2 *s) { e->u.b.q = s; }
__attribute__((noinline)) void wv(struct E *e, int i) { e->u.b.q = mk(i); }
__attribute__((noinline)) void use(struct E *e) {
  struct S2 *s = e->u.b.q;
  s->g(); // CHECK: f2 f3
}
int main(int argc, char **argv) {
  struct E *e = malloc(sizeof *e);
  (void)argv;
  if (argc > 1) wb(e, &tab2[0]); else wv(e, argc);
  use(e);
  return 0;
}
