// t_cells_fresh_or_arg.c — item 4 (Fable 2026-10-17): a constructor that
// returns its argument or a fresh block (bfd_hash_newfunc's `if (entry ==
// NULL) entry = alloc (...); return entry;`) is inferred FRESH
// ALIAS(ret=arg0) BODY and applied per call site, and so are the derived
// constructors that return its result for their own block. Before, base's
// formal and return were shared by every caller: ctor1's block (f1)
// reached ctor2's result through base's return.
// LOG: ConfirmFresh: promoted base \[fresh-or-arg\]
// LOG: ConfirmFresh: LINE ctor2 FRESH ALIAS\(ret=arg0\) BODY
#include <stdlib.h>
struct E { void (*f)(void); long pad; };
void f1(void) {}
void f2(void) {}
__attribute__((noinline)) void *alloc(unsigned long n) { return malloc(n); }
__attribute__((noinline)) struct E *base(struct E *e) {
  if (e == NULL) e = alloc(sizeof *e);
  return e;
}
__attribute__((noinline)) struct E *ctor1(struct E *e) {
  if (e == NULL) e = alloc(sizeof *e);
  if (e == NULL) return NULL;
  e = base(e);
  if (e != NULL) e->f = f1;
  return e;
}
__attribute__((noinline)) struct E *ctor2(struct E *e) {
  if (e == NULL) e = alloc(sizeof *e);
  if (e == NULL) return NULL;
  e = base(e);
  if (e != NULL) e->f = f2;
  return e;
}
int main(int argc, char **argv) {
  (void)argc; (void)argv;
  struct E *a = ctor1(NULL);
  struct E *b = ctor2(NULL);
  (void)a;
  b->f(); // CHECK: f2 CHECK-NOT: f1
  return 0;
}
