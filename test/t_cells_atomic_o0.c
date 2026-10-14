// t_cells_atomic_o0.c — -O0 atomics carry their pointers (Fable
// 2026-10-14). clang -O0 lowers __atomic_exchange_n / compare_exchange
// through a temporary slot: `store ptr f, s; v = load i64, s; atomicrmw
// xchg ptr q, i64 v` (and the old value back through `store i64`). The
// integer load fed only the atomic, which no use-side rule admitted, so
// the exchange stored nothing and both reads found nothing (cells and
// flows-to). An atomic's stored value now flows onward like a store's
// value, and its old value is a load of its slot.
// CFLAGS: -O0
#include <stdlib.h>
typedef void (*fn)(void);
struct cache { long flags; fn dst; long more; };
void f1(void) {}
void f2(void) {}
void h(void) {}
struct other { fn x; } O;
__attribute__((noinline)) void set_a(struct cache *c, fn f) { __atomic_exchange_n(&c->dst, f, __ATOMIC_SEQ_CST); }
__attribute__((noinline)) void set_b(struct cache *c, fn f) { fn old = 0; __atomic_compare_exchange_n(&c->dst, &old, f, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST); }
__attribute__((noinline)) void read_a(struct cache *c) {
  c->dst(); // CHECK: f1 CHECK-NOT: f2
}
__attribute__((noinline)) void read_b(struct cache *c) { c->dst(); }
int main(int argc, char **argv) {
  struct cache *a = calloc(1, sizeof *a), *b = calloc(1, sizeof *b);
  O.x = h;
  set_a(a, f1);
  set_b(b, f2);
  read_a(a);
  read_b(b);
  return 0;
}
