// t_cells_zerok_o2.c — the -O2 form of t_cells_zerok.c: `if (!n) n = 1`
// becomes umax(n, 1), the same function, so the term is the same: both
// objects are one struct by size.
// CFLAGS: -O2
// LOG: extents: 0 arrays by size, 2 one by size, 0 header \+ data by size, 0 one then unknown
#include <stdlib.h>
typedef void (*fn)(void);
struct S { long a; fn f; long b; };
struct T { long a; fn f; long b[3]; };
void sfn(void) {}
void tfn(void) {}
__attribute__((noinline)) void *xalloc(unsigned long n) {
  if (!n) n = 1;
  n = (n + 7) & -8;
  return malloc(n);
}
__attribute__((noinline)) void sets(struct S *s) { s->f = sfn; }
__attribute__((noinline)) void sett(struct T *t) { t->f = tfn; }
__attribute__((noinline)) void calls(struct S *s) {
  s->f(); // CHECK: sfn CHECK-NOT: tfn
}
int main(int argc, char **argv) {
  struct S *s = xalloc(sizeof(struct S));
  struct T *t = xalloc(sizeof(struct T));
  sets(s);
  sett(t);
  calls(s);
  return t->b[0] != 0;
}
