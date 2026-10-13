// t_cells_zerok.c — plan 3.53 term extension (Fable 2026-10-13): a
// wrapper that reads a zero size as 1 and rounds it up (binutils
// objalloc_alloc: `if (!n) n = 1; n = (n + 7) & -8`) has the term
// "n, 1 when zero, rounded to 8"; at sizeof-constant calls it is exact,
// so both objects are one struct by size, not "one then unknown".

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
int main(int argc, char **argv) {
  struct S *s = xalloc(sizeof(struct S));
  struct T *t = xalloc(sizeof(struct T));
  s->f = sfn;
  t->f = tfn;
  (argc > 1 ? s->f : t->f)(); // CHECK: sfn tfn
  return 0;
}
