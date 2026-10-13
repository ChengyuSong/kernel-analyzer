// t_cells_zeroprod.c — row (2) (plan 3.53, Fable 2026-10-13): binutils
// bfd_alloc2(abfd, n, size) = bfd_alloc(abfd, size * n), whose zero case
// and rounding (`if (!n) n = 1; n = (n + 7) & -8`) apply to the product.
// The zero case names no element (zero elements, k bytes), and rounding a
// multiple of 24 to 8 is the identity, so xalloc2(k, sizeof (struct S))
// is an array of S with no tail: a variable index stays in it.
// LOG: extents: 1 arrays by size, 0 one by size, 0 header \+ data by size, 0 one then unknown
// LOG: 1 sized by a product through a zero-guarded wrapper
#include <stdlib.h>
typedef void (*fn)(void);
struct S { long a; fn f; long b; };
void afn(void) {}
void bfn(void) {}
__attribute__((noinline)) void *xalloc(unsigned long n) {
  if (!n) n = 1;
  n = (n + 7) & -8;
  return malloc(n);
}
__attribute__((noinline)) void *xalloc2(unsigned long nmemb, unsigned long size) {
  return xalloc(size * nmemb);
}
int main(int argc, char **argv) {
  struct S *v = xalloc2(argc, sizeof(struct S));
  for (int i = 0; i < argc; i++) v[i].f = (i & 1) ? afn : bfn;
  v[argc - 1].f(); // CHECK: afn bfn
  return 0;
}
