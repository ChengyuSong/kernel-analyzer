// A variable index then a constant back-step on a site-labeled T followed
// by data (`s[argc - 1]`, the index and the -1 in separate GEPs at -O3)
// must reach the T's field and the data after it: the index is some
// element (a folded address), and the -1 stays in the element.
// CFLAGS: -O3
#include <stdlib.h>
struct carsym { void (*fn)(void); long pos; };
void f(void) {}
__attribute__((noinline)) struct carsym *slurp(size_t n, size_t strsz) {
  struct carsym *syms = malloc(sizeof(struct carsym) + n * sizeof(struct carsym) + strsz);
  for (struct carsym *p = syms; p < syms + n + 1; p++) {
    p->fn = f;
    p->pos = (long)n;
  }
  return syms;
}
int main(int argc, char **argv) {
  struct carsym *s = slurp((size_t)argc, 16);
  s[argc - 1].fn(); // CHECK: f
  return 0;
}
