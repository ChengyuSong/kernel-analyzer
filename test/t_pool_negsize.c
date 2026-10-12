// Plan 3.53 rule 1 extent: a size expression with a negative constant
// term (-O3 folds binutils' `nsymz * 16 + (len - 8 * nsymz - 8) + 1` into a
// sum carrying -8) says nothing about a header: the block is one T then
// unknown data, never "a T plus trailing data" read from -8 as 2^64 - 8.
// The constant-stride walk then settles it as an array of T.
// CFLAGS: -O3
// MAXCELLS: 400
// NOLOG: heap 1 labeled \([0-9]+ arrays of pointer slots, 1 header \+ trailing data\)
#include <stdlib.h>
struct carsym { void (*fn)(void); long pos; };
void f(void) {}
__attribute__((noinline)) struct carsym *slurp(size_t nsymz, size_t parsed_size) {
  size_t stringsize = parsed_size - 8 * nsymz - 8;
  struct carsym *syms = malloc(nsymz * sizeof(struct carsym) + stringsize + 1);
  for (struct carsym *p = syms; p < syms + nsymz; p++) {
    p->fn = f;
    p->pos = (long)nsymz;
  }
  return syms;
}
int main(int argc, char **argv) {
  struct carsym *s = slurp((size_t)argc, 4096);
  s[argc].fn(); // CHECK: f
  return 0;
}
