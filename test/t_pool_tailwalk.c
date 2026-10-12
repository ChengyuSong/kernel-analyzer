// Plan 3.53 rule 1 extent: a sized header-plus-data allocation (a T, more
// T's and a string table: _bfd_archive_64_bit_slurp_armap's carsym block)
// walked by a constant-stride pointer cycle. The trailing object right
// after the header takes the header's own T, so the block is an array of
// T: the walk settles with a bounded number of cells.
// CFLAGS: -O3
// MAXCELLS: 400
#include <stdlib.h>
struct carsym { void (*fn)(void); long pos; };
void f(void) {}
// The size is binutils' amt = nsymz * sizeof (carsym) + stringsize + 1
// with stringsize = parsed_size - 8 * nsymz - 8: at -O3 a sum with the
// constant -8, which is no header size.
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
