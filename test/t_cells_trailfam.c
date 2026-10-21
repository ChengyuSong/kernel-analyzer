// t_cells_trailfam.c — gap 2 (Fable 2026-10-20): a struct ending in a
// flexible array member has no arrays of it (C11 6.7.2.1p3), so
// malloc(sizeof(struct F) + 2 * sizeof(fn)), a multiple of sizeof(struct
// F), is the header and its two trailing elements, never an array of
// F: the elements stay apart from first.
#include <stdlib.h>
typedef void (*fn)(void);
struct F { fn first; fn secs[]; };
void afn(void) {}
void bfn(void) {}
void cfn(void) {}
int main(int argc, char **argv) {
  struct F *f = malloc(sizeof(struct F) + 2 * sizeof(fn));
  f->first = cfn;
  fn *s = f->secs;
  s[0] = afn;
  s[1] = bfn;
  f->secs[argc](); // CHECK: afn bfn CHECK-NOT: cfn
  f->first();
  return 0;
}
// LOG: 1 structs ending in a flexible array member sized a multiple of theirs read as header \+ tail
// Order of the three clauses here: gap 2 first makes the object header +
// tail (famHeaders 1); the segment clause then labels the tail as the
// site's declared segment (secs[], an array of pointer slots); A1 runs
// second and only on a tail still unlabeled, so it counts 0 here. The
// 0 is that ordering, not A1 doing nothing.
// LOG: 1 objects \(1 trailing, 1 of them segments the site declares
// LOG: Cells: trailing arrays \(A1\): 0 trailing objects
