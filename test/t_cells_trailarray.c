// t_cells_trailarray.c — A1 (Fable 2026-10-20, plan 3.51 trailing arrays):
// an allocation of sizeof(struct M) + sizeof(fn) for a struct M that ends
// in `fn secs[1]` conforms: its trailing object is the array's further
// element, labeled an array of fn, and the index running on past secs[0]
// reaches it. The array is filled through its own index, as bfd fills
// elf_segment_map.sections, so no M-stride makes M an array. Before A1 the
// trailing object was unlabeled data reached through its any-offset cell.
#include <stdlib.h>
typedef void (*fn)(void);
struct M { long n; fn secs[1]; };
void afn(void) {}
void bfn(void) {}
int main(int argc, char **argv) {
  struct M *m = malloc(sizeof(struct M) + sizeof(fn));
  m->n = 2;
  fn *s = m->secs;
  s[0] = afn;
  s[1] = bfn;
  m->secs[argc](); // CHECK: afn bfn
  return 0;
}
// LOG: Cells: trailing arrays \(A1\): 1 trailing objects are their header's trailing array's further elements
// LOG: ; 1 variable indexes ran on into them
