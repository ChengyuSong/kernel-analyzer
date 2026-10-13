// t_cells_ptrarray.c — row (1) (plan 3.53, Fable 2026-10-13): a pointer-
// slot array declared at its site (a T** receiver) is an array of slots
// whatever its size says. Here the size is not a multiple of a slot (an
// extra byte for a terminator), which the extent rule read as "one slot
// then unknown data", linking a variable index to a tail (sqlite3's
// fts3InitVtab char *[] tail@8, binutils buildargv).
// LOG: extents: 0 arrays by size, 0 one by size, 0 header \+ data by size, 0 one then unknown
// NOLOG: tail@8
#include <stdlib.h>
typedef void (*fn)(void);
void afn(void) {}
void bfn(void) {}
int main(int argc, char **argv) {
  fn *v = malloc(argc * sizeof(fn) + 1);
  for (int i = 0; i < argc; i++) v[i] = (i & 1) ? afn : bfn;
  v[argc - 1](); // CHECK: afn bfn
  return 0;
}
