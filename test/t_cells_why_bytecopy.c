// t_cells_why_bytecopy.c — a --cfl-cell-why chain crosses a byte copy and
// names it (BC, Fable 2026-10-27; instrument only): a byte copy's content
// edges are recorded with the copy as their cause, so the chain prints the
// copy's line and the two content cells it joins, where it printed
// "static copy edge or byte-copy content edge (unrecorded)"; a step with
// no record is now named an edge a node merge carried.
// KAFLAGS: --cfl-cell-why=sfn --cfl-cell-why-at=use:
// LOG: <- byte copy main t_cells_why_bytecopy.c:20 \(struct.S\+0 @0 of .* into struct.S\+0 @0 of .*\): cell struct.S\+8 @8 of main::call malloc @t_cells_why_bytecopy.c:17 #[0-9]+ \[id #[0-9]+\] \[struct.S\] \[id #[0-9]+\] -> cell struct.S\+8 @8 of main::call malloc @t_cells_why_bytecopy.c:19
// LOG: Cells: why: [1-9][0-9]* byte-copy content edges recorded
// NOLOG: unrecorded\)
#include <stdlib.h>
#include <string.h>
struct S { long a; void (*f)(void); };
void sfn(void) {}
__attribute__((noinline)) void use(struct S *b) { b->f(); } // CHECK: sfn
int main(void) {
  struct S *a = malloc(sizeof *a);
  a->f = sfn;
  struct S *b = malloc(sizeof *b);
  memcpy(b, a, sizeof *a);
  use(b);
  return 0;
}
