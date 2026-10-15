// t_cells_slot_census.c — --cfl-cell-slot-census (Fable 2026-10-14;
// report only): a fact in a cell whose layout has no pointer-width slot at
// the cell's offset (here the int member n, written with a function
// pointer through an untyped address) is counted in the no-slot classes,
// and the store that fed it is named with its stored facts' origin kind.
// KAFLAGS: --cfl-cell-soup-profile --cfl-cell-leak-census --cfl-cell-slot-census
// LOG: SLOT NO slot: other integer member: 1 facts
// LOG: SLOT #1 1 facts .*: struct.S\+0 of main::call malloc #[0-9]+ \[struct.S\] \| other integer member, leaf i32
// LOG: fed 1 \(function 1\) by store main t_cells_slot_census.c:19 store ptr @fb
// LOG: SLOT object #1 1 facts .* in 1 cells: main::call malloc
#include <stdlib.h>
typedef void (*fn)(void);
struct S { int n; int m; fn f; };
void fa(void) {}
void fb(void) {}
int main(void) {
  struct S *s = malloc(sizeof *s);
  s->f = fa;
  *(fn *)(void *)s = fb; // a pointer into the int member n
  s->f(); // CHECK: fa
  return 0;
}
