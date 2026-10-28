// t_cells_why_xp.c — a --cfl-cell-why pattern copied from a --verbose=2
// log matches (XP, Fable 2026-10-26): logs name an object without ids
// ("main::call malloc @t_cells_why_xp.c:16 #K [struct.S]"); the why output
// inserts " [id #N]" before the label, and patterns were matched only
// against that form, so a pattern spanning the site and the label matched
// nothing. Now either form matches. Program as t_cells_why_layout.c; the
// pattern has spaces, so KAFLAGS quotes it (cells-cases.sh splits as xargs).
// KAFLAGS: "--cfl-cell-why=main::call malloc @t_cells_why_xp.c:17 #9 [struct.S]"
// LOG: LAYOUT main::call malloc @[^ ]+ #[0-9]+ \[id #[0-9]+\] \[struct.S\] learned struct.S at pop [0-9]+ \(member \+8\) stepping main:
#include <stdlib.h>
typedef void (*fn)(void);
struct S { long a; fn f; long b; };
void sfn(void) {}
void *blk;
__attribute__((noinline)) void *get(void) { return blk; }
int main(int argc, char **argv) {
  blk = malloc(24);
  struct S *p = get();
  p->f = sfn;
  p->f(); // CHECK: sfn
  return 0;
}
