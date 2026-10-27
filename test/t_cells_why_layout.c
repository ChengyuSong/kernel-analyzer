// t_cells_why_layout.c — --cfl-cell-why prints where each object it names
// learned its label during the solve (Fable 2026-10-15, log-only): the
// layout, the pop, and the step that wrote it (the kernel's kfree_rcu page
// took struct.intel_gt from a wrong-target pointer; this names that site).
// A block kept as void * is first written as S through p (no label at its
// site: the site's value is untyped).
// KAFLAGS: --cfl-cell-why=[struct.S
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
