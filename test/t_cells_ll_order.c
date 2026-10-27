// t_cells_ll_order.c — LL (Fable 2026-10-24/25, plan 3.95): a lazy label
// is chosen by program order, not by the solve's arrival order. One malloc
// is written as struct B by wb, reached through one global, and as struct
// A by wa, reached through a chain of four globals, so B arrives first;
// neither write is in the allocation's own frame (main's pointer reaches
// them through globals, which are loads), so program order decides, and
// wa comes first in the module. KAMain.TTE1 (c0e3473) labels the object
// struct.B (an array of B by its 48-byte size) and answers [fa fb] at the
// A read and [fy] at the B read; LL discards that solve, mints the object
// as struct.A (an array of A: B's +16 folds onto A's +0) and answers
// [fa fb fy] at both reads: the answer depends on the label.
// Executed (clang -O0): fa then fy, exit 0.
#include <stdlib.h>
typedef void (*fn)(void);
struct A { fn f; fn h; };
struct B { fn g; fn x; fn y; };
void fa(void) {}
void fh(void) {}
void fb(void) {}
void fy(void) {}
static void *GA, *GB, *G1, *G2, *G3;
__attribute__((noinline)) void wa(void) { struct A *a = GA; a->f = fa; a->h = fh; }
__attribute__((noinline)) void wb(void) { struct B *b = GB; b->g = fb; b->y = fy; }
int main(int argc, char **argv) {
  (void)argc; (void)argv;
  void *p = malloc(48);
  GB = p;
  wb();
  G1 = p; G2 = G1; G3 = G2; GA = G3;
  wa();
  ((struct A *)p)->f(); // CHECK: fa fb fy
  ((struct B *)p)->y(); // answers fa fb fy (the harness checks one read)
  free(p);
  return 0;
}
// LOG: lazy labels \(LL\): 1 decided by this solve, which is discarded
// LOG: LL label by order: main::call malloc @[^ ]+ #[0-9]+ \[struct.A array\] chosen struct.A \(program order: write at wa .*t_cells_ll_order.c:22\) over first-arrival struct.B; candidates struct.A x1 @wa .*t_cells_ll_order.c:22, struct.B x1 @wb .*t_cells_ll_order.c:23; decided in iteration 0, confirmed in iteration [0-9]+
// LOG: LL relabeled in iteration 1: main::call malloc @[^ ]+ #[0-9]+ \[struct.B array\] struct.B -> struct.A
