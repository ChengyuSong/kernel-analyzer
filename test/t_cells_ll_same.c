// t_cells_ll_same.c — LL (Fable 2026-10-24/25, plan 3.95): an object with
// several candidates whose first arrival is the program-order choice keeps
// it, with a row ("the first arrival") and no LL decision. wa writes
// struct.A at the object's start; wb, defined after it, copies the global
// gB (a struct.B) over it. The copy arrives first (the later write in the
// module does, in this solver), and its key is the copy source's own
// labeling site, the global gB, which precedes every instruction in
// program order: struct.B is both the first arrival and the choice
// (neither write is in main's frame).
// Executed (clang -O0): fb then fy, exit 0.
#include <stdlib.h>
#include <string.h>
typedef void (*fn)(void);
struct A { fn f; fn h; };
struct B { fn g; fn x; fn y; };
void fa(void) {}
void fh(void) {}
void fb(void) {}
void fy(void) {}
static struct B gB = {fb, 0, fy};
static void *GA, *GB;
__attribute__((noinline)) void wa(void) { struct A *a = GA; a->f = fa; a->h = fh; }
__attribute__((noinline)) void wb(void) { memcpy(GB, &gB, sizeof gB); }
int main(int argc, char **argv) {
  (void)argc; (void)argv;
  void *p = malloc(48);
  GA = p;
  wa();
  GB = p;
  wb();
  ((struct A *)p)->f(); // CHECK: fa fb
  ((struct B *)p)->y(); // answers fy (the harness checks one read)
  free(p);
  return 0;
}
// LOG: LL label by order: main::call malloc @[^ ]+ #[0-9]+ \[struct.B array\] chosen struct.B \(program order: global gB \(through 1 copies\)\), the first arrival; candidates struct.A x1 @wa .*t_cells_ll_same.c:22, struct.B x1 @wb .*t_cells_ll_same.c:23 \(copied\)
// NOLOG: lazy labels \(LL\): [0-9]+ decided by this solve, which is discarded
// NOLOG: LL relabeled
