// t_cells_sitesolve.c — site names (B, (c), Fable 2026-10-22): a write the
// solve finds through a by-origins address (no struct step) that the
// site's web did not find is judged as the walk judges it. w1's long over
// the long x is checked at the solve; w2's pointer into the long y FAILs,
// and the site loses its name: untyped at the solve, with its row.
// LOG: site names \(B\): mk .*:[0-9]+ malloc: struct.s: untyped at the solve: \(c\) FAIL: \+16 8B ptr: a pointer into a non-pointer field of struct.s over struct.s\+16 at mk .*, found at solve by store w2
// LOG: \(c\) checked at solve 1, not checked 1 \(1 sites untyped by them\)
#include <stdlib.h>
struct s { void (*f)(void); long x; long y; };
void fa(void) {}
void *g;
__attribute__((noinline)) void mk(void) {
  struct s *p = malloc(sizeof *p);
  p->x = 0;
  g = p;
}
__attribute__((noinline)) void w1(void) { char *q = g; *(long *)(q + 8) = 5; }
__attribute__((noinline)) void w2(void) { char *q = g; *(void **)(q + 16) = (void *)fa; }
__attribute__((noinline)) void w3(void) { char *q = g; *(void (**)(void))(q + 0) = fa; }
int main(void) { mk(); w1(); w2(); w3(); ((struct s *)g)->f(); return 0; } // CHECK: fa
