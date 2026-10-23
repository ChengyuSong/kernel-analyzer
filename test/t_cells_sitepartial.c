// t_cells_sitepartial.c — site names (B, Fable 2026-10-22): a non-pointer
// write that starts inside a field, at or past its half (an i32 4 bytes
// into the i64 x), covers bytes 4..8 of x and no pointer field: the site is
// named struct s. The judge steps from the start of the field that holds
// the write's first byte (before the fix it stepped from 4 bytes before x
// and looped).
// LOG: site names \(B\): mk .*t_cells_sitepartial.c:[0-9]+ malloc: struct.s: named
#include <stdlib.h>
struct s { long x; void (*f)(void); };
void fa(void) {}
struct s *g;
void mk(void) {
  struct s *p = malloc(sizeof(struct s));
  *(int *)((char *)p + 4) = 7;
  p->f = fa;
  g = p;
}
void call(void) { g->f(); } // CHECK: fa
