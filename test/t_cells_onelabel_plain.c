// t_cells_onelabel_plain.c — --cfl-cell-one-label-object (Fable ruling
// 2026-10-14; measurement only): a named object's conflicts are reported
// whether or not both sides carry function-pointer objects and whether or
// not the node is in the icall cone, marked for the unfiltered verdict.
// P and Q hold no function pointers and meet at a select; no icall reads
// them.
// KAFLAGS: --cfl-cell-one-label --cfl-cell-one-label-object=[struct.P
// LOG: \(outside the icall cone: .*\) \[fn-ptr: no, in cone: no\]
// LOG: = struct.P\+0 @0 of \{main::call malloc #[0-9]+ \[struct.P\]\}
// LOG: = struct.Q\+0 @0 of \{main::call malloc #[0-9]+ \[struct.Q\]\}
// LOG: stopped at [0-9]+ pops \(one-label stop, 1 conflict\)
#include <stdlib.h>
struct P { long a; long b; };
struct Q { int c; short d; short e; double f; };
void *G;
__attribute__((noinline)) long use(void *q) { return ((struct P *)q)->b; }
int main(int argc, char **argv) {
  struct P *p = malloc(sizeof *p); p->a = 1;
  struct Q *q = malloc(sizeof *q); q->c = 2; q->f = 1.5;
  G = argc > 1 ? (void *)p : (void *)q;
  return (int)use(G);
}
