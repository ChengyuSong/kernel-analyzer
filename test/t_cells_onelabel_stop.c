// t_cells_onelabel_stop.c — the one-label mode at a stop that is not its
// own (Fable ruling 2026-10-14; measurement only): the cone line with the
// held and filtered counts is printed, and the final line names the stop.
// A filter matching nothing filters the x/y conflict out.
// KAFLAGS: --cfl-cell-one-label --cfl-cell-one-label-object=[struct.NOSUCH --cfl-cell-census-at=40
// LOG: icall cone at the stop: .* conflicts filtered out \(no object matching "\[struct.NOSUCH"\)
// LOG: stopped at [0-9]+ pops \(census-at stop\)
#include <stdlib.h>
typedef void (*fn)(void);
struct X { long a; fn f; };
struct Y { fn g; long b; };
void fx(void) {}
void fy(void) {}
void *G1;
__attribute__((noinline)) void use1(void *q) { ((struct X *)q)->f(); }
int main(int argc, char **argv) {
  struct X *x = malloc(sizeof *x); x->f = fx;
  struct Y *y = malloc(sizeof *y); y->g = fy;
  G1 = argc > 1 ? (void *)x : (void *)y;
  use1(G1);
  return 0;
}
