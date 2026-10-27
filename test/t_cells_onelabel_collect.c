// t_cells_onelabel_collect.c — collect mode under --cfl-cell-one-label-object
// (Fable ruling 2026-10-14; measurement only): a step of another struct
// (kind 1) is pended and reported like a two-name conflict, and every
// reported conflict prints both arrival paths. x is labeled X by its first
// write, then written as Y through asY; x and z meet at a phi.
// Max 3: the step conflict arrives among the first three, its place among
// them set by node order (rule S, 2026-10-24, moved it from first to third).
// KAFLAGS: --cfl-cell-one-label --cfl-cell-one-label-object=[struct.X --cfl-cell-one-label-max=3
// LOG: NAME CONFLICT #[123] at pop [0-9]+ \[fn-ptr: (yes|no), in cone: (yes|no)\]: .*a step as struct.Y of a cell of another struct
// LOG: NAME CONFLICT #[123] at pop [0-9]+ \[fn-ptr: (yes|no), in cone: (yes|no)\]: .*A = struct.[XZ]\+0
// LOG: path of 'main::call malloc @[^ ]+ #[0-9]+' into
// LOG: stopped at [0-9]+ pops \(one-label stop, 3 conflicts\)
#include <stdlib.h>
struct X { long a; long b; };
struct Y { int c; short d; short e; double f; };
struct Z { int g; int h; char i[8]; };
void *G;
__attribute__((noinline)) void asY(void *p) { ((struct Y *)p)->f = 1.0; }
int main(int argc, char **argv) {
  struct X *x = malloc(sizeof *x); x->a = 1;
  struct Z *z = malloc(sizeof *z); z->g = 2;
  asY(x);
  G = argc > 1 ? (void *)x : (void *)z;
  return (int)((struct X *)G)->b;
}
