// t_cells_onelabel_object.c — --cfl-cell-one-label-object (the user,
// Fable 2026-10-14; measurement only): the one-label stop mode counts only
// a name conflict whose held or arriving cell belongs to an object whose
// description contains the pattern. Two conflicts meet at a phi each:
// z/w first by pop, then x/y. Unfiltered the mode stops at z/w; filtered on
// struct.X it skips z/w (counted) and stops at x/y.
// KAFLAGS: --cfl-cell-one-label --cfl-cell-one-label-object=[struct.X
// LOG: A = struct.Y\+0 @0 of \{main::call malloc #[0-9]+ \[struct.Y\]\}
// LOG: B = struct.X\+0 @0 of \{main::call malloc #[0-9]+ \[struct.X\]\}
// NOLOG: \[struct.W\]\}
#include <stdlib.h>
typedef void (*fn)(void);
struct X { long a; fn f; };
struct Y { fn g; long b; };
struct Z { long c; fn h; };
struct W { fn k; long d; };
void fx(void) {}
void fy(void) {}
void fz(void) {}
void fw(void) {}
void *G1, *G2;
__attribute__((noinline)) void use1(void *q) { ((struct X *)q)->f(); }
__attribute__((noinline)) void use2(void *q) { ((struct Z *)q)->h(); }
int main(int argc, char **argv) {
  struct X *x = malloc(sizeof *x); x->f = fx;
  struct Y *y = malloc(sizeof *y); y->g = fy;
  struct Z *z = malloc(sizeof *z); z->h = fz;
  struct W *w = malloc(sizeof *w); w->k = fw;
  G1 = argc > 1 ? (void *)x : (void *)y;
  use1(G1);
  G2 = argc > 2 ? (void *)z : (void *)w;
  use2(G2);
  return 0;
}
