// t_cells_relay_regions.c — rows (ii) (Fable 2026-10-25, plan 3.121): a relay
// row counts its distinct regions (D) at the final cell keys, relative to
// the origin, apart from its applications (A). One copy site (cp) copies
// a struct S into an unlabeled byte object at +8 and at +24; a stride-16
// read (sum16, reached through a chain of globals, so after the copies)
// teaches the object period 16, and the refold folds +24 onto key 8. Two
// applications, one region; the +24 application was recorded at an offset
// the object has folded since (R = 1), the +8 one was not.
// Executed (clang -O0): fa, exit 0.
// KAFLAGS: --cfl-rule-report=/dev/stdout
#include <stdlib.h>
#include <string.h>
typedef void (*fn)(void);
struct S { fn f; fn g; };
void fa(void) {}
void fb(void) {}
static char *g0;
static char *g1;
static char *g2;
static char *g3;
static char *g4;
static char *g5;
static char *g6;
static char *g7;
static char *g8;
static char *g9;
static char *g10;
static char *g11;
static char *g12;
static char *g13;
static char *g14;
static char *g15;
static char *g16;
static char *g17;
static char *g18;
static char *g19;
static char *g20;
static char *g21;
static char *g22;
static char *g23;
static char *g24;
static char *g25;
static char *g26;
static char *g27;
static char *g28;
static char *g29;
static char *g30;
static char *g31;
static char *g32;
static char *g33;
static char *g34;
static char *g35;
static char *g36;
static char *g37;
static char *g38;
static char *g39;
typedef long L2[2];
__attribute__((noinline)) long sum16(int n) {
  long s = 0;
  for (int i = 0; i < n; i++) s += ((L2 *)g39)[i][1];
  return s;
}
__attribute__((noinline)) void cp(char *d, struct S *s) { memcpy(d, s, sizeof *s); }
int main(int argc, char **argv) {
  (void)argv;
  char *o = calloc(64, 1);
  struct S s = {fa, fb};
  cp(o + 8, &s);
  cp(o + 24, &s);
  ((struct S *)(o + 24))->f(); // CHECK: fa
  g0 = o;
  g1 = g0;
  g2 = g1;
  g3 = g2;
  g4 = g3;
  g5 = g4;
  g6 = g5;
  g7 = g6;
  g8 = g7;
  g9 = g8;
  g10 = g9;
  g11 = g10;
  g12 = g11;
  g13 = g12;
  g14 = g13;
  g15 = g14;
  g16 = g15;
  g17 = g16;
  g18 = g17;
  g19 = g18;
  g20 = g19;
  g21 = g20;
  g22 = g21;
  g23 = g22;
  g24 = g23;
  g25 = g24;
  g26 = g25;
  g27 = g26;
  g28 = g27;
  g29 = g28;
  g30 = g29;
  g31 = g30;
  g32 = g31;
  g33 = g32;
  g34 = g33;
  g35 = g34;
  g36 = g35;
  g37 = g36;
  g38 = g37;
  g39 = g38;
  (void)sum16(argc);
  return 0;
}
// LOG: C relay cp .*t_cells_relay_regions.c:[0-9]+: struct.S into bytes \(1 regions, 2 applications, 1 applied at a since-refolded offset\)
