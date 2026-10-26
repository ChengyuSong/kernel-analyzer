// t_cells_refold_mint.c — RM (Fable 2026-10-25): a refold mints into the
// table it is rebuilding. An unlabeled object (calloc'd, never written as a
// struct) has cells at +0 and +16 with member steps (+2: peek's q->b; +8:
// call's q->f); a stride-8 read (sum8, reached through a chain of globals,
// so after the steps) teaches it period 8, and the refold folds +16 onto
// +0. Merging the two cells replays one cell's steps onto the other's
// members; before MD the replay minted a +0 cell into the cleared table
// and the group's own placement overwrote it (a live cell outside the
// table: two cells of one name). MD skips that replay (both sides hold
// the member); RM places by merging, re-folds what a refold minted, and
// asserts that no cell minted during a refold is outside the table.
// Executed (clang -O0): fa, exit 0.
#include <stdlib.h>
#include <string.h>
typedef void (*fn)(void);
struct T { short a; short b; int c; fn f; };
void fa(void) {}
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
__attribute__((noinline)) void put(struct T *r) { fn x = fa; memcpy((char *)r + 8, &x, sizeof x); }
__attribute__((noinline)) short peek(struct T *q) { return q->b; }
__attribute__((noinline)) void call(struct T *q) {
  q->f(); // CHECK: fa
}
__attribute__((noinline)) long sum8(int n) {
  long s = 0;
  for (int i = 0; i < n; i++) s += ((long *)g39)[i];
  return s;
}
int main(int argc, char **argv) {
  (void)argv;
  char *o = calloc(64, 1);
  struct T *r = (struct T *)o, *q = (struct T *)(o + 16);
  peek(r);
  peek(q);
  put(r);
  memcpy(o + 16, o, 16);
  call(q);
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
  return (int)sum8(argc);
}
// LOG: [1-9][0-9]* cells merged by re-folding, 0 merged into cells the refold's own replays minted \(RM\)
