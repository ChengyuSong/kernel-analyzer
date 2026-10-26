// t_cells_walk_flags.c — WF (Fable 2026-10-26, plan 3.127): walk flags are
// settled before facts cross. walk() advances S.p by one byte in a loop:
// the cycle S.p -> q -> q + 1 -> S.p closes only through the load and the
// store of S.p (hub edges made during the solve), so no pass before the
// facts move sees it, and b + 0 steps across q + 1 as +1, +2, ... until the
// final cycle pass flags the edge a walk (the first solve: q holds 33
// facts, q + 1 32). With WF that solve is redone from the final flags: q + 1
// is a walk from the start, its result is b's any-offset cell alone, and q
// holds b + 0 (stored before the loop) and the any-offset cell. The same in
// both arms: t_cells_walk_flags_off.c runs this file with collapse off.
// Executed (clang -O0): exit 1 (b[argc]).
// KAFLAGS: --cfl-cell-node-facts=-
#include <stdlib.h>
struct st { char *p; };
static struct st S;
__attribute__((noinline)) char far(char *r) { return r[0]; }
__attribute__((noinline)) void walk(int n) {
  for (int i = 0; i < n; i++) {
    char *q = S.p;
    S.p = q + 1;
  }
}
int main(int argc, char **argv) {
  (void)argv;
  char *b = malloc(64);
  for (int i = 0; i < 64; i++) b[i] = (char)i;
  S.p = b;
  walk(argc);
  return far(S.p);
}
// LOG: Cells: walk flags \(WF\): [0-9]+ at the end of this solve, 0 seeded, [1-9][0-9]* differ from the seed; the solve is redone from them
// LOG: Cells: walk flags: [1-9][0-9]* flags at the fixpoint, [0-9]+ solves \(1 redone for flags\)
// LOG: ^walk:   %10 = load ptr, ptr @S, align 8, !dbg ![0-9]+	2$
// LOG: ^walk:   %12 = getelementptr inbounds i8, ptr %11, i64 1, !dbg ![0-9]+	1$
