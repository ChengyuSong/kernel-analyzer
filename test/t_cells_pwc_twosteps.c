// t_cells_pwc_twosteps.c — W (Fable 2026-10-23): a cycle through two step
// functions (+16 and +24) has cycle weights 16 and 24; the period stays
// their gcd, 8, as it was (the edges' gcd), and the walk keeps reaching the
// table's 8-byte slots it can reach.
// Executed (clang -O0 -fsanitize=address): t0, t2, t5, exit 0, no report.
#include <stdlib.h>
typedef void (*fn)(void);
void t0(void) {}
void t1(void) {}
void t2(void) {}
void t3(void) {}
void t4(void) {}
void t5(void) {}
__attribute__((noinline)) static char *step16(char *p) { return p + 16; }
__attribute__((noinline)) static char *step24(char *p) { return p + 24; }
int main(void) {
  fn *tab = malloc(8 * sizeof(fn));
  tab[0] = t0; tab[1] = t1; tab[2] = t2; tab[3] = t3; tab[4] = t4; tab[5] = t5;
  char *p = (char *)tab;
  for (int i = 0; i < 3; i++) {
    (*(fn *)p)(); // CHECK: t0 t2 t5
    p = (i & 1) ? step24(p) : step16(p);
  }
  free(tab);
  return 0;
}
// LOG: Cells: field edges on cycles .* step 8=
// NOLOG: pwc period [0-9]+ \(edge gcd 8\) over .*t_cells_pwc_twosteps
