// t_cells_ptrdiff.c — PD (Fable 2026-10-23): a pointer difference p - q
// (sub of two ptrtoints) is an integer with no object identity, so it
// carries no facts. Used as an index back into the buffer it was taken
// from, the read still finds the target: the address goes through the
// GEP's base (tab), not through the integer. Before PD the difference also
// carried tab's and p's facts into d (bfd's elf-eh-frame.c:824 and
// merge.c:939 carried section-contents buffers this way).
// Executed (clang -O0 -fsanitize=address): t2 once, exit 0, no report.
#include <stdlib.h>
typedef void (*fn)(void);
void t0(void) {}
void t1(void) {}
void t2(void) {}
__attribute__((noinline)) static long offset_of(char *p, char *base) { return p - base; }
int main(void) {
  fn *tab = malloc(4 * sizeof(fn));
  tab[0] = t0; tab[1] = t1; tab[2] = t2;
  char *p = (char *)&tab[2];
  long d = offset_of(p, (char *)tab);
  fn g = *(fn *)((char *)tab + d);
  g(); // CHECK: t2
  free(tab);
  return 0;
}
// LOG: pointer differences \(sub of two ptrtoint\) carry no facts \(PD\)
// NOLOG: 0 pointer differences \(sub of two ptrtoint\) carry no facts
