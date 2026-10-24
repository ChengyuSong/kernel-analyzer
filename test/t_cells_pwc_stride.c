// t_cells_pwc_stride.c — W (Fable 2026-10-23): a strided step inside a
// net-zero cycle keeps its stride as the period. next_sec steps from a
// section back to its entry (-24), on by a variable number of entries
// (stride 72) and forward to that entry's section (+24): the cycle weights
// are multiples of 72, so the walk stays at the sections' offset (24 mod
// 72); W's row names it. Before W the period was the edges' gcd, 24;
// KAMain.TA6 (09adb58) answers [f] here as well, so the case pins the
// period, not an answer.
// Executed (clang -O0 -fsanitize=address): f twice, exit 0, no report.
#include <stddef.h>
#include <stdlib.h>
typedef void (*fn)(void);
struct sec { fn fn; long a, b; fn other; long c, d; };
struct entry { struct entry *next; long hash; const char *str; struct sec section; };
void f(void) {}
void g(void) {}
static int k = 1;
__attribute__((noinline)) static struct sec *next_sec(struct sec *s, struct entry *end) {
  struct entry *sh = (struct entry *)((char *)s - offsetof(struct entry, section));
  sh += k;
  return sh < end ? &sh->section : NULL;
}
int main(int argc, char **argv) {
  (void)argv;
  struct entry *tab = calloc(1, 2 * sizeof *tab + argc); /* a tail, as bfd's */
  for (int i = 0; i < 2; i++) {
    tab[i].section.fn = f;
    tab[i].section.other = g;
  }
  for (struct sec *s = &tab[0].section; s; s = next_sec(s, tab + 2))
  {
    s->other = g; /* a write through the walked pointer, as bfd's s->contents = ... */
    s->fn(); // CHECK: f CHECK-NOT: g
  }
  free(tab);
  return 0;
}
// LOG: pwc period 72 \(edge gcd 24\) over .* at next_sec .*t_cells_pwc_stride.c:19
