// t_cells_pwc_exit.c — W (Fable 2026-10-23): a strided step that leaves the
// cycle is on no cycle and gives the period nothing. next_sec is
// t_cells_pwc_stride's net-zero cycle (-24, a stride of 72, +24: period
// 72) plus a load through a stride of 8 from the walked section (peek)
// whose result never returns to the cycle. KAMain.TW1 (the first W build)
// added that stride to the period ("pwc period 8 (edge gcd 24)"); the
// period is 72.
// Executed (clang -O0 -fsanitize=address): f twice, exit 0, no report.
#include <stddef.h>
#include <stdlib.h>
typedef void (*fn)(void);
struct sec { fn fn; long a, b; fn other; long c, d; };
struct entry { struct entry *next; long hash; const char *str; struct sec section; };
void f(void) {}
void g(void) {}
static int k = 1;
long peek;
__attribute__((noinline)) static struct sec *next_sec(struct sec *s, struct entry *end) {
  peek = ((long *)s)[k];
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
    s->other = g;
    s->fn(); // CHECK: f
  }
  free(tab);
  return 0;
}
// LOG: pwc period 72 \(edge gcd 24\) over .* at next_sec .*t_cells_pwc_exit.c:
// NOLOG: pwc period 8 
