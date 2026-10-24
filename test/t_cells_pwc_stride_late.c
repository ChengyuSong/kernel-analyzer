// t_cells_pwc_stride_late.c — LA (Fable 2026-10-24): array-ness decided
// late. As t_cells_pwc_stride.c, but the walk steps by another 72-byte
// struct (no evidence that the calloc'd struct.entry is an array) and the
// T-typed index (tab[i]) is in init, reached only through G after the
// walk has run: the walk reaches calloc while it is still "struct.entry
// then unknown" and links the tail's any-offset cell (an index from the T
// may run past it); the T-typed index then makes it an array of
// struct.entry, but the link stays, and the any-offset cell, written with
// g through the walked pointer, gives g to the read of s->fn. KAMain.TPW
// (ff2d008) answers [f, g]. LA discards that solve and mints the object
// as the array in the next iteration (the walk folds back at 72), where
// the T-typed index confirms it: [f].
// Executed (clang -O0 -fsanitize=address): f twice, exit 0, no report.
#include <stddef.h>
#include <stdlib.h>
typedef void (*fn)(void);
struct sec { fn fn; long a, b; fn other; long c, d; };
struct entry { struct entry *next; long hash; const char *str; struct sec section; };
struct pad72 { char b[72]; };
void f(void) {}
void g(void) {}
static int k = 1;
static struct entry *G;
__attribute__((noinline)) static struct sec *next_sec(struct sec *s, struct entry *end) {
  struct entry *sh = (struct entry *)((char *)s - offsetof(struct entry, section));
  sh = (struct entry *)((struct pad72 *)sh + k);
  return sh < end ? &sh->section : NULL;
}
__attribute__((noinline)) static void init(void) {
  struct entry *tab = G;
  for (int i = 0; i < 2; i++) {
    tab[i].section.fn = f;
    tab[i].section.other = g;
  }
}
int main(int argc, char **argv) {
  (void)argv;
  struct entry *tab = calloc(1, 2 * sizeof *tab + argc);
  tab[0].section.fn = f;
  for (struct sec *s = &tab[0].section; s; s = next_sec(s, tab + 2))
  {
    if (!G) { G = tab; init(); }
    s->other = g;
    s->fn(); // CHECK: f CHECK-NOT: g
  }
  free(tab);
  return 0;
}
// LOG: late arrays \(LA\): 1 decided by this solve, which is discarded
// LOG: array-ness decided late: main .*t_cells_pwc_stride_late.c:[0-9]+ struct.entry, decided by a T-typed index at init .*t_cells_pwc_stride_late.c:[0-9]+; tail link made by next_sec .*t_cells_pwc_stride_late.c:[0-9]+ \(stride 72\); redone in iteration 1, confirmed in iteration 2
