// t_cells_pwc_netzero.c — W (Fable 2026-10-23): a walk's period is the gcd
// of its component's cycle weights. bfd_get_next_section_by_name
// (section.c:923/:932) steps from a section back to its hash entry
// (container_of, -24) and forward to the next entry's section (+24); the
// caller's loop feeds the result back in, so the cycle has weight 0 and
// the pointer stays at the section's offset. Before W the period was the
// gcd of the edges' steps (24): the walk ran past the entry (its size is
// not known, as bfd_hash_allocate's is not) into the unlabeled tail, whose
// any-offset cell then took the write of `other` and gave it to every read
// through the walked pointer. KAMain.TA6 (09adb58) answers [f, g]; W
// answers [f] (no walk).
// Executed (clang -O0 -fsanitize=address): f twice, exit 0, no report.
#include <stddef.h>
#include <stdlib.h>
typedef void (*fn)(void);
struct sec { fn fn; long a, b; fn other; };
struct entry { struct entry *next; long hash; const char *str; struct sec section; };
void f(void) {}
void g(void) {}
__attribute__((noinline)) static struct sec *next_sec(struct sec *s) {
  struct entry *sh = (struct entry *)((char *)s - offsetof(struct entry, section));
  for (sh = sh->next; sh != NULL; sh = sh->next)
    if (sh->hash == 1) return &sh->section;
  return NULL;
}
int main(int argc, char **argv) {
  (void)argv;
  /* bfd_hash_allocate's entries: a size the solver does not know (a tail). */
  struct entry *e1 = calloc(1, sizeof *e1 + argc), *e2 = calloc(1, sizeof *e2 + argc);
  e1->next = e2;
  e1->hash = e2->hash = 1;
  e1->section.fn = e2->section.fn = f;
  e1->section.other = e2->section.other = g;
  for (struct sec *s = &e1->section; s; s = next_sec(s))
  {
    s->other = g; /* a write through the walked pointer, as bfd's s->contents = ... */
    s->fn(); // CHECK: f CHECK-NOT: g
  }
  free(e1);
  free(e2);
  return 0;
}
// LOG: offset-free cycle \(edge gcd 24, no walk\) over .* at next_sec .*t_cells_pwc_netzero.c:21
