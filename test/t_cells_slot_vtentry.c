// t_cells_slot_vtentry.c — rule S (Fable 2026-10-24): an -O0 local slot is
// its reaching stores. The bfd_elf_gc_record_vtentry shape (elflink.c:13820):
// a table keeps a "done" entry at index -1, so it grows with
// realloc(ptr - 1) and stores ptr + 1 back. At -O0 the local ptr's three
// stores (the loaded used, the realloc result, the calloc result) all
// reached all four loads, so ptr - 1 fed realloc, realloc fed ptr, and
// ptr - 1 read it again (a -16 cycle closed by realloc's ALIAS(ret=arg0)),
// and ptr + 1 stored into used came back through ptr (a +16 cycle): a walk
// of step 16 ("field edges on cycles 2 ... step 16=2"). Reaching stores cut
// both: the loads before the realloc see only the loaded used, those after
// only the realloc or calloc result; the cycle through used is offset-free
// (-16 then +16), as at -O3: no walk, and the row says so. The answer is
// [f] either way: the table's elements fold onto one element's cells, and a
// walk of the element's size keeps a in a (in nm-O0 the walk joined the
// soup component and spread; here it has nothing to spread into).
// Executed (clang -O0 -fsanitize=address): f once, exit 0, no report.
#include <stdlib.h>
typedef void (*fn)(void);
void f(void) {}
void g(void) {}
struct slot { fn a, b; };
struct ent { struct slot *used; size_t size; };
__attribute__((noinline)) static int record(struct ent *e, size_t n) {
  struct slot *ptr = e->used;
  if (ptr)
    ptr = realloc(ptr - 1, (n + 1) * sizeof(struct slot));
  else
    ptr = calloc(n + 1, sizeof(struct slot));
  if (!ptr) return 0;
  e->used = ptr + 1;
  e->size = n;
  return 1;
}
int main(void) {
  struct ent e = {0, 0};
  if (!record(&e, 4) || !record(&e, 8)) return 1;
  e.used[-1].b = g; // the done entry
  e.used[0].a = f;
  e.used[0].a(); // CHECK: f CHECK-NOT: g
  free(e.used - 1);
  return 0;
}
// LOG: Slots: cut record ptr: 3 writes x 4 loads = 12 pairs -> 6 reaching
// LOG: offset-free cycle \(edge gcd 16, no walk\) over .* at record
// NOLOG: field edges on cycles [1-9]
