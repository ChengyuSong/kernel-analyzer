// t_cells_closure.c — container storage closure (plan 3.55 obligation 1,
// --cfl-container-closure, report only; Fable 2026-10-13). The obligation
// is the FEED condition: a field fed only fresh blocks, null, or its own
// reload of the same owner is closed (tbl.slots, with bfd's `old =
// t->slots; ... t->slots = old` restore); a block moved between owners
// (`a->buf = b->buf`) is another value and opens the field. Where an
// address read from a field goes is information, not a verdict (tbl.slots
// is passed to a callee and still closed). A fed block that also leaves
// another way before the feed (tbl.aux's block is returned too) leaves its
// site unpaired.
// KAFLAGS: --cfl-container-closure
// LOG: CLOSED struct.tbl\+0: fed 1 fresh blocks \(0 through a formal; 0 of them leave
// LOG: CLOSED struct.tbl\+0: .* 1 re-stores
// LOG: OPEN struct.pair\+0: .* 1 stores of another value
// LOG: CLOSED struct.tbl\+8: fed 1 fresh blocks \(0 through a formal; 1 of them leave by another way too
// LOG: addresses read from it flow: passed to use_slots
#include <stdlib.h>
typedef void (*fn)(void);
struct tbl { fn *slots; fn *aux; };
struct pair { fn *buf; };
void f1(void) {}
__attribute__((noinline)) void use_slots(fn *s) { s[0] = f1; }
__attribute__((noinline)) fn *mk(struct tbl *t) {
  t->slots = malloc(8 * sizeof(fn));
  fn *a = malloc(sizeof(fn));
  t->aux = a;
  return a;
}
__attribute__((noinline)) void grow(struct tbl *t) {
  fn *old = t->slots;
  t->slots = 0;
  t->slots = old;
}
int main(int argc, char **argv) {
  struct tbl *t = malloc(sizeof *t);
  fn *extra = mk(t);
  grow(t);
  use_slots(t->slots);
  struct pair *a = malloc(sizeof *a), *b = malloc(sizeof *b);
  b->buf = malloc(sizeof(fn));
  a->buf = b->buf;
  a->buf[0] = f1;
  t->slots[argc](); // CHECK: f1
  return extra != 0;
}
