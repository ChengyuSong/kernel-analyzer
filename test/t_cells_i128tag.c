// t_cells_i128tag.c — the first kernel finding (plan 3.53, kernel census):
// a tag field written from u128 arithmetic (a constant wider than 64
// bits) aborted the tagged-field term evaluator (APInt::getSExtValue).
// An integer wider than 64 bits is not a term: the store is not
// evaluable, the pair refused or unkeyed and counted, and the read stays
// sound.
#include <stdlib.h>
struct R { void (*fn)(void); };
struct M { int kind; void *z; };
void rfn(void) {}
void set(struct M *m, struct R *r) {
  __int128 big = ((__int128)1 << 100);
  m->z = r;
  m->kind = (int)(big >> 99);
}
void use(struct M *m) {
  if (m->kind == 2) {
    struct R *r = m->z;
    r->fn(); // CHECK: rfn
  }
}
int main(int argc, char **argv) {
  struct M *m = malloc(sizeof *m);
  struct R *r = malloc(sizeof *r);
  r->fn = rfn;
  set(m, r);
  use(m);
  return 0;
}
