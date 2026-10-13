// t_cells_carvesize.c — plan 3.53 row 1: a pool carve's size is its
// form's (counter: the decrement), here n rounded up to 8 at entry, so a
// wrapper's object made by new_obj(cs, code) is sizeof(struct S) rounded
// up: one S, not "S then unknown" (libpcap newchunk / new_stmt).
// LOG: extents: 0 arrays by size, [1-9][0-9]* one by size, 0 header \+ data by size
// LOG: of them fresh wrappers with an unknown size term; 0 pool carves with an unknown size term
#include <stdlib.h>
typedef void (*fn)(void);
struct S { long a; fn f; long b; };
struct cstate { void *m; unsigned long n_left; };
void sfn(void) {}
static void *newchunk(struct cstate *cs, unsigned long n) {
  n = (n + 7) & -8;
  if (n > cs->n_left) {
    cs->m = malloc(4096);
    cs->n_left = 4096;
  }
  cs->n_left -= n;
  return (char *)cs->m + cs->n_left;
}
struct S *new_obj(struct cstate *cs, int code) {
  struct S *p = newchunk(cs, sizeof *p);
  p->a = code;
  return p;
}
int main(int argc, char **argv) {
  struct cstate cs = {0, 0};
  struct S *s = new_obj(&cs, 100);
  s->f = sfn;
  s->f(); // CHECK: sfn
  return 0;
}
