// t_tagged_between.c — plan 3.51 last-writer rule, gap 3: an F write
// between a function's F store and its tag store. wg writes fp = g, then
// seth overwrites fp = h (and tags 3), then wg tags 1: the object holds
// h under tag 1, so the read under tag == 1 must see h.
#include <stdlib.h>
struct S { int tag; void (*fp)(void); };
void fa(void) {}
void fb(void) {}
void g(void) {}
void h(void) {}
void seth(struct S *s) { s->fp = h; s->tag = 3; }
void wb(struct S *s) { s->fp = fb; s->tag = 2; }
void wg(struct S *s) { s->fp = g; seth(s); s->tag = 1; }
void use(struct S *s) {
  if (s->tag == 1)
    s->fp(); // CHECK: h
}
int main(void) {
  struct S *s = malloc(sizeof *s);
  wg(s);
  use(s);
  wb(s);
  use(s);
  return 0;
}
