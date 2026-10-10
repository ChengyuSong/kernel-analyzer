// t_tagged_window.c — plan 3.51 last-writer rule, gap 2: a read between
// the F store and its tag store. wg writes fp = g, calls use while s
// still has its old tag (1, from wa), then retags; the read under
// tag == 1 must see g.
#include <stdlib.h>
struct S { int tag; void (*fp)(void); };
void fa(void) {}
void fb(void) {}
void g(void) {}
void use(struct S *s) {
  if (s->tag == 1)
    s->fp(); // CHECK: fa g
}
void wa(struct S *s) { s->fp = fa; s->tag = 1; }
void wb(struct S *s) { s->fp = fb; s->tag = 2; }
void wg(struct S *s) { s->fp = g; use(s); s->tag = 2; }
int main(void) {
  struct S *s = malloc(sizeof *s);
  wa(s);
  wg(s);
  wb(s);
  use(s);
  return 0;
}
