// t_tagged_branch.c — plan 3.51 last-writer rule, gap 1: a tag store not
// on every path after the F store. wg writes fp = g and retags only when
// c holds; on the other path s keeps its old tag (1, from wa), so the
// read under tag == 1 must still see g.
#include <stdlib.h>
struct S { int tag; void (*fp)(void); };
void fa(void) {}
void fb(void) {}
void g(void) {}
void wa(struct S *s) { s->fp = fa; s->tag = 1; }
void wb(struct S *s) { s->fp = fb; s->tag = 2; }
void wg(struct S *s, int c) { s->fp = g; if (c) s->tag = 2; }
void use(struct S *s) {
  if (s->tag == 1)
    s->fp(); // CHECK: fa g
}
int main(int argc, char **argv) {
  struct S *s = malloc(sizeof *s);
  wa(s);
  wg(s, argc > 1);
  use(s);
  wb(s);
  use(s);
  return 0;
}
