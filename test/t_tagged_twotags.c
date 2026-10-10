// t_tagged_twotags.c — plan 3.51, soundness: one field keyed by two tags.
// useA's read is keyed by a, useB's by b; writer keys do not name the
// tag, so useB's admitted writers are the cells the writers write.
#include <stdlib.h>
struct S { int a; int b; void (*fp)(void); };
void f1(void) {}
void f2(void) {}
void f3(void) {}
void w1(struct S *s) { s->fp = f1; s->a = 1; s->b = 1; }
void w2(struct S *s) { s->fp = f2; s->a = 2; s->b = 1; }
void w3(struct S *s) { s->fp = f3; s->a = 1; s->b = 2; }
void useA(struct S *s) {
  if (s->a == 1) s->fp();
}
void useB(struct S *s) {
  if (s->b == 1)
    s->fp(); // CHECK: f1 f2 CHECK-NOT: f3
}
int main(int argc, char **argv) {
  struct S *s = malloc(sizeof *s);
  if (argc > 2) w1(s); else if (argc > 1) w2(s); else w3(s);
  useA(s);
  useB(s);
  return 0;
}
