// t_tagged_settest.c — plan 3.51, Fable 2026-10-17 (T): a set test. The
// read is guarded by `s->tag == 1 || s->tag == 2`, which -O0 emits as a
// branch on a phi of the two comparisons (`phi i1 [true, P1], [c2, P2]`)
// and -O1 as two edges into the guarded block: on its true edge the tag is
// one of {1, 2}, so the read admits the writers of tags 1 and 2 only (at
// the commit before: "no dominating test", every writer).
#include <stdlib.h>
struct S { int tag; void (*fp)(void); };
void f1(void) {}
void f2(void) {}
void f3(void) {}
void w1(struct S *s) { s->fp = f1; s->tag = 1; }
void w2(struct S *s) { s->fp = f2; s->tag = 2; }
void w3(struct S *s) { s->fp = f3; s->tag = 3; }
void use(struct S *s) {
  if (s->tag == 1 || s->tag == 2)
    s->fp(); // CHECK: f1 f2 CHECK-NOT: f3
}
int main(int argc, char **argv) {
  (void)argv;
  struct S *s = malloc(sizeof *s);
  if (argc > 2) w1(s); else if (argc > 1) w2(s); else w3(s);
  use(s);
  return 0;
}
