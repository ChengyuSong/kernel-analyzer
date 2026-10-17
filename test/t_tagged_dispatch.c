// t_tagged_dispatch.c — plan 3.51, Fable 2026-10-17 (T): a dispatch through
// a constant 2-D table (binutils' `switch (link_action[row][prev])`, prev =
// h->type, or a constant on another path). On the case edge ACT_CALL the
// table entry is ACT_CALL, so the tag is a column holding ACT_CALL in some
// row: {1, 2}. prev's other value, 0, holds no ACT_CALL in any row, so the
// test stands (were it one, the tag would be untested). At the commit
// before: no test (the switch is on a table value), every writer.
#include <stdlib.h>
enum act { ACT_NONE, ACT_CALL, ACT_SKIP };
static const enum act table[2][4] = {
  { ACT_NONE, ACT_CALL, ACT_CALL, ACT_SKIP },
  { ACT_NONE, ACT_SKIP, ACT_CALL, ACT_SKIP },
};
struct S { int tag; void (*fp)(void); int flag; };
void f0(void) {}
void f1(void) {}
void f2(void) {}
void f3(void) {}
void w0(struct S *s) { s->fp = f0; s->tag = 0; }
void w1(struct S *s) { s->fp = f1; s->tag = 1; }
void w2(struct S *s) { s->fp = f2; s->tag = 2; }
void w3(struct S *s) { s->fp = f3; s->tag = 3; }
__attribute__((noinline)) void use(struct S *s, int row) {
  int prev = s->tag;
  if (s->flag) prev = 0;
  enum act a = table[row][prev];
  switch (a) {
  case ACT_CALL:
    s->fp(); // CHECK: f1 f2 CHECK-NOT: f0 f3
    break;
  case ACT_SKIP:
  case ACT_NONE:
    break;
  }
}
int main(int argc, char **argv) {
  (void)argv;
  struct S *s = malloc(sizeof *s);
  s->flag = argc > 4;
  if (argc > 3) w0(s); else if (argc > 2) w1(s); else if (argc > 1) w2(s); else w3(s);
  use(s, argc & 1);
  return 0;
}
