// t_cells_p3_disagree.c — P3 (Fable 2026-10-17): a tagged write of another
// member, excluded and reported as a tag/member disagreement. w4 writes
// member b under tag 2; retag sets tag 2 to 1 in place, with no content
// write (as elf64-x86-64.c:1902 sets a hash entry defined), so the read
// under `s->kind == 1` admits w4 by its tag (2 retagged to 1); w5 (tag 3)
// it excludes by the tag. The census types w4 as member b (a char *
// local) and the read as member a: the read of both schemes excludes w4 by
// its member name, and the rule report names the retag it was admitted
// through. At the commit before: f1 f4.
// KAFLAGS: --cfl-rule-report=/dev/null
// LOG: UnionKeys: 1 tag-keyed reads with a census member key read both schemes; 0 untagged and 1 tagged stores
// LOG: UnionKeys:   tag/member disagreement: w4:[0-9]+ admitted by its tag at use
#include <stdlib.h>
struct S {
  int kind;
  union {
    struct { void *next; void (*fp)(void); } a;
    struct { void *next; char *s; } b;
  } u;
};
void f1(void) {}
void f4(void) {}
void f5(void) {}
void w1(struct S *s) { s->kind = 1; s->u.a.fp = f1; }
void w4(struct S *s) { char *p = (char *)f4; s->kind = 2; s->u.b.s = p; }
void w5(struct S *s) { char *p = (char *)f5; s->kind = 3; s->u.b.s = p; }
void retag(struct S *s) {
  if (s->kind == 2) s->kind = 1;
}
void use(struct S *s) {
  if (s->kind == 1)
    s->u.a.fp(); // CHECK: f1 CHECK-NOT: f4 f5
}
int main(int argc, char **argv) {
  (void)argv;
  struct S *s = malloc(sizeof *s);
  if (argc > 2) w1(s); else if (argc > 1) w5(s); else w4(s);
  retag(s);
  use(s);
  return 0;
}
