// t_cells_p3_catchall.c — P3 (Fable 2026-10-17): a write the census cannot
// type by member (#?, every member) is admitted by a read of both schemes.
// w6 writes the slot under tag 1 a value whose type the census does not
// know (`c ? (char *)f6 : gbuf`: a function and a char array), so its
// member key is the census catch-all; the read under `s->kind == 1`, keyed
// by the tag and typed as member a by the census, admits it by both: f6.
// w2's write of member b under tag 2 is excluded by its tag.
// LOG: UnionKeys: 1 tag-keyed reads with a census member key read both schemes; 0 untagged and 0 tagged stores
#include <stdlib.h>
struct S {
  int kind;
  union {
    struct { void *next; void (*fp)(void); } a;
    struct { void *next; char *s; } b;
  } u;
};
void f1(void) {}
void f2(void) {}
void f6(void) {}
char gbuf[8];
int c;
void w1(struct S *s) { s->kind = 1; s->u.a.fp = f1; }
void w2(struct S *s) { char *p = (char *)f2; s->kind = 2; s->u.b.s = p; }
void w6(struct S *s) { s->kind = 1; s->u.b.s = c ? (char *)f6 : gbuf; }
void use(struct S *s) {
  if (s->kind == 1)
    s->u.a.fp(); // CHECK: f1 f6 CHECK-NOT: f2
}
int main(int argc, char **argv) {
  (void)argv;
  struct S *s = malloc(sizeof *s);
  c = argc > 3;
  if (argc > 2) w1(s); else if (argc > 1) w2(s); else w6(s);
  use(s);
  return 0;
}
