// t_cells_p3_untagged.c — P3 (Fable 2026-10-17): a tag-keyed read with a
// census member key reads both schemes. The read of u.a.fp under
// `s->kind == 1` is keyed by the tag, and the census types it as member a.
// w3 writes member b without writing the tag (an untagged write: the tag
// catch-all), so the tag alone admits it; the census types it as member b
// (a char * local), another member: excluded by its member name, a listed
// assumption. At the commit before (one scheme per read): f1 f3.
// LOG: TaggedFields:   KEYED struct.S\+16 by \+0
// LOG: UnionKeys: 1 tag-keyed reads with a census member key read both schemes; 1 untagged and 0 tagged stores
#include <stdlib.h>
struct S {
  int kind;
  union {
    struct { void *next; void (*fp)(void); } a;
    struct { void *next; char *s; } b;
  } u;
};
void f1(void) {}
void f3(void) {}
void w1(struct S *s) { s->kind = 1; s->u.a.fp = f1; }
void w2(struct S *s, char *str) { s->kind = 2; s->u.b.s = str; }
void w3(struct S *s) { char *p = (char *)f3; s->u.b.s = p; }
void use(struct S *s) {
  if (s->kind == 1)
    s->u.a.fp(); // CHECK: f1 CHECK-NOT: f3
}
int main(int argc, char **argv) {
  struct S *s = malloc(sizeof *s);
  if (argc > 2) w1(s); else if (argc > 1) w2(s, argv[0]); else w3(s);
  use(s);
  return 0;
}
