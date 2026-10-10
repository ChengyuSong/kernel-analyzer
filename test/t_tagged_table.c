// t_tagged_table.c — plan 3.51: a tag written from a constant table
// (sqlite3's `pOut->flags = aFlag[pOp->p1 & 1]`): the value is one of the
// table's elements, so the writer's tags are {BLOB, STR}, never PTR.
#include <stdlib.h>
#define T_STR 1
#define T_BLOB 2
#define T_PTR 4
struct P { void (*fn)(void); };
struct T { void (*fn)(void); };
struct S { int tag; void *z; };
void pfn(void) {}
void tfn(void) {}
static const int aFlag[2] = { T_BLOB, T_STR };
void setText(struct S *s, struct T *t, int k) { s->z = t; s->tag = aFlag[k & 1]; }
void setPtr(struct S *s, struct P *p) { s->z = p; s->tag = T_PTR; }
void use(struct S *s) {
  if (s->tag & T_PTR) {
    struct P *p = s->z;
    p->fn(); // CHECK: pfn CHECK-NOT: tfn
  }
}
int main(int argc, char **argv) {
  struct S *s = malloc(sizeof *s);
  struct P *p = malloc(sizeof *p);
  struct T *t = malloc(sizeof *t);
  p->fn = pfn;
  t->fn = tfn;
  if (argc > 1) setPtr(s, p); else setText(s, t, argc);
  use(s);
  return 0;
}
