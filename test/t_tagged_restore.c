// t_tagged_restore.c — plan 3.51 (iii): a tag value loaded at L and
// stored later is the tag set that held at L, not the current tag. Here
// restore() saves the tag, writes PTR content and tag, then restores the
// saved tag (STR) with the pointer content still in z: the STR read must
// admit that writer. NOKEY: the saved tag is open at the load (a
// parameter's tag), so the read admits every writer; the point is pfn.
#include <stdlib.h>
#define T_STR 1
#define T_PTR 4
struct P { void (*fn)(void); };
struct T { void (*fn)(void); };
struct S { int tag; void *z; };
void pfn(void) {}
void tfn(void) {}
void setStr(struct S *s, struct T *t) { s->z = t; s->tag = T_STR; }
void restore(struct S *s, struct P *p) {
  int saved = s->tag;
  s->z = p;
  s->tag = T_PTR;
  s->tag = saved;
}
void useStr(struct S *s) {
  if (s->tag & T_STR) {
    struct T *t = s->z;
    t->fn(); // CHECK: tfn pfn
  }
}
int main(int argc, char **argv) {
  struct S *s = malloc(sizeof *s);
  struct P *p = malloc(sizeof *p);
  struct T *t = malloc(sizeof *t);
  p->fn = pfn;
  t->fn = tfn;
  setStr(s, t);
  if (argc > 1) restore(s, p);
  useStr(s);
  return 0;
}
