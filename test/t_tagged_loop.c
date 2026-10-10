// t_tagged_loop.c — plan 3.51 definition barrier (a50aa34): p names a
// different object each iteration. Walking back from `p->tag = STR`
// around the loop reaches `p->fp = fstr` of the previous iteration, which
// is another object; the tag write retags the content p's object holds
// now (fptr, from wptr) before use() reads it under STR. The STR read must
// keep fptr.
// NOKEY: the open STR retag applies to every writer; before the barrier the
// walk closed on the previous iteration and the pair keyed without fptr.
#include <stdlib.h>
#define STR 1
#define PTR 4
struct S { int tag; void (*fp)(void); };
void fstr(void) {}
void fptr(void) {}
void wptr(struct S *s) { s->fp = fptr; s->tag = PTR; }
void use(struct S *s) {
  if (s->tag & STR)
    s->fp(); // CHECK: fstr fptr
}
void fill(struct S **v, int n) {
  for (int i = 0; i < n; i++) {
    struct S *p = v[i];
    p->tag = STR;
    use(p);
    p->fp = fstr;
  }
}
int main(void) {
  struct S *v[2];
  v[0] = malloc(sizeof(struct S));
  v[1] = malloc(sizeof(struct S));
  wptr(v[0]);
  wptr(v[1]);
  fill(v, 2);
  use(v[0]);
  return 0;
}
