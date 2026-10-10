// t_tagged_ptrne.c — the negative of t_tagged_ptreq.c: the same copy
// under a != test does not merge (outside the equal edge the two pointers
// are different objects), so a's tag (any object's, STR included) lands
// on b's content: the STR read must keep the pointer writer.
// NOKEY: the unmerged copy puts STR on every tag, so the STR read admits every writer.
#include <stdlib.h>
#define STR 1
#define INT 2
#define PTR 4
struct S { int tag; void (*fp)(void); };
void fstr(void) {}
void fint(void) {}
void fptr(void) {}
void wstr(struct S *s) { s->fp = fstr; s->tag = STR; }
void wint(struct S *s) { s->fp = fint; s->tag = INT; }
void wptr(struct S *s) { s->fp = fptr; s->tag = PTR; }
void cmp(struct S *a, struct S *b) {
  if (b->tag & INT) {
    int fa = a->tag;
    int fb = b->tag;
    if (a != b) fb = fa | STR;
    b->tag = fb;
  }
}
void use(struct S *s) {
  if (s->tag & STR)
    s->fp(); // CHECK: fstr fint fptr
}
int main(int argc, char **argv) {
  struct S *x = malloc(sizeof *x), *y = malloc(sizeof *y);
  if (argc > 1) wstr(x); else if (argc > 2) wint(x); else wptr(x);
  if (argc > 3) wstr(y); else if (argc > 4) wint(y); else wptr(y);
  cmp(x, y);
  use(x);
  use(y);
  return 0;
}
