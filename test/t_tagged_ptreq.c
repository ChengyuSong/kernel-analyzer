// t_tagged_ptreq.c — plan 3.51 pointer-equality identity merge
// (sqlite3VdbeExec's comparison opcodes: `if (pIn1 == pIn3) flags3 =
// flags1 | MEM_Str`). Inside the region the test a == b dominates, a's tag
// is b's: the retag of b is (b's tag | STR), guarded by b's INT test, so
// only the INT writer gains STR and the pointer writer stays out of the
// STR read. Without the merge, a's tag would be any object's tag.
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
    if (a == b) fb = fa | STR;
    b->tag = fb;
  }
}
void use(struct S *s) {
  if (s->tag & STR)
    s->fp(); // CHECK: fstr fint CHECK-NOT: fptr
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
