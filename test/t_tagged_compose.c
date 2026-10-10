// t_tagged_compose.c — plan 3.51 composition: a retag guarded by a test,
// with a callee between the test and the retag that rewrites the tag.
// totext() is valueToText's shape: only Str or Blob values become Str,
// after expand() clears Zero. Composing expand's effect into the guard
// keeps the pointer value (Ptr) from ever being read as text; dropping
// the guard would admit fptr at the Str read.
#include <stdlib.h>
#define T_STR 1
#define T_BLOB 2
#define T_PTR 4
#define T_ZERO 8
struct S { int tag; void (*fp)(void); };
void fstr(void) {}
void fblob(void) {}
void fptr(void) {}
void wstr(struct S *s) { s->fp = fstr; s->tag = T_STR; }
void wblob(struct S *s) { s->fp = fblob; s->tag = T_BLOB | T_ZERO; }
void wptr(struct S *s) { s->fp = fptr; s->tag = T_PTR; }
void expand(struct S *s) { if (s->tag & T_ZERO) s->tag &= ~T_ZERO; }
void totext(struct S *s) {
  if (s->tag & (T_STR | T_BLOB)) {
    expand(s);
    s->tag |= T_STR;
  }
}
void use(struct S *s) {
  if (s->tag & T_STR)
    s->fp(); // CHECK: fstr fblob CHECK-NOT: fptr
}
int main(int argc, char **argv) {
  struct S *s = malloc(sizeof *s);
  if (argc > 1) wstr(s);
  else if (argc > 2) wblob(s);
  else wptr(s);
  totext(s);
  use(s);
  return 0;
}
