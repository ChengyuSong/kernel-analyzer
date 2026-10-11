// t_tagged_valuetest.c — plan 3.51 value tests (sqlite3's OP_Concat:
// flags1 = pIn1->flags; if ((flags1 & (Str|Blob)) == 0) Stringify(pIn1);
// ... pIn1->flags = flags1). The restored tag is the value loaded at L,
// and on the Stringify path that value has Str and Blob clear: the string
// Stringify writes is never read under Blob, so the Blob|Dyn read (the
// RowSet test) does not admit it.
// PAIR: struct.M+8 by +0
#include <stdlib.h>
#define T_STR 1
#define T_BLOB 2
#define T_DYN 4
struct R { void (*fn)(void); };
struct T { void (*fn)(void); };
struct M { int flags; void *z; };
void rfn(void) {}
void tfn(void) {}
void setRowSet(struct M *m, struct R *r) { m->z = r; m->flags = T_BLOB | T_DYN; }
void stringify(struct M *m, struct T *t) { m->z = t; m->flags = (m->flags & ~(T_STR | T_BLOB)) | T_STR; }
void concat(struct M *m, struct T *t) {
  int flags1 = m->flags;
  if ((flags1 & (T_STR | T_BLOB)) == 0) stringify(m, t);
  m->flags = flags1;
}
void useRowSet(struct M *m) {
  if ((m->flags & (T_BLOB | T_DYN)) == (T_BLOB | T_DYN)) {
    struct R *r = m->z;
    r->fn(); // CHECK: rfn CHECK-NOT: tfn
  }
}
int main(int argc, char **argv) {
  struct M *m = malloc(sizeof *m);
  struct R *r = malloc(sizeof *r);
  struct T *t = malloc(sizeof *t);
  r->fn = rfn;
  t->fn = tfn;
  m->flags = 0;
  if (argc > 1) setRowSet(m, r);
  concat(m, t);
  useRowSet(m);
  return 0;
}
