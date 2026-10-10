// t_tagged_product.c — plan 3.51 ruling (a): product tags. isRowSet tests
// the flags and the destructor together (sqlite3's Mem.z under
// MEM_Blob|MEM_Dyn and xDel == rsDelete); the blob writer has the flags
// but not the destructor, the string writer the destructor but not the
// flags, so only the pair (flags, xDel) excludes both.
// PAIR: struct.M+8 by +0 x +16
#include <stdlib.h>
struct R { void (*fn)(void); };
struct B { void (*fn)(void); };
struct T { void (*fn)(void); };
struct M { int flags; void *z; void (*xDel)(void *); };
void rfn(void) {}
void bfn(void) {}
void tfn(void) {}
void rsDelete(void *p) { free(p); }
void blobFree(void *p) { free(p); }
int isRowSet(struct M *m) { return (m->flags & 3) == 3 && m->xDel == rsDelete; }
void setRowSet(struct M *m, struct R *r) { m->z = r; m->flags = 3; m->xDel = rsDelete; }
void setBlob(struct M *m, struct B *b) { m->z = b; m->flags = 3; m->xDel = blobFree; }
void setStr(struct M *m, struct T *t) { m->z = t; m->flags = 1; m->xDel = rsDelete; }
void useRowSet(struct M *m) {
  if (isRowSet(m)) {
    struct R *r = m->z;
    r->fn(); // CHECK: rfn CHECK-NOT: bfn tfn
  }
}
int main(int argc, char **argv) {
  struct M *m = malloc(sizeof *m);
  struct R *r = malloc(sizeof *r);
  struct B *b = malloc(sizeof *b);
  struct T *t = malloc(sizeof *t);
  r->fn = rfn;
  b->fn = bfn;
  t->fn = tfn;
  if (argc > 2) setRowSet(m, r); else if (argc > 1) setBlob(m, b); else setStr(m, t);
  useRowSet(m);
  return 0;
}
