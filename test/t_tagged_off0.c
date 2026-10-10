// t_tagged_off0.c — plan 3.51: the keyed field at offset 0 (the object is
// typed after its first cell there is minted; the cell is split into its
// keyed read side when the object is typed). Otherwise t_tagged_fnptr: a
// function-pointer tag. The
// content z of an M is a RowSet only when its destructor is rsDelete
// (sqlite3's Mem.z by Mem.xDel); a read tested on the destructor admits
// only the RowSet writer, so the blob's function never reaches the call.
// PAIR: struct.M+0 by +16
#include <stdlib.h>
struct R { void (*fn)(void); };
struct B { void (*fn)(void); };
struct M { void *z; int flags; void (*xDel)(void *); };
void rfn(void) {}
void bfn(void) {}
void rsDelete(void *p) { free(p); }
void blobFree(void *p) { free(p); }
void setRowSet(struct M *m, struct R *r) { m->z = r; m->xDel = rsDelete; }
void setBlob(struct M *m, struct B *b) { m->z = b; m->xDel = blobFree; }
void useRowSet(struct M *m) {
  if (m->xDel == rsDelete) {
    struct R *r = m->z;
    r->fn(); // CHECK: rfn CHECK-NOT: bfn
  }
}
int main(int argc, char **argv) {
  struct M *m = malloc(sizeof *m);
  struct R *r = malloc(sizeof *r);
  struct B *b = malloc(sizeof *b);
  r->fn = rfn;
  b->fn = bfn;
  if (argc > 1) setRowSet(m, r); else setBlob(m, b);
  useRowSet(m);
  return 0;
}
