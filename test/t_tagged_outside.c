// t_tagged_outside.c — plan 3.51 ruling (a.2): the outside domain of a
// function pointer. setText is exported and its address is taken by an
// API table handed outside, so its xDel parameter holds its call sites'
// arguments or what outside code can name (NULL, -1, its own functions,
// exported functions); rsDelete is internal and never reaches the
// outside, so the RowSet read admits only the RowSet writer.
// PAIR: struct.M+8 by +16
#include <stdlib.h>
struct R { void (*fn)(void); };
struct T { void (*fn)(void); };
struct M { int flags; void *z; void (*xDel)(void *); };
void rfn(void) {}
void tfn(void) {}
static void rsDelete(void *p) { free(p); }
void setText(struct M *m, struct T *t, void (*xDel)(void *)) { m->z = t; m->xDel = xDel; }
void setRowSet(struct M *m, struct R *r) { m->z = r; m->xDel = rsDelete; }
struct api { void (*setText)(struct M *, struct T *, void (*)(void *)); };
static const struct api apis = { setText };
extern void handout(const struct api *);
// (The call is in main: an indirect call after the read would rest on an
// alias assumption that setText, address-taken, fails; GAPS item 9.)
struct R *getRowSet(struct M *m) {
  if (m->xDel == rsDelete) return m->z;
  return 0;
}
int main(int argc, char **argv) {
  struct M *m = malloc(sizeof *m);
  struct R *r = malloc(sizeof *r);
  struct T *t = malloc(sizeof *t);
  r->fn = rfn;
  t->fn = tfn;
  handout(&apis);
  if (argc > 1) setRowSet(m, r); else setText(m, t, free);
  struct R *x = getRowSet(m);
  if (x)
    x->fn(); // CHECK: rfn CHECK-NOT: tfn
  return 0;
}
