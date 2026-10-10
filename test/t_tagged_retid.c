// t_tagged_retid.c — plan 3.51 return identity (sqlite3's
// `pOut = out2Prerelease(p, pOp); pOut->u.i = ..`): the callee sets the
// returned object's tag (on one path through a nested callee that returns
// its argument), so the writer through the result finds INT, not an open
// tag, and a BLOB read excludes it.
#include <stdlib.h>
#define T_INT 1
#define T_BLOB 2
struct I { void (*fn)(void); };
struct B { void (*fn)(void); };
struct S { int flags; void *z; };
void ifn(void) {}
void bfn(void) {}
static struct S *outClear(struct S *p) { p->flags = 0; p->flags = T_INT; return p; }
static struct S *outInt(struct S *base, int k) {
  struct S *p = &base[k];
  if (k > 5) return outClear(p);
  p->flags = T_INT;
  return p;
}
void opInt(struct S *base, int k, struct I *iv) { struct S *o = outInt(base, k); o->z = iv; }
void setBlob(struct S *s, struct B *b) { s->z = b; s->flags = T_BLOB; }
void useBlob(struct S *s) {
  if (s->flags & T_BLOB) {
    struct B *b = s->z;
    b->fn(); // CHECK: bfn CHECK-NOT: ifn
  }
}
int main(int argc, char **argv) {
  struct S *s = malloc(8 * sizeof *s);
  struct I *i = malloc(sizeof *i);
  struct B *b = malloc(sizeof *b);
  i->fn = ifn;
  b->fn = bfn;
  if (argc > 1) opInt(s, argc, i); else setBlob(&s[argc], b);
  useBlob(&s[argc]);
  return 0;
}
