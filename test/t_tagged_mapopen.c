// t_tagged_mapopen.c — plan 3.51: a writer whose found tag is open (its
// object is a parameter) and only mapped, never read: sqlite3's
// `pMem->u.i = ix; MemSetTypeFlag(pMem, MEM_Int)`. Its content is read
// under the map's image of an unknown tag, (t & ~TYPE) | INT, which a
// BLOB test excludes; it is not "any tag".
#include <stdlib.h>
#define T_INT 1
#define T_BLOB 2
#define T_TYPE 3
struct I { void (*fn)(void); };
struct B { void (*fn)(void); };
struct S { int flags; void *z; };
void ifn(void) {}
void bfn(void) {}
void setInt(struct S *s, struct I *i) { s->z = i; s->flags = (s->flags & ~T_TYPE) | T_INT; }
void setBlob(struct S *s, struct B *b) { s->z = b; s->flags = T_BLOB; }
void useBlob(struct S *s) {
  if (s->flags & T_BLOB) {
    struct B *b = s->z;
    b->fn(); // CHECK: bfn CHECK-NOT: ifn
  }
}
int main(int argc, char **argv) {
  struct S *s = malloc(sizeof *s);
  struct I *i = malloc(sizeof *i);
  struct B *b = malloc(sizeof *b);
  i->fn = ifn;
  b->fn = bfn;
  if (argc > 1) setInt(s, i); else setBlob(s, b);
  useBlob(s);
  return 0;
}
