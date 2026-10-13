// t_cells_segments_use.c — rule 1, segments typed by first use: the same
// allocation with no casts at the site; callees type B and C at constant
// offsets (rule 1 for an unlabeled object), and a load of B's pointer
// field sees only what was stored there, not C's function pointer.
// (A variable index on A's trailing array is linked by solve order here:
// before B and C are typed it reaches the still-unlabeled tail; reported.)
#include <stdlib.h>
typedef void (*fn)(void);
struct A { long n; fn arr[2]; };
struct B { int k; fn fb; long pad; };
struct C { fn fc; long m[3]; };
void afn(void) {}
void bfn(void) {}
void cfn(void) {}
void initB(void *p) { struct B *b = p; b->fb = bfn; }
void initC(void *p) { struct C *c = p; c->fc = cfn; }
void callB(void *p) {
  struct B *b = p;
  b->fb(); // CHECK: bfn CHECK-NOT: cfn
}
int main(int argc, char **argv) {
  struct A *a = malloc(sizeof(struct A) + sizeof(struct B) + sizeof(struct C));
  a->arr[0] = afn;
  initB((char *)a + sizeof(struct A));
  initC((char *)a + sizeof(struct A) + sizeof(struct B));
  callB((char *)a + sizeof(struct A));
  return 0;
}
