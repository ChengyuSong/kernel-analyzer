// t_cells_segments_rest.c — rule 1, segments with a variable-size remainder
// after C: the size is sizeof A + sizeof B + sizeof C plus a variable n. The
// variable index on A's trailing array passes the labeled segments and
// reaches the unlabeled remainder, where a function pointer is stored, and
// not C.
#include <stdlib.h>
typedef void (*fn)(void);
struct A { long n; fn arr[2]; };
struct B { int k; fn fb; long pad; };
struct C { fn fc; long m[3]; };
void afn(void) {}
void bfn(void) {}
void cfn(void) {}
void rfn(void) {}
int main(int argc, char **argv) {
  size_t extra = (size_t)argc * 8;
  struct A *a = malloc(sizeof(struct A) + sizeof(struct B) + sizeof(struct C) + extra);
  struct B *b = (struct B *)&a[1];
  struct C *c = (struct C *)&b[1];
  fn *rest = (fn *)&c[1];
  a->arr[0] = afn;
  b->fb = bfn;
  c->fc = cfn;
  rest[argc] = rfn;
  a->arr[argc](); // CHECK: afn rfn CHECK-NOT: bfn cfn
  return 0;
}
