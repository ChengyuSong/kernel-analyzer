// t_cells_segments.c — rule 1, segments (plan 3.53, Fable 2026-10-13): one
// allocation of known size, sizeof A + sizeof B + sizeof C, with the site's
// casts declaring B and C. A's last field is an array, so a variable index
// on it runs on past A, but B and C are labeled segments: the index stays
// in bound there (counted) and reaches no unlabeled remainder (there is
// none). The memset makes the block byte-used first, so without the site's
// declaration the tail would stay unlabeled and the index would read it all.
#include <stdlib.h>
#include <string.h>
typedef void (*fn)(void);
struct A { long n; fn arr[2]; };
struct B { int k; fn fb; long pad; };
struct C { fn fc; long m[3]; };
void afn(void) {}
void bfn(void) {}
void cfn(void) {}
int main(int argc, char **argv) {
  size_t n = sizeof(struct A) + sizeof(struct B) + sizeof(struct C);
  struct A *a = malloc(n);
  memset(a, 0, n);
  struct B *b = (struct B *)&a[1];
  struct C *c = (struct C *)&b[1];
  a->arr[0] = afn;
  b->fb = bfn;
  c->fc = cfn;
  a->arr[argc](); // CHECK: afn CHECK-NOT: bfn cfn
  return 0;
}
