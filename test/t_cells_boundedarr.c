// t_cells_boundedarr.c — rule 1 bound clause (plan 3.53, Fable 2026-10-13):
// a T followed by data, indexed by a variable inside a declared array
// field that ends strictly within T (Fts3Table's aStmt[40]): the index
// stays in the field; it does not reach the trailing data, where a
// function pointer is stored.
#include <stdlib.h>
typedef void (*fn)(void);
void inarr(void) {}
void intail(void) {}
struct T { long n; fn a[4]; long m; };
int main(int argc, char **argv) {
  struct T *t = malloc(sizeof(struct T) + 64);
  t->a[0] = inarr;
  *(fn *)((char *)(t + 1) + 8) = intail;
  t->a[argc](); // CHECK: inarr CHECK-NOT: intail
  return 0;
}
