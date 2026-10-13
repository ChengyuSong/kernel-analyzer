// t_cells_container0.c — row 2 (plan 3.53): a block declared as the base
// T at its site (1b) but sized for a container S that has T at offset 0
// (C inheritance), stepped as S at its start: the label widens to S
// (the size fits S), so the S member steps are no rule (b) rows and the
// cells inside T keep T's names.
// LOG: labels widened to a container at offset 0 \(row 2\): 1;
// LOG: rule \(b\) member steps whose struct is not at the address's offset: 0
#include <stdlib.h>
typedef void (*fn)(void);
struct T { fn f; long x; };
struct S { struct T base; fn g; long y[4]; };
void tfn(void) {}
void gfn(void) {}
int main(int argc, char **argv) {
  struct T *t = malloc(sizeof(struct S) + 16);
  t->f = tfn;
  struct S *s = (struct S *)t;
  s->g = gfn;
  s->g();       // CHECK: gfn CHECK-NOT: tfn
  s->base.f();
  return 0;
}
