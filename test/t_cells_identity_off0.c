// t_cells_identity_off0.c — a method-identity test on a slot at offset 0
// (plan 3.53, the second kernel memory finding): `if (c->ops->init !=
// init_a) abort();` then a reload of c->ops, in a method dispatched as
// c->ops->run(c). The guard's pseudo receiver site steps from the holder
// to the tested slot; at offset 0 there is no step (the pointer itself),
// and the setup left the sentinel UINT32_MAX as the step's label, which
// the solve then indexed (the kernel's identity tests; e30b761 and 964cc57
// segfaulted in stepOne).
#include <stdlib.h>
struct ctx;
struct ops { void (*init)(void); void (*run)(struct ctx *); };
struct ctx { struct ops *ops; };
void init_a(void) {}
void init_b(void) {}
void run_a(struct ctx *c) {
  if (c->ops->init != init_a) abort();
  struct ops *o = c->ops;
  o->init(); // CHECK: init_a CHECK-NOT: init_b
}
void run_b(struct ctx *c) {}
struct ops oa = { init_a, run_a }, ob = { init_b, run_b };
int main(int argc, char **argv) {
  struct ctx c1 = { &oa }, c2 = { &ob };
  struct ctx *c = argc > 1 ? &c1 : &c2;
  c->ops->run(c);
  return 0;
}
