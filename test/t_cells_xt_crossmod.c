// t_cells_xt_crossmod.c — a holder guard's premise ("the method and its
// callees never rewrite the dispatch path's slot") is checked across
// modules (XT, Fable 2026-10-27): method_a calls reset_ops, defined in the
// other module, which rewrites h->ops. Through this module's declaration
// reset_ops looked bodiless, so the premise held without a check and the
// reload of h->ops in method_a was guarded; now reset_ops's body is
// checked, the premise fails and method_a gets no guard, so its call
// reaches method_b too (before XT: method_a only). One CHECK per case
// (cells-cases.sh): the reload in method_a is the answer XT changes.
// MODULE: t2_cells_xt_crossmod.c
// LOG: refused method_a: may write the dispatch path.s slot \+0 \(receiver premise fails; no guard\)
// LOG: holder guards: 0 reloads guarded; 1 methods that may rewrite the path
// LOG: cross-module calls \(XT\): 1 direct calls through a declaration of a function another module defines \(1 callees\)
struct H;
struct ops { void (*m)(struct H *); };
struct H { struct ops *ops; long n; };
void reset_ops(struct H *h);
void method_b(struct H *h);
__attribute__((noinline)) void method_a(struct H *h) {
  reset_ops(h);
  h->ops->m(h); // CHECK: method_a method_b
}
static struct ops ops_a = { method_a };
extern struct ops ops_b;
__attribute__((noinline)) void run(struct H *h) { h->ops->m(h); } // method_a method_b (before and after XT)
int main(int argc, char **argv) {
  struct H h = { argc ? &ops_a : &ops_b, 0 };
  run(&h);
  return (int)h.n;
}
