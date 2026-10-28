// The second module of t_cells_xt_crossmod.c: reset_ops rewrites the slot
// the dispatch in run reads.
struct H;
struct ops { void (*m)(struct H *); };
struct H { struct ops *ops; long n; };
__attribute__((noinline)) void method_b(struct H *h) { h->n++; }
struct ops ops_b = { method_b };
__attribute__((noinline)) void reset_ops(struct H *h) { h->ops = &ops_b; }
