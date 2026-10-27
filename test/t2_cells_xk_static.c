// The second module of t_cells_xk_static.c: its own static handler and ops.
struct ops { void (*f)(void); };
static int hits2;
static void handler(void) { hits2++; }
static struct ops ops = { handler };
__attribute__((noinline)) void run_b(void) { ops.f(); }
