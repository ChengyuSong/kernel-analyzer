// t_cells_xk_static.c — a static function and a static global defined
// under one name in two modules (the kernel's static event_show in several
// files) are named with their module (XK, Fable 2026-10-27): "fn handler
// (t_cells_xk_static.c)" and "fn handler (t2_cells_xk_static.c)", "ops (...)"
// likewise; XN's census and the node-facts writer find every name distinct.
// MODULE: t2_cells_xk_static.c
// KAFLAGS: --cfl-cell-node-facts=/dev/null --cfl-cell-why=handler --cfl-cell-why-at=run_a:
// LOG: object names \(XN\): [0-9]+ objects, all distinct; .*; 4 objects named with their module \(2 name groups defined more than once\)
// LOG: fn handler \(t_cells_xk_static.c\)
// NOLOG: share the name
struct ops { void (*f)(void); };
static int hits;
static void handler(void) { hits++; }
static struct ops ops = { handler };
void run_b(void);
__attribute__((noinline)) void run_a(void) { ops.f(); } // CHECK: handler
int main(void) {
  run_a();
  run_b();
  return hits;
}
