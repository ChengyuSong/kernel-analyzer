// t_cells_slot_escape.c — rule S (Fable 2026-10-24): a slot whose address
// escapes to a call is not summarized and stays a memory node; S changes
// nothing for it. x holds g, set() writes f through its address, the call
// reads both stores (flow-insensitive memory): [f, g] before and after S.
// Executed (clang -O0 -fsanitize=address): f once, exit 0, no report.
typedef void (*fn)(void);
void f(void) {}
void g(void) {}
__attribute__((noinline)) static void set(fn *p) { *p = f; }
int main(void) {
  fn x = g;
  set(&x);
  x(); // CHECK: f g
  return 0;
}
