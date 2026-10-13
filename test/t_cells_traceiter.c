// t_cells_traceiter.c — tracepoints by flow (plan 3.53, kernel census,
// Fable 2026-10-13): __traceiter_X is a defined function, its dispatch
// `it_func = funcs->func` an ordinary indirect call. Probes registered on
// two tracepoints go through one registration body into arrays from one
// allocation site, so each iterator sees both probes: the shared pool is
// the expected answer (an allocation-site confluence, owner-keyed: plan
// 3.55), counted, not a bug.
// LOG: 2 __traceiter_ direct calls kept
#include <stdlib.h>
struct tracepoint_func { void *func; void *data; };
struct tracepoint { const char *name; struct tracepoint_func *funcs; };
struct tracepoint __tracepoint_x = { "x", 0 };
struct tracepoint __tracepoint_y = { "y", 0 };
typedef void (*probe_t)(void *, int);
void probe_x(void *d, int v) {}
void probe_y(void *d, int v) {}
__attribute__((noinline)) struct tracepoint_func *func_add(void *f) {
  struct tracepoint_func *n = malloc(2 * sizeof(*n));
  n[0].func = f;
  n[0].data = 0;
  n[1].func = 0;
  return n;
}
__attribute__((noinline)) int tracepoint_probe_register(struct tracepoint *tp, void *probe, void *data) {
  tp->funcs = func_add(probe);
  return 0;
}
__attribute__((noinline)) void __traceiter_x(void *d, int v) {
  for (struct tracepoint_func *it = __tracepoint_x.funcs; it && it->func; it++)
    ((probe_t)it->func)(it->data, v); // CHECK: probe_x probe_y
}
__attribute__((noinline)) void __traceiter_y(void *d, int v) {
  for (struct tracepoint_func *it = __tracepoint_y.funcs; it && it->func; it++)
    ((probe_t)it->func)(it->data, v);
}
int main(int argc, char **argv) {
  tracepoint_probe_register(&__tracepoint_x, (void *)probe_x, 0);
  tracepoint_probe_register(&__tracepoint_y, (void *)probe_y, 0);
  __traceiter_x(0, argc);
  __traceiter_y(0, argc);
  return 0;
}
