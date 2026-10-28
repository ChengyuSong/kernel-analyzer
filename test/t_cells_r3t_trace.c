// t_cells_r3t_trace.c — under --cfl-trace-func, R3 (ConfirmFresh: no
// pointer side effects besides the fresh object's init) scans the whole
// body and prints every rejecting instruction with its class, then the
// return path's sources (R3t, Fable 2026-10-27; instrument only). The
// decision stays at the first rejection (the "R3: ... side effect" line).
// wrap stores a formal into a global (pointer store) and passes it on
// (pointer-arg call); it returns malloc's result or null, both through
// O0 slots (the reloads resolve to the stores that reach them).
// KAFLAGS: --cfl-trace-func=wrap
// LOG: ConfirmFresh R3: wrap side effect store ptr
// LOG: ConfirmFresh R3t: wrap reject 1/2 \[pointer store\] @t_cells_r3t_trace.c:23 store ptr
// LOG: ConfirmFresh R3t: wrap reject 2/2 \[pointer-arg call\] @t_cells_r3t_trace.c:24 call void @sink
// LOG: ConfirmFresh R3t: wrap return path: allocator result malloc \(via slot\), null \(via slot\)$
#include <stdlib.h>
void *G, *G2;
__attribute__((noinline)) void sink(char *s) { G2 = s; }
void (*fp)(void);
void tgt(void) {}
__attribute__((noinline)) void call_it(void) { fp(); } // CHECK: tgt
__attribute__((noinline)) char *wrap(unsigned n, char *name) {
  char *p = malloc(n);
  if (!p) return 0;
  G = name;
  sink(name);
  return p;
}
int main(int argc, char **argv) {
  fp = tgt;
  call_it();
  return wrap(argc, argv[0]) != 0;
}
