// t_cells_staticcall.c — kernel static_call as a named cell (plan 3.53,
// kernel census, Fable 2026-10-13): a direct call to the bodiless
// trampoline __SCT__a dispatches through the cell (@__SCK__a,
// static_call_key.func): its initializer (DEFINE_STATIC_CALL) and the
// store in __static_call_update's body (ordinary flow). Another key's
// initializer target never reaches it.
// LOG: 1 __SCT__ sites rewritten through their key
#include <stdlib.h>
struct static_call_key { void *func; union { unsigned long type; void *mods; }; };
void afn(void) {}
void a2fn(void) {}
void bfn(void) {}
struct static_call_key __SCK__a = { (void *)afn, { 1 } };
struct static_call_key __SCK__b = { (void *)bfn, { 1 } };
void __SCT__a(void);
void __SCT__b(void);
__attribute__((noinline)) void __static_call_update(struct static_call_key *key, void *tramp, void *func) {
  key->func = func;
}
int main(int argc, char **argv) {
  if (argc > 2) __static_call_update(&__SCK__a, (void *)__SCT__a, (void *)a2fn);
  __SCT__a(); // CHECK: afn a2fn CHECK-NOT: bfn
  return 0;
}
