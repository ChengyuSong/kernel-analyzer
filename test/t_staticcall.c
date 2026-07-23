/* static_call shape (task #14): __SCT__X is an undefined trampoline;
 * its target set = __SCK__X key initializer + everything stored by
 * __static_call_update (in-corpus, stores key->func in plain IR).
 * Expected: both __SCT__test callsites resolve to {f1, f2}. */
struct static_call_key { void *func; };
static int f1(int x) { return x; }
static int f2(int x) { return x + 1; }
struct static_call_key __SCK__test = { (void *)f1 };
extern int __SCT__test(int);
void __static_call_update(struct static_call_key *k, void *tramp,
                          void *func) {
  k->func = func;
}
int main(void) {
  int s = __SCT__test(1);
  __static_call_update(&__SCK__test, 0, (void *)f2);
  return s + __SCT__test(2);
}
