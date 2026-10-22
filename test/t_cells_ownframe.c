// t_cells_ownframe.c — A5c (Fable 2026-10-21): a site's declaration
// (siteDeclared, sitePtrArray, siteScalar) comes only from a receiver in
// the call's own frame, the rule A4 and A5a use. At -O2 keep_a is inlined
// into mk and its formal `p` (struct a *) receives malloc's result through
// a dbg.value; it is keep_a's variable, not the site's, so it declares
// nothing: mk's own receiver `v` is a void *, and the site has no
// declaration (before: declared struct a by the sibling formal). The
// object is labeled by its struct b access either way.
// CFLAGS: -O2
// LOG: 0 declared through a shared slot; 1 with no declaration \(1 received by a variable or field whose type declares nothing
#include <stdlib.h>
struct a { long x; long y; };
struct b { void (*f)(void); long y; };
struct a *ga;
static inline void keep_a(struct a *p) { ga = p; }
struct a ga0;
long gety(void) { return ga0.y; }
void fa(void) {}
void *g;
__attribute__((noinline)) void mk(void) {
  void *v = malloc(16);
  keep_a(v);
  ((struct b *)v)->f = fa;
  g = v;
}
void call(void) { ((struct b *)g)->f(); } // CHECK: fa
