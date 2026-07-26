/* --cfl-confirm-invoke DIRECT shape (task #28 tier 2): run_cb is a
 * synchronous higher-order fn — its fn formal is invoked with its data
 * formal, nothing else touches the pointer formals -> auto-confirms as
 * `run_cb INVOKE(arg0:f0<-arg1)`. run_cb_leak stores data into a
 * global (escape): the completeness check must REJECT it (LEDGER
 * "escape"), leaving its pooled behavior unchanged.
 *
 * Without --cfl-confirm-invoke (8 + 4 = 12 pairs):
 *   run_cb icall -> {cb1,cb2}; cb1/cb2 inner -> {f1,f2} each (pooled)
 *   run_cb_leak icall -> {cb3,cb4}; cb3/cb4 inner -> {f3,f4} each
 * With it (8 pairs):
 *   cb1->f1, cb2->f2 exact; run_cb's own icall drains (re-attributed);
 *   run_cb_leak side unchanged: icall {cb3,cb4}, inner {f3,f4} each.
 */
struct D {
  void (*fp)(void);
};

static void f1(void) {}
static void f2(void) {}
static void f3(void) {}
static void f4(void) {}
static struct D d1 = { f1 };
static struct D d2 = { f2 };
static struct D d3 = { f3 };
static struct D d4 = { f4 };

static void cb1(void *p) { ((struct D *)p)->fp(); } /* expect f1 only */
static void cb2(void *p) { ((struct D *)p)->fp(); } /* expect f2 only */
static void cb3(void *p) { ((struct D *)p)->fp(); } /* expect f3,f4 */
static void cb4(void *p) { ((struct D *)p)->fp(); } /* expect f3,f4 */

__attribute__((noinline, weak)) int run_cb(void (*fn)(void *), void *data) {
  if (!fn)
    return -1;
  fn(data);
  return 0;
}

void *g_leak;
__attribute__((noinline, weak)) int run_cb_leak(void (*fn)(void *), void *data) {
  g_leak = data; /* pointer formal escapes: must NOT confirm */
  fn(data);
  return 0;
}

int main(void) {
  run_cb(cb1, &d1);
  run_cb(cb2, &d2);
  run_cb_leak(cb3, &d3);
  run_cb_leak(cb4, &d4);
  return 0;
}
