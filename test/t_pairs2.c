/* Dynamic-fn INVOKE fallback through the allocator branch (the
 * smpboot/kthread_create_on_cpu shape that the kernel run caught):
 * spawn() is summarized FRESH + INVOKE, and spawn_wrap() passes its
 * OWN FORMALS to spawn — the fn operand is not a constant there, so
 * the callsite must fall back to pooled arg wiring INTO spawn's body
 * (feeding the table the dispatcher reads), despite the FRESH atom
 * routing the callsite through the allocator branch.
 *
 * With t_pairs2.summ:
 *   cb1 -> f1, cb2 -> f2 (direct registrations, INVOKE-bound exact)
 *   cb3 -> f3 (wrapper registration: pooled through the table; the
 *              table holds only wrapper-fed pairs, so still 1 target)
 *   dispatch icall -> cb3 only (direct regs drained/re-attributed)
 * Buggy needPooled-dropped behavior: cb3's inner icall loses f3
 * (0 targets) because spawn's body never receives fn/data.
 */
typedef unsigned long size_t;
extern void *malloc(size_t);

struct pair {
  void (*fn)(void *);
  void *data;
};

static struct pair table[4];
static int n;

__attribute__((noinline)) void *spawn(void (*fn)(void *), void *data) {
  table[n].fn = fn;
  table[n].data = data;
  n++;
  return malloc(64); /* stand-in task handle: FRESH models this */
}

__attribute__((noinline)) void *spawn_wrap(void (*fn)(void *), void *data) {
  return spawn(fn, data); /* fn is a formal: dynamic at the callsite */
}

__attribute__((noinline)) void dispatch(void) {
  for (int i = 0; i < n; i++)
    table[i].fn(table[i].data);
}

struct D {
  void (*fp)(void);
};

static void f1(void) {}
static void f2(void) {}
static void f3(void) {}
static struct D d1 = { f1 };
static struct D d2 = { f2 };
static struct D d3 = { f3 };

static void cb1(void *p) { ((struct D *)p)->fp(); } /* expect f1 only */
static void cb2(void *p) { ((struct D *)p)->fp(); } /* expect f2 only */
static void cb3(void *p) { ((struct D *)p)->fp(); } /* expect f3 only */

int main(void) {
  void *a = spawn(cb1, &d1);
  void *b = spawn(cb2, &d2);
  void *c = spawn_wrap(cb3, &d3);
  dispatch();
  return (a && b && c) ? 0 : 1;
}
