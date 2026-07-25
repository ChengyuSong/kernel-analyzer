/* Pair-correlated dispatch (task #28): C interface polymorphism via
 * (fn,data) registration pairs. reg() stores both halves into a shared
 * table; dispatch() icalls fn(data) — the pooled container decorrelates
 * the pairs, so each callback's inner icall cross-smears.
 *
 * Without summaries: dispatch icall -> {cb1,cb2}; cb1/cb2 formal p ->
 * {&d1,&d2}; inner icalls -> {f1,f2} each. 2 + 4 = 6 pairs.
 * With `reg INVOKE(arg0:f0<-arg1)` (test/t_pairs.summ): the callsite
 * binds data directly to the registered fn's formal and re-attributes
 * the invocation to the registration site; no actual->formal edges
 * feed reg's body, so the table (pooled channel) drains. Expected:
 * cb1 -> f1 only, cb2 -> f2 only (2/2 exact); dispatch icall empty
 * (its invocations are accounted at the registration callsites via
 * the Callees re-attribution edge).
 */
struct pair {
  void (*fn)(void *);
  void *data;
};

static struct pair table[4];
static int n;

__attribute__((noinline)) void reg(void (*fn)(void *), void *data) {
  table[n].fn = fn;
  table[n].data = data;
  n++;
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
static struct D d1 = { f1 };
static struct D d2 = { f2 };

static void cb1(void *p) { ((struct D *)p)->fp(); } /* expect f1 only */
static void cb2(void *p) { ((struct D *)p)->fp(); } /* expect f2 only */

int main(void) {
  reg(cb1, &d1);
  reg(cb2, &d2);
  dispatch();
  return 0;
}
