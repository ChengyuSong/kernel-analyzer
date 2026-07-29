// task #30 walker v2 micro: helper-mediated registration.
//
// reg_ops(o, t) is the cdev_init shape: the table pointer escapes into
// a direct call and is stored into a field of another formal. The v2
// recipe (FORMAL 1 stored into FORMAL 0) must certify ops_a/ops_b with
// containers = the caller-side actuals (&OA, &OB).
//
// mk_widget(t, cb) is the relay_open shape: the table is stored into a
// helper-allocated object returned to the caller — recipe RETALLOC,
// container = the callsite value.
//
// direct_probe() reads ops_a directly (member load) — v2 must classify
// that benign instead of failing the certificate.
//
// EXPECTED with --cfl-ops-pairs: all tables certified. The inner-icall
// smear through the SHARED writer (reg_ops's single store) is the
// recorded shared-writer collapse — cells merge through the helper's
// deref cell, so a1/b1 may still pool {cba,cbb} until store-side
// splitting (helper summaries) lands. The certificate side is what
// this micro pins.

struct obj;
struct ops {
  void (*op1)(struct obj *);
  void (*op2)(struct obj *);
};
struct obj {
  const struct ops *ops;
  void (*cb)(void);
};

static void cba(void) {}
static void cbb(void) {}

static void a1(struct obj *o) { o->cb(); }
static void a2(struct obj *o) { o->cb(); }
static void b1(struct obj *o) { o->cb(); }
static void b2(struct obj *o) { o->cb(); }

static const struct ops ops_a = {a1, a2};
static const struct ops ops_b = {b1, b2};

static struct obj OA, OB;

// cdev_init shape: table escapes into a call, lands in formal 0's field
void reg_ops(struct obj *o, const struct ops *t) { o->ops = t; }

// relay_open shape: table lands in an allocated object that is returned
extern void *malloc(unsigned long);
struct obj *mk_widget(const struct ops *t, void (*cb)(void)) {
  struct obj *w = (struct obj *)malloc(sizeof(struct obj));
  if (!w)
    return 0;
  w->ops = t;
  w->cb = cb;
  return w;
}

void dispatch(struct obj *o) { o->ops->op1(o); }

// direct member read of a table (benign, must not fail the certificate)
int direct_probe(void) { return ops_a.op1 != 0; }

int main(void) {
  reg_ops(&OA, &ops_a);
  OA.cb = cba;
  reg_ops(&OB, &ops_b);
  OB.cb = cbb;
  dispatch(&OA);
  dispatch(&OB);
  struct obj *w = mk_widget(&ops_a, cba);
  if (w)
    dispatch(w);
  return direct_probe();
}
