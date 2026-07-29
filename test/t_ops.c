// task #30 step 2 micro: certified (ops-global, container) pairs.
// Two containers OA/OB carry different certified ops tables and
// different inner callbacks. The dispatcher calls o->ops->op1(o); each
// op fires the inner icall o->cb().
//
// Pooled (no --cfl-ops-pairs): the shared receiver formal of a1/b1
// mixes OA and OB, so every inner icall smears {cba, cbb}.
// Tightened (--cfl-ops-pairs): a1/a2's receiver binds only to OA
// (container of ops_a), b1/b2's only to OB — inner icalls exact:
//   a1,a2 -> cba only; b1,b2 -> cbb only.
// Dispatch-site targets must be unchanged: {a1,a2,b1,b2}.

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

void dispatch(struct obj *o) { o->ops->op1(o); }

int main(void) {
  OA.ops = &ops_a;
  OA.cb = cba;
  OB.ops = &ops_b;
  OB.cb = cbb;
  dispatch(&OA);
  dispatch(&OB);
  return 0;
}
