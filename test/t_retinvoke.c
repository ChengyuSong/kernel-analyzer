// task #31: INVOKE ret-transparency atom. find() is a ret-pooling HOF
// (the fwnode_connection_find_match shape): it invokes the constant
// matcher and returns its result. Pooled, find's shared return node
// mixes both matchers' objects, so each caller's dispatch smears
// {cba, cbb}. With `find INVOKE(arg1:ret)` the callsite return binds
// to THAT matcher's return only:
//   use_a -> cba only, use_b -> cbb only;
// find's internal icall (match targets {match_a, match_b}) unchanged
// (args stay pooled — pure-ret claims nothing about them).

struct obj {
  void (*cb)(void);
};

static void cba(void) {}
static void cbb(void) {}

static struct obj OA = {cba};
static struct obj OB = {cbb};

static void *match_a(void *key) { (void)key; return &OA; }
static void *match_b(void *key) { (void)key; return &OB; }

void *find(void *key, void *(*match)(void *)) {
  void *r = match(key);
  if (r)
    return r;
  return 0;
}

static struct obj *pa, *pb;

void use_a(void) {
  pa = (struct obj *)find(0, match_a);
  if (pa)
    pa->cb();
}

void use_b(void) {
  pb = (struct obj *)find(0, match_b);
  if (pb)
    pb->cb();
}

int main(void) {
  use_a();
  use_b();
  return 0;
}
