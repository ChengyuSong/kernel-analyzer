/* kmemdup = alloc + memcpy: the dup'd object must carry the source's
 * function pointers (soundness), and two callers' dups must NOT
 * conflate (precision: 2 icalls x 1 target each, not 2x2).
 *
 * Expected ICALLs: call_a -> cb_a ; call_b -> cb_b   (2 pairs exact)
 * Pre-summary status: kmemdup is in isAllocFn, its body is skipped,
 * so the copy is DROPPED -> both icalls resolve to nothing (0 pairs,
 * unsound). Conflated-but-sound would be 4 pairs.
 */
typedef unsigned long size_t;

struct ops {
  int (*fp)(int);
  int pad;
};

/* stand-in for the kernel definition: body present, listed in
 * isAllocFn, body edges skipped by the allocator treatment */
void *__kmalloc(size_t n, unsigned flags);
__attribute__((noinline)) void *kmemdup(const void *src, size_t len, unsigned gfp) {
  char *p = __kmalloc(len, gfp);
  if (p)
    for (size_t i = 0; i < len; i++)
      p[i] = ((const char *)src)[i];
  return p;
}

static int cb_a(int x) { return x + 1; }
static int cb_b(int x) { return x - 1; }

static const struct ops ops_a = { cb_a, 0 };
static const struct ops ops_b = { cb_b, 1 };

int call_a(void) {
  struct ops *d = kmemdup(&ops_a, sizeof(ops_a), 0);
  return d->fp(1);
}

int call_b(void) {
  struct ops *d = kmemdup(&ops_b, sizeof(ops_b), 0);
  return d->fp(2);
}
