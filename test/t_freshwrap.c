/* Pure-fresh wrapper promotion (task #17 step A): xmalloc only
 * allocates and returns — its callers must get per-callsite object
 * identities once the confirmer promotes it.
 *
 * Expected: a->fn() -> cb1, b->fn() -> cb2 (2 pairs exact).
 * Without --cfl-confirm-fresh: one shared internal malloc site ->
 * 4 pairs (cross-smeared). With it: 2/2.
 */
typedef unsigned long size_t;
extern void *malloc(size_t);

struct S {
  void (*fn)(void);
  int x;
};

__attribute__((noinline)) static void *xmalloc(size_t n) {
  void *p = malloc(n);
  if (!p)
    return 0;
  return p;
}

static void cb1(void) {}
static void cb2(void) {}

#define opaque(p) __asm__ volatile("" : : "r"(p) : "memory")

/* alloc-INIT wrapper (step B): store a formal into the fresh object.
 * Confirms as {FRESH, ST(*ret <- arg0)}; two callers must not
 * cross-smear (4 pairs without, 2/2 with --cfl-confirm-fresh). */
__attribute__((noinline)) static struct S *make(void (*f)(void)) {
  struct S *s = xmalloc(sizeof(struct S));
  if (s)
    s->fn = f;
  return s;
}

static void cb3(void) {}
static void cb4(void) {}

int main(void) {
  struct S *a = xmalloc(sizeof(struct S));
  a->fn = cb1;
  opaque(a); /* defeat store-to-load forwarding */
  a->fn(); /* expect cb1 only */
  struct S *b = xmalloc(sizeof(struct S));
  b->fn = cb2;
  opaque(b);
  b->fn(); /* expect cb2 only */
  struct S *c = make(cb3);
  opaque(c);
  c->fn(); /* expect cb3 only */
  struct S *d = make(cb4);
  opaque(d);
  d->fn(); /* expect cb4 only */
  return 0;
}
