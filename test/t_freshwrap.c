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

int main(void) {
  struct S *a = xmalloc(sizeof(struct S));
  a->fn = cb1;
  opaque(a); /* defeat store-to-load forwarding */
  a->fn(); /* expect cb1 only */
  struct S *b = xmalloc(sizeof(struct S));
  b->fn = cb2;
  opaque(b);
  b->fn(); /* expect cb2 only */
  return 0;
}
