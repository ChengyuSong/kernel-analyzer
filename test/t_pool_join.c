// Plan 3.53 rule 3: a pool carve joined with a formal (allocate unless the
// caller provides the object: bfd_hash_newfunc's `entry`). At -O3 the
// carve is inlined into newent, and the result is phi [carve, entry]: only
// the carve is fresh; the caller's object keeps flowing through the join.
// CFLAGS: -O3
#include <stdlib.h>
struct chunk { size_t size; struct chunk *next; };
struct pool { char *cur; char *end; struct chunk *chunks; };
static struct pool P;
__attribute__((noinline)) static void refill(struct pool *p) {
  struct chunk *c = malloc(4096);
  c->size = 4096;
  c->next = p->chunks;
  p->chunks = c;
  p->cur = (char *)c + sizeof(struct chunk);
  p->end = (char *)c + 4096;
}
static inline void *pool_alloc(struct pool *p, size_t n) {
  if ((size_t)(p->end - p->cur) < n) refill(p);
  char *r = p->cur;
  p->cur = r + n;
  return r;
}
struct ent { void (*fn)(void); long x; };
__attribute__((noinline)) static struct ent *newent(struct pool *pp, struct ent *e) {
  if (!e) e = pool_alloc(pp, sizeof *e);
  return e;
}
void f(void) {}
void g(void) {}
static struct ent given;
int main(int argc, char **argv) {
  given.fn = f;
  struct ent *e = newent(argc > 3 ? &P : (struct pool *)argv, argc > 1 ? &given : NULL);
  if (argc > 2) e->fn = g;
  e->fn(); // CHECK: f g
  return 0;
}
