// S1: a pool handle read through a pointer the IR does not name (an
// untyped pointer kept in memory): the carve rule never judged it, the
// solve finds it, and the pool is withdrawn: its carves and handle
// stores are built as ordinary code for the next iteration, which reads
// g's store through the chunk (empty of g before). At run time peek()
// returns the cursor the next pool_alloc hands out, so h == e.
// Executed: g. 9547f21 answers [f] (misses the executed target: peek's
// load of P.cur through the folded @P is unjudged and the carve model
// drops the handle stores); S1 [f, g].
// LOG: 1 accesses outside the pools. forms, 1 pools withdrawn at the solve \(1 in all\)
// LOG: PoolCarve: withdrawn at the solve: 1 pools; 2 carves and 4 handle stores built as ordinary code
#include <stdlib.h>
struct chunk { struct chunk *next; };
struct pool { char *cur; char *end; struct chunk *chunks; };
static struct pool P;
__attribute__((noinline)) static void refill(struct pool *p) {
  struct chunk *c = malloc(4096);
  c->next = p->chunks;
  p->chunks = c;
  p->cur = (char *)c + sizeof(struct chunk);
  p->end = (char *)c + 4096;
}
__attribute__((noinline)) static void *pool_alloc(struct pool *p, size_t n) {
  if ((size_t)(p->end - p->cur) < n) refill(p);
  char *r = p->cur;
  p->cur += n;
  return r;
}
struct ent { void (*fn)(void); long x; };
void f(void) {}
void g(void) {}
void *holder;
__attribute__((noinline)) void *peek(void) {
  char **c = holder; /* reads P.cur, unseen by the carve rule */
  return *c;
}
int main(void) {
  holder = &P;
  (void)pool_alloc(&P, 8); // the first chunk
  struct ent *h = peek();  // the cursor: e's address below
  struct ent *e = pool_alloc(&P, sizeof *e);
  e->fn = f;
  h->fn = g;
  e->fn(); // CHECK: f g
  return 0;
}
