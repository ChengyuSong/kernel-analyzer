// S1 (Fable 2026-10-23): a handle field at offset 0 of a global pool read
// by its folded address (`load ptr, ptr @P`, no GEP at -O0) is keyed like
// any field access: mk's direct carve is one of the pool's carves, and
// its object receives e->fn (empty before: the access was invisible to
// the carve rule while its store was dropped as a handle store).
// Executed: f twice. 9547f21 answers [] at e->fn(); S1 [f].
// LOG: PoolCarve: 1 pools \(0 refused\), 3 handle fields .* 5 carve sites
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
__attribute__((noinline)) struct ent *mk(void) {
  struct ent *e = (struct ent *)P.cur; /* a carve read twice through one slot */
  P.cur += sizeof *e;
  e->fn = f;
  e->x = 1;
  return e;
}
int main(void) {
  struct ent *g = pool_alloc(&P, sizeof *g); // the first chunk
  g->fn = f;
  struct ent *e = mk();
  e->fn(); // CHECK: f
  g->fn();
  return 0;
}
