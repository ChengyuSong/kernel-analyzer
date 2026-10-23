// A saved cursor (libiberty objalloc_free_block, objalloc.c:277/295): a
// free-space pointer kept in a -O0 local and stored back into the cursor
// is a rewind through the local, not a hand-out; the pool stays certified.
// (A) before the fix (KAMain.TA3) carved at the slot store and refused the
// pool by one use ("a pointer into the free space used as data where
// nothing bumps it: store ptr %10, ptr %4" at pool_pop :32); with the fix
// (TA4/TA5) the pool is certified, the slot followed load by load.
// Executed (clang -O0 -fsanitize=address): f once, exit 0, no report.
// Answer [f] on both binaries (a refused pool is sound).
// LOG: PoolCarve: 1 pools \(0 refused\), .* 1 saved cursors
// LOG: PoolCarve: slot followed load by load at pool_pop .*:32: saved cursor stored back to pool\+0 at pool_pop .*:35
#include <stdlib.h>
struct chunk { struct chunk *next; char *saved; };
struct pool { char *cur; char *end; struct chunk *chunks; };
static struct pool P;
__attribute__((noinline)) static void refill(struct pool *p) {
  struct chunk *c = malloc(4096);
  c->next = p->chunks;
  c->saved = p->cur;
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
__attribute__((noinline)) static void pool_pop(struct pool *p) {
  struct chunk *c = p->chunks;
  char *cur = c->saved; /* the cursor saved in the chunk, kept in a local */
  p->chunks = c->next;
  free(c);
  p->cur = cur;
}
struct ent { void (*fn)(void); long x; };
void f(void) {}
int main(void) {
  struct ent *e = pool_alloc(&P, sizeof *e);
  e->fn = f;
  e->fn(); // CHECK: f
  pool_pop(&P);
  return 0;
}
