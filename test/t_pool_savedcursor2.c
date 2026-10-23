// A saved cursor handed out twice (Fable 2026-10-23): pool_mark keeps the
// pool's cursor in a -O0 local (a mark), bumps the cursor (the entry at
// the mark is handed out), reloads the local twice as data (a and b) and
// stores it back into the cursor (the release). Followed load by load,
// each data load is a carve of its own: one hand-out split into two
// objects that need not share their writes. The pool is refused ("saved
// cursor handed out twice"). KAMain.TA5 (no refusal) certifies it with
// two carves (:38, :40); here the presolve puts their sites under one
// representative (both reload one slot), so it still answers [f]; the
// refusal does not rest on that. TA6 answers [f, g] (the pool refused).
// Executed (clang -O0 -fsanitize=address): f once, exit 0, no report.
// LOG: PoolCarve: 1 pools \(1 refused\)
// LOG: refusing use pool_mark .*: saved cursor handed out twice: the slot stored at pool_mark .*:36 is carved at
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
struct ent { void (*fn)(void); long x; };
void f(void) {}
void g(void) {}
__attribute__((noinline)) static void (*pool_mark(struct pool *p))(void) {
  char *cur = p->cur;           /* the mark */
  p->cur += sizeof(struct ent); /* the entry at cur is handed out */
  struct ent *a = (struct ent *)cur;
  a->fn = f;
  struct ent *b = (struct ent *)cur;
  void (*r)(void) = b->fn;
  p->cur = cur;                 /* the release: stored back, a saved cursor */
  return r;
}
int main(void) {
  struct ent *e = pool_alloc(&P, sizeof *e); // chunk 1
  e->fn = g;
  void (*h)(void) = pool_mark(&P);
  h(); // CHECK: f
  return 0;
}
