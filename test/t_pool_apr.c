// The APR pool shapes (apr_pools.c / apr_buckets_alloc.c / util.c, APR 1.7,
// APR-util 1.6, httpd 2.4), cut down: the carve forms (a) the pool struct
// bumped through its carry field, (b) the bucket small path's end slot,
// (c) whole tails, (d) bytes written before the bump, (e) the refill; the
// allocator's free lists (G1 link fields and a `ref` walk), the chunk
// source (G2), the end bound (G3) and the chunk formal (G5) (Fable
// 2026-10-23, P1).
// Executed: fa, fb, fc, fd (one each). 732d45a (the pool refused by 24
// uses) answers [fa, fb, fc, fd] at each of the four calls; P1 (the pool
// certified) answers [fa], [fb] (this cut-down palloc, which has no
// abort_fn call, is confirmed FRESH: an object per caller; linked httpd's
// apr_palloc is not, R3 rejecting its pool->abort_fn(APR_ENOMEM) call
// through a pointer), [fc, fd], [fc, fd] (bucket_alloc returns its
// hand-out + 32, not a fresh object's start: one object per carve site,
// not per caller; an offset-carrying FRESH is out of scope).
// LOG: PoolCarve: POOL fields
// LOG: ConfirmFresh: pool hand-outs 2 \(carve sites before 2\)
#include <stdlib.h>
#include <string.h>
typedef struct apr_memnode_t apr_memnode_t;
struct apr_memnode_t {
  apr_memnode_t *next;
  apr_memnode_t **ref;
  unsigned index;
  unsigned free_index;
  char *first_avail;
  char *endp;
};
#define ALIGN(s, b) (((s) + ((b)-1)) & ~((b)-1))
#define MEMNODE_SIZE ALIGN(sizeof(apr_memnode_t), 8)
typedef struct allocator_t { size_t max_index; apr_memnode_t *free[20]; } allocator_t;
typedef struct pool_t {
  struct pool_t *parent;
  allocator_t *allocator;
  apr_memnode_t *active;
  apr_memnode_t *self;
  char *self_first_avail;
} pool_t;
#define POOL_SIZE ALIGN(sizeof(pool_t), 8)
static allocator_t A;
// G2 (a chunk source) and G1 (free lists walked through `ref`), (e) refill.
__attribute__((noinline)) static apr_memnode_t *allocator_alloc(allocator_t *a, size_t in) {
  size_t size = ALIGN(in + MEMNODE_SIZE, 4096);
  size_t index = (size >> 12) - 1;
  apr_memnode_t *node, **ref;
  if (index < 20) {
    ref = &a->free[index];
    while ((node = *ref) == NULL && index < 19) ref++, index++;
    if (node) {
      *ref = node->next;
      goto have;
    }
  }
  ref = &a->free[0];
  while ((node = *ref) != NULL && node->index < index) ref = &node->next;
  if (node) {
    *ref = node->next;
    goto have;
  }
  if ((node = malloc(size)) == NULL) return NULL;
  node->index = (unsigned)index;
  node->endp = (char *)node + size; // G3: the end bound
have:
  node->next = NULL;
  node->first_avail = (char *)node + MEMNODE_SIZE; // (e) refill
  return node;
}
// G5: node, a chunk formal (every call passes a chunk base).
__attribute__((noinline)) static void allocator_free(allocator_t *a, apr_memnode_t *node) {
  unsigned i = node->index < 20 ? node->index : 0;
  node->next = a->free[i];
  a->free[i] = node;
}
// (a) the pool struct carved from its own node, bumped through its field.
__attribute__((noinline)) static pool_t *pool_create(pool_t *parent) {
  apr_memnode_t *node = allocator_alloc(&A, 8192 - MEMNODE_SIZE);
  if (!node) return NULL;
  node->next = node;
  node->ref = &node->next;
  pool_t *pool = (pool_t *)node->first_avail;
  pool->self_first_avail = (char *)pool + POOL_SIZE;
  node->first_avail = pool->self_first_avail;
  pool->allocator = &A;
  pool->active = pool->self = node;
  pool->parent = parent;
  return pool;
}
// apr_palloc: before-bump, its node switch and the ring list (G1 through ref).
__attribute__((noinline)) void *palloc(pool_t *pool, size_t in) {
  size_t size = ALIGN(in, 8);
  apr_memnode_t *active = pool->active, *node;
  void *mem;
  if (size <= (size_t)(active->endp - active->first_avail)) {
    mem = active->first_avail;
    active->first_avail += size;
    return mem;
  }
  if ((node = allocator_alloc(pool->allocator, size)) == NULL) return NULL;
  mem = node->first_avail;
  node->first_avail += size;
  node->ref = active->ref;
  *node->ref = node;
  node->next = active;
  active->ref = &node->next;
  pool->active = node;
  return mem;
}
// (d) bytes written before the bump: a cursor kept in a char pointer, a
// byte copy into the free space, then the bump that hands them out.
typedef struct fmt_t { char *curpos; char *endpos; } fmt_t;
__attribute__((noinline)) char *pstrcat2(pool_t *pool, const char *a, const char *b) {
  apr_memnode_t *active = pool->active;
  fmt_t f;
  f.curpos = active->first_avail;
  f.endpos = active->endp - 1;
  size_t la = strlen(a), lb = strlen(b);
  if (la + lb + 1 > (size_t)(f.endpos - f.curpos)) return NULL;
  memcpy(f.curpos, a, la);
  f.curpos += la;
  memcpy(f.curpos, b, lb + 1);
  char *strp = active->first_avail;
  active->first_avail += ALIGN(la + lb + 1, 8);
  return strp;
}
// (b) the bucket small path: the end computed first (in a slot), on the
// node it carves from; (c) the large path's whole tail.
typedef struct node_header_t { size_t size; void *alloc; apr_memnode_t *memnode; struct node_header_t *next; } node_header_t;
typedef struct bucket_alloc_t { pool_t *pool; allocator_t *allocator; node_header_t *freelist; apr_memnode_t *blocks; } bucket_alloc_t;
#define HDR ALIGN(sizeof(node_header_t), 8)
#define SMALL 160
__attribute__((noinline)) void *bucket_alloc(size_t size, bucket_alloc_t *list) {
  node_header_t *node;
  apr_memnode_t *active = list->blocks;
  char *endp;
  size += HDR;
  if (size <= SMALL) {
    if (list->freelist) {
      node = list->freelist;
      list->freelist = node->next;
    } else {
      endp = active->first_avail + SMALL;
      if (endp >= active->endp) {
        list->blocks = allocator_alloc(list->allocator, 8192 - MEMNODE_SIZE);
        if (!list->blocks) {
          list->blocks = active;
          return NULL;
        }
        list->blocks->next = active;
        active = list->blocks;
        endp = active->first_avail + SMALL;
      }
      node = (node_header_t *)active->first_avail;
      node->alloc = list;
      node->memnode = active;
      node->size = SMALL;
      active->first_avail = endp;
    }
  } else {
    apr_memnode_t *memnode = allocator_alloc(list->allocator, size);
    if (!memnode) return NULL;
    node = (node_header_t *)memnode->first_avail;
    node->alloc = list;
    node->memnode = memnode;
    node->size = size;
  }
  return ((char *)node) + HDR;
}
__attribute__((noinline)) void bucket_free(void *mem) {
  node_header_t *node = (node_header_t *)((char *)mem - HDR);
  bucket_alloc_t *list = node->alloc;
  if (node->size == SMALL) {
    node->next = list->freelist;
    list->freelist = node;
  } else {
    allocator_free(list->allocator, node->memnode);
  }
}
struct rec { void (*h)(void); long n; };
void fa(void) {}
void fb(void) {}
void fc(void) {}
void fd(void) {}
int main(int argc, char **argv) {
  pool_t *p = pool_create(NULL);
  struct rec *r = palloc(p, sizeof *r);
  r->h = fa;
  struct rec *big = palloc(p, 9000); // a new node: the ring list
  big->h = fb;
  char *s = pstrcat2(p, "x", argv[0]);
  bucket_alloc_t L = {p, &A, NULL, allocator_alloc(&A, 8192 - MEMNODE_SIZE)};
  struct rec *b = bucket_alloc(sizeof *b, &L);
  b->h = fc;
  struct rec *w = bucket_alloc(4096, &L); // the whole tail
  w->h = fd;
  r->h();
  big->h(); // CHECK: fb CHECK-NOT: fa
  b->h();
  w->h();
  bucket_free(w);
  return s != NULL && argc > 0 ? 0 : 1;
}
