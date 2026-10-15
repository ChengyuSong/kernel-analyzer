// t_cells_size_label.c — the size label (GAPS "Size label", Fable
// 2026-10-14): a block of sizeof(struct codec) whose first use is its
// first member (struct dev) is a struct codec, by the embedding table; two
// containers of the same size leave the first label (counted, candidates
// printed). kmem_cache_alloc_trace's size is its arg2 (summary SIZE). A
// size that is a multiple of the label's is an array of it (rule 1), so
// the containers here are not. kmalloc_trace(s, flags, size) (6.8.2): the
// row's SIZE(arg2) is read before the allocator table, whose kmalloc*
// prefix entry would take arg0, the cache.
// LOG: 2 relabeled to the container their size names, 1 ambiguous size labels
// LOG: ambiguous size label: struct.dev2 at 24 bytes: \{struct.boxa, struct.boxb\}
#include <stddef.h>
void *kmem_cache_alloc_trace(void *s, unsigned flags, size_t size);
void *kmalloc_trace(void *s, unsigned flags, size_t size);
void *kcache[4];
typedef void (*fn)(void);
struct dev { void *parent; long id; };
struct codec { struct dev core; long a, b; fn op; };      // 40 bytes, not a multiple of 16
struct dev3 { void *q; long n; };
struct codec3 { struct dev3 core; fn op3; };              // 24 bytes
struct dev2 { long x; long y; };
struct boxa { struct dev2 d; long p; };                  // 24 bytes
struct boxb { struct dev2 d; double r; };                // 24 bytes
struct boxa GA;
struct boxb GB;
void f1(void) {}
__attribute__((noinline)) void init_dev(struct dev *d) { d->parent = 0; d->id = 1; }
__attribute__((noinline)) void init_dev3(struct dev3 *d) { d->q = 0; d->n = 2; }
__attribute__((noinline)) void init_dev2(struct dev2 *d) { d->x = 1; }
int main(void) {
  struct dev *d = kmem_cache_alloc_trace(0, 0, sizeof(struct codec));
  init_dev(d);
  struct codec *c = (struct codec *)d;
  c->op = f1;
  struct dev3 *g = kmalloc_trace(kcache[1], 0, sizeof(struct codec3));
  init_dev3(g);
  ((struct codec3 *)g)->op3 = f1;
  struct dev2 *e = kmem_cache_alloc_trace(0, 0, sizeof(struct boxa));
  init_dev2(e);
  GA.p = 1;
  GB.r = 2.0;
  c->op(); // CHECK: f1
  return 0;
}
