// t_cells_cache_conflict.c — A5b (Fable 2026-10-21): a kmem_cache_alloc
// object whose cache size two structs embedding its label at 0 have
// (struct ta and struct tb, 32 bytes, both begin with a list_head; tb is
// used through the global gtb, so the IR has both): a conflict, unlabeled,
// its row. The receiver is a void *, so no
// declaration selects one; a slab object is one object, never read as an
// array of list_head (32 = 2 x 16).
// CFLAGS: -O2
// LOG: 1 kmem_cache_\* objects whose cache size several or no structs embedding their label have, A5b\)
// LOG: cache sizes \(A5b\): 1 kmem_cache_\* allocations, 1 sized by their cache \(0 its label's size, 0 named by the one struct of that size embedding the label, 1 several such structs and 0 none: unlabeled, 0 with no mint label, 0 declared arrays kept\), 0 refused
struct list_head { struct list_head *next, *prev; };
struct ta { struct list_head list; void (*fn)(void); long pad; };
struct tb { struct list_head list; void (*gn)(void); long pad; };
struct kmem_cache;
struct kmem_cache *kmem_cache_create(const char *, unsigned int, unsigned int, unsigned long, void (*)(void *));
void *kmem_cache_alloc(struct kmem_cache *, unsigned int);
static struct kmem_cache *both_cache;
void fa(void) {}
void setup(void) { both_cache = kmem_cache_create("both", sizeof(struct ta), 0, 0, 0); }
static inline void init_list(struct list_head *h) { h->next = h; h->prev = h; }
void *g;
void fb(void) {}
struct tb gtb = { { 0, 0 }, fb, 0 };
void (*gget(void))(void) { return gtb.gn; }
__attribute__((noinline)) void mk(void) {
  void *t = kmem_cache_alloc(both_cache, 0);
  init_list(t);
  g = t;
}
void set(void) { ((struct ta *)g)->fn = fa; }
void call(void) {
  ((struct ta *)g)->fn(); // CHECK: fa
}
