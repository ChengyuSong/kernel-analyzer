// t_cells_cache.c — A5b (Fable 2026-10-21): a kmem_cache_alloc object is
// one object of its cache's size, read from the cache's one
// kmem_cache_create (k_itimer: its list_head initialized first, 256
// bytes). mk: the label is the list_head the inlined init_list writes, the
// cache's size is struct timer's, which embeds it at 0: named struct
// timer, one by size (before: one list_head, then an unknown tail). mk2:
// a cache global stored twice: refused, one then unknown as before. The
// receivers are void *, so no declaration names the struct (the kernel's
// IR has no debug info).
// CFLAGS: -O2
// LOG: extents: 0 arrays by size, 1 one by size, 0 header \+ data by size, 1 one then unknown
// LOG: cache sizes \(A5b\): 2 kmem_cache_\* allocations, 1 sized by their cache \(0 its label's size, 1 named by the one struct of that size embedding the label, 0 several such structs and 0 none: unlabeled, 0 with no mint label, 0 declared arrays kept\), 1 refused \(1 cache global stored 2 times\)
struct list_head { struct list_head *next, *prev; };
struct timer { struct list_head list; void (*fn)(void); long pad[5]; };
struct other { struct list_head list; void (*fn)(void); };
struct kmem_cache;
struct kmem_cache *kmem_cache_create(const char *, unsigned int, unsigned int, unsigned long, void (*)(void *));
void *kmem_cache_alloc(struct kmem_cache *, unsigned int);
static struct kmem_cache *timer_cache, *twice_cache;
void fa(void) {}
void fb(void) {}
static inline void init_list(struct list_head *h) { h->next = h; h->prev = h; }
void setup(void) {
  timer_cache = kmem_cache_create("timer", sizeof(struct timer), 0, 0, 0);
  twice_cache = kmem_cache_create("twice", sizeof(struct other), 0, 0, 0);
}
void setup2(void) { twice_cache = kmem_cache_create("twice2", sizeof(struct other), 0, 0, 0); }
void *gt, *go;
__attribute__((noinline)) void mk(void) {
  void *t = kmem_cache_alloc(timer_cache, 0);
  init_list(t);
  gt = t;
}
__attribute__((noinline)) void mk2(void) {
  void *o = kmem_cache_alloc(twice_cache, 0);
  init_list(o);
  go = o;
}
void set(void) {
  ((struct timer *)gt)->fn = fa;
  ((struct other *)go)->fn = fb;
}
void call(void) {
  ((struct timer *)gt)->fn(); // CHECK: fa CHECK-NOT: fb
}
