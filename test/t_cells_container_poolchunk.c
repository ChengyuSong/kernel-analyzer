// t_cells_container_poolchunk.c — a pool's chunk allocated inside a
// container's body is pool storage, not an element (Fable 2026-10-14).
// nm-new at -O3 inlines objalloc_alloc into the hash tables' constructors,
// so the body's fresh blocks include the pool's new chunk, stored into the
// certified pool's handle field (objalloc.c:168 `o->chunks = chunk`); O3
// failed on it and bfd_hash was rejected at -O3. The chunk is covered by
// the pool's certificate and its carves are the elements: O3 exempts it
// (counted). The mint case's shape, with the pool inlined at -O2.
// CFLAGS: -O2
// LOG: O3 PASS \([1-9][0-9]* pool chunks allocated inside the body: certified pool storage\)
// LOG: VERIFIED \(rows applied\); the body optimized
#include <stdlib.h>
#include <string.h>
typedef void (*fn)(void);
struct bfd_hash_entry { struct bfd_hash_entry *next; const char *string; unsigned long hash; };
struct bfd_hash_table;
typedef struct bfd_hash_entry *(*newfunc_t)(struct bfd_hash_entry *, struct bfd_hash_table *, const char *);
struct bfd_hash_table { struct bfd_hash_entry **table; newfunc_t newfunc; void *memory; unsigned int size; unsigned int count; };
struct my_entry { struct bfd_hash_entry root; fn func; };
struct objalloc { char *current_ptr; unsigned int current_space; void *chunks; };
struct objalloc_chunk { struct objalloc_chunk *next; char *current_ptr; };
#define CHUNK_HEADER_SIZE 16
#define CHUNK_SIZE (4096 - 32)
static inline __attribute__((always_inline)) void *objalloc_alloc(struct objalloc *o, unsigned long len) {
  if (len == 0) len = 1;
  len = (len + 7) & ~7UL;
  if (len <= o->current_space) {
    o->current_ptr += len;
    o->current_space -= len;
    return o->current_ptr - len;
  }
  struct objalloc_chunk *chunk = malloc(CHUNK_SIZE);
  if (chunk == NULL) return NULL;
  chunk->next = o->chunks;
  chunk->current_ptr = NULL;
  o->current_ptr = (char *)chunk + CHUNK_HEADER_SIZE + len;
  o->current_space = CHUNK_SIZE - CHUNK_HEADER_SIZE - len;
  o->chunks = chunk;
  return (char *)chunk + CHUNK_HEADER_SIZE;
}
static inline __attribute__((always_inline)) void *bfd_hash_allocate(struct bfd_hash_table *table, unsigned int size) {
  return objalloc_alloc((struct objalloc *)table->memory, size);
}
static unsigned long bfd_hash_hash(const char *string) {
  unsigned long h = 0;
  while (*string) h = h * 31 + (unsigned char)*string++;
  return h;
}
__attribute__((noinline)) struct bfd_hash_entry *bfd_hash_insert(struct bfd_hash_table *table, const char *string, unsigned long hash) {
  struct bfd_hash_entry *hashp = (*table->newfunc)(NULL, table, string);
  unsigned int _index;
  if (hashp == NULL) return NULL;
  hashp->string = string;
  hashp->hash = hash;
  _index = hash % table->size;
  hashp->next = table->table[_index];
  table->table[_index] = hashp;
  table->count++;
  return hashp;
}
__attribute__((noinline)) struct bfd_hash_entry *bfd_hash_lookup(struct bfd_hash_table *table, const char *string, int create, int copy) {
  unsigned long hash = bfd_hash_hash(string);
  unsigned int _index = hash % table->size;
  struct bfd_hash_entry *hashp;
  (void)copy;
  for (hashp = table->table[_index]; hashp != NULL; hashp = hashp->next)
    if (hashp->hash == hash && strcmp(hashp->string, string) == 0) return hashp;
  if (!create) return NULL;
  return bfd_hash_insert(table, string, hash);
}
static struct bfd_hash_entry *my_newfunc(struct bfd_hash_entry *entry, struct bfd_hash_table *table, const char *string) {
  (void)string;
  if (entry == NULL) entry = (struct bfd_hash_entry *)bfd_hash_allocate(table, sizeof(struct my_entry));
  if (entry != NULL) ((struct my_entry *)entry)->func = NULL;
  return entry;
}
__attribute__((noinline)) int bfd_hash_table_init_n(struct bfd_hash_table *table, newfunc_t newfunc, unsigned int size) {
  table->table = calloc(size, sizeof(struct bfd_hash_entry *));
  if (table->table == NULL) return 0;
  table->size = size;
  table->count = 0;
  table->newfunc = newfunc;
  table->memory = calloc(1, sizeof(struct objalloc));
  return table->memory != NULL;
}
void f1(void) {}
void f2(void) {}
struct tables { struct bfd_hash_table syms; struct bfd_hash_table secs; };
int main(int argc, char **argv) {
  struct tables *t = malloc(sizeof *t);
  bfd_hash_table_init_n(&t->syms, my_newfunc, 61);
  bfd_hash_table_init_n(&t->secs, my_newfunc, 61);
  struct my_entry *a = (struct my_entry *)bfd_hash_lookup(&t->syms, "a", 1, 0);
  a->func = f1;
  struct my_entry *b = (struct my_entry *)bfd_hash_lookup(&t->secs, argv[0], 1, 0);
  b->func = f2;
  struct my_entry *c = (struct my_entry *)bfd_hash_lookup(&t->secs, argv[0], 0, 0);
  if (c && c->func) c->func(); // CHECK: f2 CHECK-NOT: f1
  return 0;
}
