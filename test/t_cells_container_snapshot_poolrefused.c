// t_cells_container_snapshot_poolrefused.c — (ii) r2's control (Fable
// 2026-10-19): the pool case with the pool REFUSED by Carves.cc (scribble
// writes data at the free space's start, where nothing bumps it): its
// carves are no allocation, so bfd_zalloc is no wrapper and the walk
// declines on the refused pool's carve, named with its verdict. At the
// commit before it declined on the pool's bump step ("a runtime step"),
// the pool unnamed.
// LOG: PoolCarve: REFUSED fields objalloc\+0
// LOG: not unreachable by name \(the word's objects are open: [0-9]+ reasons, e.g. a carve of pool objalloc\+0 at .*\(REFUSED fields objalloc\+0
// NOLOG: ASSUMPTION unreachable by name
// NOLOG: ASSUMPTION pool objalloc
#include <stdlib.h>
#include <string.h>
typedef void (*fn)(void);
struct bfd_hash_entry { struct bfd_hash_entry *next; const char *string; unsigned long hash; };
struct bfd_hash_table;
typedef struct bfd_hash_entry *(*newfunc_t)(struct bfd_hash_entry *, struct bfd_hash_table *, const char *);
struct bfd_hash_table {
  struct bfd_hash_entry **table; newfunc_t newfunc; void *memory; unsigned int size; unsigned int count;
  unsigned int entsize;
};
struct my_entry { struct bfd_hash_entry root; fn fa; fn fb; };
struct big_entry { struct bfd_hash_entry root; fn fa; fn fb; fn fc; };
void ga(void) {}
void gb(void) {}
__attribute__((noinline)) void *bfd_hash_allocate(struct bfd_hash_table *table, unsigned int size) {
  (void)table;
  return malloc(size);
}
static unsigned long bfd_hash_hash(const char *string) {
  unsigned long h = 0;
  while (*string) h = h * 31 + (unsigned char)*string++;
  return h;
}
struct bfd_hash_entry *bfd_hash_insert(struct bfd_hash_table *table, const char *string, unsigned long hash) {
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
struct bfd_hash_entry *bfd_hash_lookup(struct bfd_hash_table *table, const char *string, int create, int copy) {
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
  if (entry != NULL) {
    ((struct my_entry *)entry)->fa = ga;
    ((struct my_entry *)entry)->fb = gb;
  }
  return entry;
}
static struct bfd_hash_entry *big_newfunc(struct bfd_hash_entry *entry, struct bfd_hash_table *table, const char *string) {
  (void)string;
  if (entry == NULL) entry = (struct bfd_hash_entry *)bfd_hash_allocate(table, sizeof(struct big_entry));
  if (entry != NULL) ((struct big_entry *)entry)->fc = ga;
  return entry;
}
__attribute__((noinline)) int bfd_hash_table_init_n(struct bfd_hash_table *table, newfunc_t newfunc, unsigned int entsize,
                                                    unsigned int size) {
  table->table = calloc(size, sizeof(struct bfd_hash_entry *));
  if (table->table == NULL) return 0;
  table->size = size;
  table->count = 0;
  table->entsize = entsize;
  table->newfunc = newfunc;
  return 1;
}
struct owner;
struct bfd { const char *filename; union { struct owner *own; void *any; } tdata; void *memory; };
#define AS_NEEDED 1
struct owner { struct bfd_hash_table table; unsigned int lo : 6; unsigned int cls : 4; unsigned int hi : 3; };
__attribute__((noinline)) struct my_entry *snap(struct bfd *b, const char *name) {
  struct owner *o = b->tdata.own;
  struct bfd_hash_table *t = &o->table;
  size_t tabsize = 0;
  size_t entsize = 0;
  unsigned int i;
  void *old_tab, *old_ent;
  struct bfd_hash_entry *p;
  if ((o->cls & AS_NEEDED) == 0) return (struct my_entry *)bfd_hash_lookup(t, name, 1, 0);
  for (i = 0; i < t->size; i++)
    for (p = t->table[i]; p != NULL; p = p->next) entsize += t->entsize;
  tabsize = t->size * sizeof(struct bfd_hash_entry *);
  old_tab = malloc(tabsize + entsize);
  if (old_tab == NULL) return NULL;
  old_ent = (char *)old_tab + tabsize;
  memcpy(old_tab, t->table, tabsize);
  for (i = 0; i < t->size; i++)
    for (p = t->table[i]; p != NULL; p = p->next) {
      memcpy(old_ent, p, t->entsize);
      old_ent = (char *)old_ent + t->entsize;
    }
  bfd_hash_lookup(t, name, 1, 0);
  old_ent = (char *)old_tab + tabsize;
  memcpy(t->table, old_tab, tabsize);
  for (i = 0; i < t->size; i++)
    for (p = t->table[i]; p != NULL; p = p->next) {
      memcpy(p, old_ent, t->entsize);
      old_ent = (char *)old_ent + t->entsize;
    }
  free(old_tab);
  return (struct my_entry *)bfd_hash_lookup(t, name, 0, 0);
}
__attribute__((noinline)) void set_lo(struct bfd *b) { b->tdata.own->lo = 5; }
__attribute__((noinline)) void drop_needed(struct bfd *b) { b->tdata.own->cls = b->tdata.own->cls & ~AS_NEEDED; }
struct objalloc { char *current_ptr; unsigned int current_space; void *chunks; };
struct objalloc_chunk { struct objalloc_chunk *next; char *current_ptr; };
#define OBJALLOC_ALIGN 8
#define CHUNK_HEADER_SIZE 16
#define CHUNK_SIZE (4096 - 32)
#define BIG_REQUEST (512)
void *_objalloc_alloc(struct objalloc *, unsigned long);
// libiberty's objalloc.h and objalloc.c (binutils 5279478), as nm-new has them.
#define objalloc_alloc(o, l)                                                 \
  __extension__({                                                            \
    struct objalloc *__o = (o);                                              \
    unsigned long __len = (l);                                               \
    if (__len == 0) __len = 1;                                               \
    __len = (__len + OBJALLOC_ALIGN - 1) & ~(OBJALLOC_ALIGN - 1);            \
    (__len != 0 && __len <= __o->current_space                               \
         ? (__o->current_ptr += __len, __o->current_space -= __len,          \
            (void *)(__o->current_ptr - __len))                              \
         : _objalloc_alloc(__o, __len));                                     \
  })
__attribute__((noinline)) void *_objalloc_alloc(struct objalloc *o, unsigned long original_len) {
  unsigned long len = original_len;
  if (len == 0) len = 1;
  len = (len + OBJALLOC_ALIGN - 1) & ~(OBJALLOC_ALIGN - 1);
  if (len + CHUNK_HEADER_SIZE < original_len) return NULL;
  if (len <= o->current_space) {
    o->current_ptr += len;
    o->current_space -= len;
    return (void *)(o->current_ptr - len);
  }
  if (len >= BIG_REQUEST) {
    char *ret;
    struct objalloc_chunk *chunk;
    ret = (char *)malloc(CHUNK_HEADER_SIZE + len);
    if (ret == NULL) return NULL;
    chunk = (struct objalloc_chunk *)ret;
    chunk->next = (struct objalloc_chunk *)o->chunks;
    chunk->current_ptr = o->current_ptr;
    o->chunks = (void *)chunk;
    return (void *)(ret + CHUNK_HEADER_SIZE);
  } else {
    struct objalloc_chunk *chunk;
    chunk = (struct objalloc_chunk *)malloc(CHUNK_SIZE);
    if (chunk == NULL) return NULL;
    chunk->next = (struct objalloc_chunk *)o->chunks;
    chunk->current_ptr = NULL;
    o->current_ptr = (char *)chunk + CHUNK_HEADER_SIZE;
    o->current_space = CHUNK_SIZE - CHUNK_HEADER_SIZE;
    o->chunks = (void *)chunk;
    return objalloc_alloc(o, len);
  }
}
__attribute__((noinline)) struct objalloc *objalloc_create(void) {
  struct objalloc *ret = (struct objalloc *)malloc(sizeof(struct objalloc));
  if (ret == NULL) return NULL;
  ret->chunks = malloc(CHUNK_SIZE);
  if (ret->chunks == NULL) {
    free(ret);
    return NULL;
  }
  ((struct objalloc_chunk *)ret->chunks)->next = NULL;
  ((struct objalloc_chunk *)ret->chunks)->current_ptr = NULL;
  ret->current_ptr = (char *)ret->chunks + CHUNK_HEADER_SIZE;
  ret->current_space = CHUNK_SIZE - CHUNK_HEADER_SIZE;
  return ret;
}
__attribute__((noinline)) void *bfd_alloc(struct bfd *abfd, unsigned long size) {
  void *ret = objalloc_alloc((struct objalloc *)abfd->memory, size);
  return ret;
}
__attribute__((noinline)) void *bfd_zalloc(struct bfd *abfd, unsigned long size) {
  void *res = bfd_alloc(abfd, size);
  if (res) memset(res, 0, size);
  return res;
}
__attribute__((noinline)) void mk_own(struct bfd *b) { b->tdata.own = bfd_zalloc(b, sizeof(struct owner)); }
__attribute__((noinline)) void scribble(struct bfd *b) { *((struct objalloc *)b->memory)->current_ptr = 0; }
int main(int argc, char **argv) {
  struct bfd *b = calloc(1, sizeof(struct bfd));
  if (!b) return 1;
  b->memory = objalloc_create();
  if (!b->memory) return 1;
  mk_own(b);
  if (argc > 3) scribble(b);
  if (!b->tdata.own) return 1;
  set_lo(b);
  drop_needed(b);
  if (argc > 2)
    bfd_hash_table_init_n(&b->tdata.own->table, big_newfunc, sizeof(struct big_entry), 61);
  else
    bfd_hash_table_init_n(&b->tdata.own->table, my_newfunc, sizeof(struct my_entry), 61);
  bfd_hash_lookup(&b->tdata.own->table, argv[0], 1, 0);
  struct my_entry *e = snap(b, argv[1]);
  if (e) e->fa(); // CHECK: ga gb
  return 0;
}
