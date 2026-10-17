// t_cells_container_holder_local.c — rule A (3') (Fable 2026-10-17): the
// pointee array of a local pointer whose every store is a fresh block (or
// null) is a holder (binutils' sorted_sym_hash = bfd_malloc (..)): its
// stores, derived by name from the local, are lookups' elements, so a read
// of it is one and the cursor closes.
// The chase in bfd_link_hash_lookup (follow) reads the cursor `link`; its
// one store outside the constructor is `a->link = x`, x a read of a holder.
// LOG: cursor field struct.bfd_link_hash_entry\+32 on an element: CLOSED
// LOG: ASSUMPTION closed holder the array local main: .* points to: the element stored there is of the same table instance
// LOG: Container:   VERIFIED under
#include <stdlib.h>
#include <string.h>
typedef void (*fn)(void);
struct bfd_hash_entry { struct bfd_hash_entry *next; const char *string; unsigned long hash; };
struct bfd_hash_table;
typedef struct bfd_hash_entry *(*newfunc_t)(struct bfd_hash_entry *, struct bfd_hash_table *, const char *);
struct bfd_hash_table { struct bfd_hash_entry **table; newfunc_t newfunc; void *memory; unsigned int size; unsigned int count; };
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
__attribute__((noinline)) int bfd_hash_table_init_n(struct bfd_hash_table *table, newfunc_t newfunc, unsigned int size) {
  table->table = calloc(size, sizeof(struct bfd_hash_entry *));
  if (table->table == NULL) return 0;
  table->size = size;
  table->count = 0;
  table->newfunc = newfunc;
  return 1;
}
struct bfd_link_hash_entry { struct bfd_hash_entry root; int type; struct bfd_link_hash_entry *link; fn func; };
struct bfd_link_hash_table { struct bfd_hash_table table; };
static struct bfd_hash_entry *link_newfunc(struct bfd_hash_entry *entry, struct bfd_hash_table *table, const char *string) {
  (void)string;
  if (entry == NULL) entry = (struct bfd_hash_entry *)bfd_hash_allocate(table, sizeof(struct bfd_link_hash_entry));
  if (entry != NULL) {
    ((struct bfd_link_hash_entry *)entry)->type = 0;
    ((struct bfd_link_hash_entry *)entry)->link = NULL;
    ((struct bfd_link_hash_entry *)entry)->func = NULL;
  }
  return entry;
}
// With follow, chase link from an indirect entry (type 1) to another element.
struct bfd_link_hash_entry *bfd_link_hash_lookup(struct bfd_link_hash_table *table, const char *string, int create,
                                                 int copy, int follow) {
  struct bfd_link_hash_entry *ret = (struct bfd_link_hash_entry *)bfd_hash_lookup(&table->table, string, create, copy);
  if (follow && ret != NULL)
    while (ret->type == 1) ret = ret->link;
  return ret;
}
int main(int argc, char **argv) {
  struct bfd_link_hash_table t;
  bfd_hash_table_init_n(&t.table, link_newfunc, 61);
  struct bfd_link_hash_entry *a = bfd_link_hash_lookup(&t, "a", 1, 0, 0);
  a->type = 1;
  struct bfd_link_hash_entry **v = NULL;
  v = malloc(4 * sizeof *v);
  if (!v) return 1;
  struct bfd_link_hash_entry **p = v;
  for (int i = 0; i < argc && i < 4; i++) *p++ = bfd_link_hash_lookup(&t, argv[i], 1, 0, 0);
  a->link = v[argc & 3];
  struct bfd_link_hash_entry *h = bfd_link_hash_lookup(&t, argv[0], 0, 0, 1);
  return h != NULL && h->func != NULL;
}
