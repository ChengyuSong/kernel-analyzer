// t_cells_container_deref_owner.c — an owner read through a pointer
// (plan 3.55 Q-b, Fable 2026-10-16): bfd_wrapped_link_hash_lookup's row is
// OWNER(*arg1@40), the table at bfd_link_info.hash. Checked by debug info
// (the formal's pointee has a member at +40 that points to an owner type)
// and applied through its body: no row link of its own; its callers'
// elements are the inner lookup's.
// LOG: row bfd_wrapped_link_hash_lookup OWNER\(\*arg1@40\) = bfd_link_info.hash \(bfd_link_hash_table \*\): checked by debug info; applied through its body
// LOG: Container:   VERIFIED under 1 assumptions
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
// The link info a linker passes everywhere: its hash table at +40.
struct bfd_link_info { char other[40]; struct bfd_link_hash_table *hash; };
__attribute__((noinline)) struct bfd_link_hash_entry *bfd_wrapped_link_hash_lookup(void *abfd, struct bfd_link_info *info,
                                                                                const char *string, int create,
                                                                                int copy, int follow) {
  (void)abfd;
  return bfd_link_hash_lookup(info->hash, string, create, copy, follow);
}
int main(int argc, char **argv) {
  struct bfd_link_hash_table t;
  struct bfd_link_info info;
  (void)argc;
  info.hash = &t;
  bfd_hash_table_init_n(&t.table, link_newfunc, 61);
  struct bfd_link_hash_entry *a = bfd_wrapped_link_hash_lookup(NULL, &info, "a", 1, 0, 0);
  struct bfd_link_hash_entry *b = bfd_link_hash_lookup(info.hash, "b", 1, 0, 0);
  a->type = 1;
  a->link = b; // the cursor: an element of the same table
  struct bfd_link_hash_entry *h = bfd_wrapped_link_hash_lookup(NULL, &info, argv[0], 0, 0, 1);
  return h != NULL && h->func != NULL;
}
