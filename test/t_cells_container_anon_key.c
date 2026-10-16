// t_cells_container_anon_key.c — a field of an anonymous struct is named by
// its enclosing named struct and byte offset (Fable 2026-10-16). clang
// numbers anonymous structs (`struct.anon`, `struct.anon.0`), and the
// linker's suffix strip made every one `struct.anon`: bfd_hash_entry's chain
// link (inside an anonymous struct) and cfg's unrelated pointer (inside
// another, written with a string) were one key, struct.anon+0. Debug info's
// pointer members did not look inside the anonymous member, so the link was
// not found at all and the lookup's chain walk failed O2 (REJECTED at the
// commit before). Now the link is bfd_hash_entry+0 (found through the
// anonymous member), cfg's store is cfg+0, and the block verifies.
// LOG: Container: bfd_hash \(hand\).* 1 link fields
// LOG: Container:   O1 PASS
// LOG: Container:   O2 PASS
// LOG: Container:   VERIFIED
// LOG: Container: anonymous struct fields: [1-9][0-9]* named by the enclosing named struct and byte offset, 0 unnamed
#include <stdlib.h>
#include <string.h>
typedef void (*fn)(void);
struct bfd_hash_entry { struct { struct bfd_hash_entry *next; } l; const char *string; unsigned long hash; };
struct bfd_hash_table;
typedef struct bfd_hash_entry *(*newfunc_t)(struct bfd_hash_entry *, struct bfd_hash_table *, const char *);
struct bfd_hash_table { struct bfd_hash_entry **table; newfunc_t newfunc; void *memory; unsigned int size; unsigned int count; };
struct my_entry { struct bfd_hash_entry root; fn func; };
// Another anonymous struct with a pointer at +0, written with a string.
struct cfg { struct { const char *name; } x; int n; };
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
  hashp->l.next = table->table[_index];
  table->table[_index] = hashp;
  table->count++;
  return hashp;
}
struct bfd_hash_entry *bfd_hash_lookup(struct bfd_hash_table *table, const char *string, int create, int copy) {
  unsigned long hash = bfd_hash_hash(string);
  unsigned int _index = hash % table->size;
  struct bfd_hash_entry *hashp;
  (void)copy;
  for (hashp = table->table[_index]; hashp != NULL; hashp = hashp->l.next)
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
  return 1;
}
int main(int argc, char **argv) {
  struct bfd_hash_table t;
  struct cfg *c = malloc(sizeof *c);
  c->x.name = argv[0];
  bfd_hash_table_init_n(&t, my_newfunc, 61);
  struct my_entry *h = (struct my_entry *)bfd_hash_lookup(&t, c->x.name, 1, 0);
  return h->func != NULL;
}
