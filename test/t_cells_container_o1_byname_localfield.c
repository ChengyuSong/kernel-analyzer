// t_cells_container_o1_byname_localfield.c — a by-name load of a field that
// an address-taken local holds at offset 0 (Fable 2026-10-20, (0)): main
// stores an element into r.dst, whose -O0 GEP (0, 0) strips to the local's
// alloca, and fill reads it by name through rp->dst. The local's field 0 is
// now named, so the copy *pick(rp->dst) = *h is into an element. At the
// commit before: into no element (the load found no value by name and closed
// empty); with empty loads open but field 0 unnamed it would be open-
// unproven ("no value stored by name").
// LOG: O1 by name: 1 block copies .*: 1 into an element \(checked\), 0 into no element \(origins by name\), 0 open-unproven
// NOLOG: no value stored by name
#include <stdlib.h>
#include <string.h>
typedef void (*fn)(void);
struct bfd_hash_entry { struct bfd_hash_entry *next; const char *string; unsigned long hash; };
struct bfd_hash_table;
typedef struct bfd_hash_entry *(*newfunc_t)(struct bfd_hash_entry *, struct bfd_hash_table *, const char *);
struct bfd_hash_table { struct bfd_hash_entry **table; newfunc_t newfunc; void *memory; unsigned int size; unsigned int count; };
struct my_entry { struct bfd_hash_entry root; fn func; };
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
struct tables { struct bfd_hash_table syms; struct bfd_hash_table secs; };
__attribute__((noinline)) struct my_entry *pick(struct my_entry *p) { return p; }
struct reg { struct my_entry *dst; struct my_entry *other; };
__attribute__((noinline)) void fill(struct reg *rp, struct my_entry *h) { *pick(rp->dst) = *h; }
int main(int argc, char **argv) {
  struct tables *t = malloc(sizeof *t);
  struct reg r;
  (void)argc;
  bfd_hash_table_init_n(&t->syms, my_newfunc, 61);
  struct my_entry *h = (struct my_entry *)bfd_hash_lookup(&t->syms, argv[0], 1, 0);
  r.dst = (struct my_entry *)bfd_hash_lookup(&t->syms, argv[1], 1, 0);
  r.other = NULL;
  fill(&r, h);
  return 0;
}
