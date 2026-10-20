// t_cells_container_snapshot_vectorformalnodi.c — R3 (a') (Fable
// 2026-10-20): OPSU initializes a union by its second member, so its IR
// type is literal, and at -g0 it has no debug type: cp's slot has no name,
// so no load is known to read it and cp's formals stay OPEN with the
// unnamed slot as the reason. At 07c261d: the same root without a reason.
// CFLAGS: -O0 -g0
// LOG: O1 open root \(1 copies\): a formal of address-taken cp: initializer slot unnamed at @OPSU \+8
// NOLOG: R3 read side
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
__attribute__((noinline)) void cp(void *d, const void *s) { memcpy(d, s, sizeof(struct my_entry)); }
static char dummy;
struct opsu { union { long l; void *p; } u; void (*copy)(void *, const void *); };
static const struct opsu OPSU = { .u = { .p = &dummy }, .copy = cp };
const struct opsu *volatile opsp = &OPSU;
int main(int argc, char **argv) {
  struct tables *t = malloc(sizeof *t);
  struct my_entry tmp;
  (void)argc;
  bfd_hash_table_init_n(&t->syms, my_newfunc, 61);
  struct my_entry *h = (struct my_entry *)bfd_hash_lookup(&t->syms, argv[0], 1, 0);
  opsp->copy(&tmp, h);
  return tmp.func != NULL;
}
