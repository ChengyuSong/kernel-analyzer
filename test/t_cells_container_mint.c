// t_cells_container_mint.c — the element mint (plan 3.55 deliverable 1,
// Fable 2026-10-13): binutils' hash table in its shape (bfd_hash_lookup
// with create, bfd_hash_insert calling the table's newfunc through a code
// field, the newfunc carving the entry from the table's pool), under the
// bfd_hash rows of func_summaries.txt. Two tables share one newfunc, so
// the body's entry object is one per carve site; the row mints an element
// per (table, lookup site) instead, so the function the owner code writes
// into an entry of table 1 is not what an entry of table 2 holds. The
// body's own writes (string, hash, next) reach the minted elements by
// inheritance.
// LOG: Container: bfd_hash .*code fields \([1-9][0-9]* targets
// LOG: VERIFIED \(rows applied\)
// LOG: element mint: [1-9][0-9]* mint links
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
