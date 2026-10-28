// t_cells_dr_ctor_crossmod.c — a container's constructor defined in another
// module (DR, Fable 2026-10-27): main passes my_newfunc, which only
// t2_cells_dr_ctor_crossmod.c defines, to bfd_hash_table_init_n. The
// constant this module stores was its declaration, which has no body: no
// constructor element was found, and bfd_hash's mint failed ("element size
// unknown: no constructor element"), rejecting the container. The constant
// now names the definition (canonicalFunc): the container is verified and
// the row object takes struct.my_entry.
// MODULE: t2_cells_dr_ctor_crossmod.c
// LOG: row object .* at .*: struct.my_entry, constructors \{my_newfunc\}
// LOG: Container:   VERIFIED \(rows applied\)
// NOLOG: mint FAIL\(element size unknown: no constructor element\)
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
void ga(void);
void gb(void);
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
struct bfd_hash_entry *my_newfunc(struct bfd_hash_entry *, struct bfd_hash_table *, const char *);
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
struct owner { struct bfd_hash_table table; int flags; };
struct box { struct owner *o; };
struct box gbox;
__attribute__((noinline)) void put(struct box *d, struct box *s) { *d = *s; }
int main(int argc, char **argv) {
  struct owner *o = malloc(sizeof *o);
  struct box a = {o}, b, c;
  bfd_hash_table_init_n(&o->table, my_newfunc, sizeof(struct my_entry), 61);
  put(&b, &a);
  put(&c, &b);
  put(&gbox, &c);
  struct my_entry *e = (struct my_entry *)bfd_hash_lookup(&o->table, argv[argc - 1], 1, 0);
  if (e) e->fa(); // CHECK: ga
  return 0;
}
