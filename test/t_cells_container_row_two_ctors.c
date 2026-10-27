// t_cells_container_row_two_ctors.c — row objects by constructor type
// (Fable 2026-10-19): one owner initialized with two constructors on two
// paths, each writing fa of its own element struct (my_newfunc ga,
// big_newfunc gc). e->fa() answers both, one row object per type, and no
// row object takes the other constructor's layout.
// LOG: row object .* at .*: struct.my_entry, constructors \{my_newfunc\}
// LOG: row object .* at .*: struct.big_entry, constructors \{big_newfunc\}
// NOLOG: row object .* at .*: struct.my_entry, constructors \{[^}]*big_newfunc
// NOLOG: row object .* at .*: struct.big_entry, constructors \{[^}]*my_newfunc
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
void gc(void) {}
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
  if (entry != NULL) ((struct big_entry *)entry)->fa = gc;
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
struct owner { struct bfd_hash_table table; int flags; };
struct box { struct owner *o; };
struct box gbox;
__attribute__((noinline)) void put(struct box *d, struct box *s) { *d = *s; }
int main(int argc, char **argv) {
  struct owner *o = malloc(sizeof *o);
  struct box a = {o}, b, c;
  if (argc > 3) bfd_hash_table_init_n(&o->table, my_newfunc, sizeof(struct my_entry), 61);
  struct big_entry *e = (struct big_entry *)bfd_hash_lookup(&o->table, argv[0], 1, 0);
  put(&b, &a);
  put(&c, &b);
  put(&gbox, &c);
  if (argc > 2) bfd_hash_table_init_n(&o->table, big_newfunc, sizeof(struct big_entry), 61);
  e = (struct big_entry *)bfd_hash_lookup(&o->table, argv[1], 1, 0);
  if (e) e->fa(); // CHECK: ga gc
  return 0;
}
