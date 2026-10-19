// t_cells_container_snapshot_unionkey.c — (ii) the union-keyed field walk
// (Fable 2026-10-19): the guard word's object is read through a union
// member (b->tdata.own); another member's store (mk_oth, a malloc'd struct
// other, large enough to hold the word's offset) is excluded by the census
// keys, so the word's only object is mk_own's calloc and the holder is
// unreachable by name. At the commit before, the walk read every store of
// the union: "an object not zero-allocated: malloc at mk_oth".
// LOG: ASSUMPTION unreachable by name: restore snap t_cells_container_snapshot_unionkey.c:[0-9]+: .*objects zero-allocated at calloc at mk_own
// LOG: union fields read by key \([1-9][0-9]* stores another member's, excluded\)
// LOG: O1 PASS
// NOLOG: not zero-allocated
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
struct other { char bytes[64]; };
struct bfd { const char *filename; union { struct owner *own; struct other *oth; } tdata; };
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
  if ((b->tdata.own->cls & AS_NEEDED) == 0) return (struct my_entry *)bfd_hash_lookup(t, name, 1, 0);
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
__attribute__((noinline)) void mk_own(struct bfd *b) {
  struct owner *x = calloc(1, sizeof(struct owner));
  b->tdata.own = x;
}
__attribute__((noinline)) void mk_oth(struct bfd *b) {
  struct other *x = malloc(sizeof(struct other));
  b->tdata.oth = x;
}
int main(int argc, char **argv) {
  struct bfd *b = calloc(1, sizeof(struct bfd));
  if (!b) return 1;
  if (argc > 3) mk_oth(b);
  else mk_own(b);
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
