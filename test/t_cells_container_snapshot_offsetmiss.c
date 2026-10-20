// t_cells_container_snapshot_offsetmiss.c — check (2) by offset (Fable
// 2026-10-20): as t_cells_container_snapshot_unnamedcover.c, but the write
// through a void pointer formal (its actual is the owner) is an 8-byte
// store at +48 (owner.spare, added), past the guard word at +40. Its
// origins are the word's object (calloc at
// main), so by origins it reaches the word; its object walk is closed and
// puts it at +48, disjoint from [40, 44): it does not reach, and check (2)
// passes. At 062b4ff: "not unreachable by name (an unnamed-destination
// write over struct.owner+40: its destination may be the word's object at
// main ... poke".
// LOG: check \(2\) by offset: poke .*: offsets \+48 miss the word; walk closed: does not reach
// LOG: check \(2\) by offset: 1 of 1 REACH writes closed
// LOG: check \(2\) on the word \(1 kept objects' sites\): [0-9]+ close / 0 reach / 0 open; first reason: none
// NOLOG: not unreachable by name
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
#define AS_NEEDED 1
struct owner { struct bfd_hash_table table; unsigned int lo : 6; unsigned int cls : 4; unsigned int hi : 3; long spare; };
__attribute__((noinline)) struct my_entry *snap(struct owner *o, const char *name) {
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
__attribute__((noinline)) void set_lo(struct owner *o) { o->lo = 5; }
__attribute__((noinline)) void drop_needed(struct owner *o) { o->cls = o->cls & ~AS_NEEDED; }
__attribute__((noinline)) void poke(void *raw, int n) { (void)n; *(long *)((char *)raw + 48) = 7; }
int main(int argc, char **argv) {
  struct owner *o = calloc(1, sizeof(struct owner));
  if (!o) return 1;
  if (argc > 5) poke(o, argc);
  set_lo(o);
  drop_needed(o);
  if (argc > 2)
    bfd_hash_table_init_n(&o->table, big_newfunc, sizeof(struct big_entry), 61);
  else
    bfd_hash_table_init_n(&o->table, my_newfunc, sizeof(struct my_entry), 61);
  bfd_hash_lookup(&o->table, argv[0], 1, 0);
  struct my_entry *e = snap(o, argv[1]);
  // With the restores not excluded (O1 FAIL, as
  // t_cells_container_snapshot_memcpy.c): ga.
  if (e) e->fa(); // CHECK: ga
  return 0;
}
