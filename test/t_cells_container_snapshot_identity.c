// t_cells_container_snapshot_identity.c — (3'') premise relevance by
// object identity by name (Fable 2026-10-19, (a)): the holder's table is
// o->table (o from main's first malloc). big_newfunc inits two other
// tables: q->table, another allocation (refuted by site), and o->stab, the
// same allocation at another offset (refuted by offset, nm's stab_info
// shape). Only o->table's init is relevant: premise PROVEN, struct
// my_entry (at the commit before, every init was relevant: OPEN-UNPROVEN,
// a second element struct).
// LOG: snapshot holder of .*premise PROVEN, element struct struct.my_entry
// LOG: holder's entsize field at malloc at main t_cells_container_snapshot_identity.c:117 \+32; 2 paths refuted by object identity
// LOG: \[REFUTED table .*newfunc big_newfunc, entsize field at malloc at main t_cells_container_snapshot_identity.c:118 \+32\]
// LOG: \[REFUTED table .*newfunc big_newfunc, entsize field at malloc at main t_cells_container_snapshot_identity.c:117 \+80\]
// LOG: O1 PASS
// LOG: 2 restores out of a snapshot holder: moves within one owner
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
struct owner { struct bfd_hash_table table; int flags; struct bfd_hash_table stab; };
__attribute__((noinline)) struct my_entry *snap(struct owner *o, const char *name) {
  struct bfd_hash_table *t = &o->table;
  size_t tabsize = 0;
  size_t entsize = 0;
  unsigned int i;
  void *old_tab, *old_ent;
  struct bfd_hash_entry *p;
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
int main(int argc, char **argv) {
  struct owner *o = malloc(sizeof *o);
  struct owner *q = malloc(sizeof *q);
  (void)argc;
  bfd_hash_table_init_n(&o->table, my_newfunc, sizeof(struct my_entry), 61);
  bfd_hash_table_init_n(&o->stab, big_newfunc, sizeof(struct big_entry), 61);
  bfd_hash_table_init_n(&q->table, big_newfunc, sizeof(struct big_entry), 61);
  bfd_hash_lookup(&o->table, argv[0], 1, 0);
  struct my_entry *e = snap(o, argv[1]);
  // Wide, as t_cells_container_snapshot_holder.c (the holder proven, rows
  // applied: the unlabeled element tail at +24; trace open). At the commit
  // before (premise open, O1 FAIL): ga.
  if (e) e->fa(); // CHECK: ga gb
  return 0;
}
