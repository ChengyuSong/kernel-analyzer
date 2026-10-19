// t_cells_container_snapshot_initializer.c — (3'') premise relevance by
// object identity by name (Fable 2026-10-19, (a)): a global initializer is
// a write. The holder's table is ref.o->table; ref.o is initialized to
// &s1 (whose table big_newfunc inits) and stored q (whose table my_newfunc
// inits) on one path. Both inits are relevant: two element structs, the
// premise open. Without the initializer, s1's path would be refuted and
// the premise proven on q's alone (unsound: s1's entries are big_entry).
// LOG: snapshot holder of .*premise OPEN-UNPROVEN
// LOG: holder's entsize field at @s1 \+32; malloc at main t_cells_container_snapshot_initializer.c:[0-9]+ \+32; 0 paths refuted by object identity
// NOLOG: snapshot element image
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
struct owner { struct bfd_hash_table table; int flags; };
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
struct ref { int pad; struct owner *o; };
static struct owner s1;
struct ref ref = {0, &s1};
int main(int argc, char **argv) {
  struct owner *q = malloc(sizeof *q);
  bfd_hash_table_init_n(&s1.table, big_newfunc, sizeof(struct big_entry), 61);
  bfd_hash_table_init_n(&q->table, my_newfunc, sizeof(struct my_entry), 61);
  if (argc > 3) ref.o = q;
  bfd_hash_lookup(&ref.o->table, argv[0], 1, 0);
  struct my_entry *e = snap(ref.o, argv[1]);
  if (e) e->fa(); // CHECK: ga
  return 0;
}
