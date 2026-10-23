// t_cells_sitecoverwalk2.c — site names (B6, Fable 2026-10-22): the twin
// of t_cells_sitecoverwalk.c in which the chain opens. ref is a heap object
// (named struct.ref) and put_ptr writes a pointer at its +8 through a void *:
// that write reaches struct.ref+8's word on its own (self-standing, round
// 0). put_flags' write reads struct.ref+8 (Fd), so struct.h2+0's cover opens
// in round 1, its reason reading through struct.ref+8 to put_ptr's write.
// LOG: object identity walked 2 field keys, 2 open by writes named otherwise
// LOG: site names \(B6\): put_ptr t_cells_sitecoverwalk2.c:[0-9]+ over struct.ref\+8 on malloc at main t_cells_sitecoverwalk2.c:[0-9]+ \(named struct.ref\): reach: it writes the word at \+8
// LOG: site names \(B6\): put_flags t_cells_sitecoverwalk2.c:[0-9]+ over struct.h2\+0 on malloc at main t_cells_sitecoverwalk2.c:[0-9]+ \(named struct.owner\): close; open by the solve: its walk reads struct.ref\+8, whose cover is open
// LOG: unnamed-destination write over struct.h2\+0: origins include a named allocation \(malloc at main t_cells_sitecoverwalk2.c:[0-9]+ \(named struct.owner\)\), its walk reads struct.ref\+8, whose cover is open: an unnamed-destination write over struct.ref\+8: origins include a named allocation \(malloc at main t_cells_sitecoverwalk2.c:[0-9]+ \(named struct.ref\)\), it writes the word at \+8 put_ptr
// NOLOG: closed by the least solution \(cycle
// NOLOG: under way
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
  struct bfd_hash_entry *hashp = (*table->newfunc)(NULL, NULL, string); // the table is not passed: the owner site is passed to no indirect call
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
struct ref { int pad; struct owner *o; };
struct h2 { struct owner *p; } h2;
// An unnamed-destination write (through a void *) on the owner's site, at
// struct owner's flags (+40): its destination walk goes back through snap's
// formal o to ref.o, the field the holder's walk is in.
__attribute__((noinline)) static void put_flags(void *p) { *(int *)((char *)p + 40) = 1; }
// An unnamed-destination write of a pointer at +8 of a void *: on the ref
// site (named struct.ref) it writes struct.ref+8's word: reach, on its own.
__attribute__((noinline)) static void put_ptr(void *p, void *v) { *(void **)((char *)p + 8) = v; }
__attribute__((noinline)) struct my_entry *snap(struct owner *o, const char *name) {
  put_flags(o);
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
  (void)argc;
  struct ref *rp = malloc(sizeof *rp);
  rp->o = o;
  put_ptr(rp, o);
  h2.p = malloc(sizeof(struct owner));
  bfd_hash_table_init_n(&o->table, my_newfunc, sizeof(struct my_entry), 61);
  bfd_hash_table_init_n(&h2.p->table, my_newfunc, sizeof(struct my_entry), 61);
  bfd_hash_lookup(&o->table, argv[0], 1, 0);
  struct my_entry *e = snap(rp->o, argv[1]);
  if (e) e->fa(); // CHECK: ga gb
  return 0;
}
