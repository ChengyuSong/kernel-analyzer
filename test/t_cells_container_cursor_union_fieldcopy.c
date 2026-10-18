// t_cells_container_cursor_union_fieldcopy.c — (C'', Fable 2026-10-17): a
// one-field copy of the cursor between two entries (`y->u.i.link =
// x->u.i.link`, the same union field) is a copy of the cursor, not a store
// into it: its facts keep their member keys, so under the cursor's keys it
// moves the cursor's own content (Q1 (b)'s treatment for one field), and
// the copied element stays an element through the chase. Before, the
// census could not type the stored value (a load from a union): the store
// was of no member (#?), every read of the slot admitted it, and the chase
// read admitted another member's store: REJECTED.
// LOG: cursor field struct.bfd_link_hash_entry\+40 on an element: CLOSED \(3 stores, each null or an element, or 1 stores of other members of union u, each with union keys; a read of the cursor is closed only if it admits none of them; 1 copies of the union field, key-preserving\)
// LOG: Container:   VERIFIED under 2 assumptions
#include <stdlib.h>
#include <string.h>
typedef void (*fn)(void);
struct bfd_hash_entry { struct bfd_hash_entry *next; const char *string; unsigned long hash; };
struct bfd_hash_table;
typedef struct bfd_hash_entry *(*newfunc_t)(struct bfd_hash_entry *, struct bfd_hash_table *, const char *);
struct bfd_hash_table { struct bfd_hash_entry **table; newfunc_t newfunc; void *memory; unsigned int size; unsigned int count; };
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
__attribute__((noinline)) int bfd_hash_table_init_n(struct bfd_hash_table *table, newfunc_t newfunc, unsigned int size) {
  table->table = calloc(size, sizeof(struct bfd_hash_entry *));
  if (table->table == NULL) return 0;
  table->size = size;
  table->count = 0;
  table->newfunc = newfunc;
  return 1;
}
struct bfd_link_hash_entry {
  struct bfd_hash_entry root;
  int type;
  union {
    struct { struct bfd_link_hash_entry *next; struct bfd_link_hash_entry *link; } i;
    struct { struct bfd_link_hash_entry *next; char *p; } c;
  } u;
  fn func;
};
struct bfd_link_hash_table { struct bfd_hash_table table; };
static struct bfd_hash_entry *link_newfunc(struct bfd_hash_entry *entry, struct bfd_hash_table *table, const char *string) {
  (void)string;
  if (entry == NULL) entry = (struct bfd_hash_entry *)bfd_hash_allocate(table, sizeof(struct bfd_link_hash_entry));
  if (entry != NULL) {
    ((struct bfd_link_hash_entry *)entry)->type = 0;
    ((struct bfd_link_hash_entry *)entry)->u.i.link = NULL;
    ((struct bfd_link_hash_entry *)entry)->func = NULL;
  }
  return entry;
}
// With follow, chase link from an indirect entry (type 1) to another element.
struct bfd_link_hash_entry *bfd_link_hash_lookup(struct bfd_link_hash_table *table, const char *string, int create,
                                                 int copy, int follow) {
  struct bfd_link_hash_entry *ret = (struct bfd_link_hash_entry *)bfd_hash_lookup(&table->table, string, create, copy);
  if (follow && ret != NULL)
    while (ret->type == 1) ret = ret->u.i.link;
  return ret;
}
__attribute__((noinline)) static void setp(struct bfd_link_hash_entry *e, char *s) { e->u.c.p = s; }
__attribute__((noinline)) static void cplink(struct bfd_link_hash_entry *x, struct bfd_link_hash_entry *y) {
  y->type = 1;
  y->u.i.link = x->u.i.link;
}
int main(int argc, char **argv) {
  struct bfd_link_hash_table t;
  (void)argc;
  bfd_hash_table_init_n(&t.table, link_newfunc, 61);
  struct bfd_link_hash_entry *a = bfd_link_hash_lookup(&t, "a", 1, 0, 0);
  struct bfd_link_hash_entry *b = bfd_link_hash_lookup(&t, "b", 1, 0, 0);
  struct bfd_link_hash_entry *c = bfd_link_hash_lookup(&t, "c", 1, 0, 0);
  a->type = 1;
  a->u.i.link = b; // the cursor: an element
  c->type = 2;
  setp(c, argv[0]); // another member over the same bytes: a string (typed c by its formal)
  struct bfd_link_hash_entry *d = bfd_link_hash_lookup(&t, "d", 1, 0, 0);
  cplink(a, d); // a copy of the cursor: d's link is a's, an element
  struct bfd_link_hash_entry *h = bfd_link_hash_lookup(&t, argv[0], 0, 0, 1);
  return h != NULL && h->func != NULL;
}
