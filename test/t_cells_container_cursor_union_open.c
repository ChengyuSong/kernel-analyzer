// t_cells_container_cursor_union_open.c — a cursor inside a union whose
// other member's store sets no tag (plan 3.55 Q-d, Fable 2026-10-16):
// setp writes u.c.p and never writes type, so the tag pair cannot key it;
// the union census types the store by member layout (c) and keys the
// chase's read by its own member (i), with no settling check (UNCHECKED,
// the user's 2026-10-07 rule). The cursor closes on those census keys, so
// the closure rests on that UNCHECKED read: listed and counted. (At
// c1ebc1c..d612bb1 the same closure was reported "VERIFIED under 1
// assumptions", missing it.)
// LOG: ASSUMPTION closed cursor struct.bfd_link_hash_entry\+40: a read admitted by its own member's census key without a settling check \(UNCHECKED\): bfd_link_hash_lookup
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
// The other member's store in a function that never sets the tag: an
// untagged writer, every tag.
__attribute__((noinline)) static void setp(struct bfd_link_hash_entry *e, char *s) { e->u.c.p = s; }
int main(int argc, char **argv) {
  struct bfd_link_hash_table t;
  (void)argc;
  bfd_hash_table_init_n(&t.table, link_newfunc, 61);
  struct bfd_link_hash_entry *a = bfd_link_hash_lookup(&t, "a", 1, 0, 0);
  struct bfd_link_hash_entry *b = bfd_link_hash_lookup(&t, "b", 1, 0, 0);
  struct bfd_link_hash_entry *c = bfd_link_hash_lookup(&t, "c", 1, 0, 0);
  a->type = 1;
  a->u.i.link = b; // the cursor: an element
  setp(c, argv[0]); // another member over the same bytes, with no tag
  struct bfd_link_hash_entry *h = bfd_link_hash_lookup(&t, argv[0], 0, 0, 1);
  return h != NULL && h->func != NULL;
}
