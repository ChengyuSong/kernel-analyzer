// t_cells_container_snapshot_vectorformalw.c — R3's controls (Fable
// 2026-10-20), one per condition, each a copy through a formal of its own
// function and vector struct: OPSW is writable (and written at a runtime
// offset, as bfd_elf_set_pagesize writes the elf backend tables): (c);
// OPSA is constant but main stores cpa2 into another struct opsa's copy
// field: (a); OPSR is constant but the load of opsrp->copy is passed to
// keep(): (r). Each formal stays OPEN with its reason. At 07c261d: the
// same three roots without reasons.
// LOG: O1 open root \(1 copies\): a formal of address-taken cpw: writable global @OPSW
// LOG: O1 open root \(1 copies\): a formal of address-taken cpa: initializer slot @OPSA \+8: struct.opsa\+8: a write in a body over it: main
// LOG: O1 open root \(1 copies\): a formal of address-taken cpr: initializer slot @OPSR \+8: struct.opsr\+8: its load main .* has another use
// NOLOG: R3 read side
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
struct tables { struct bfd_hash_table syms; struct bfd_hash_table secs; };
__attribute__((noinline)) void cpw(void *d, const void *s) { memcpy(d, s, sizeof(struct my_entry)); }
__attribute__((noinline)) void cpa(void *d, const void *s) { memcpy(d, s, sizeof(struct my_entry)); }
__attribute__((noinline)) void cpa2(void *d, const void *s) { (void)d, (void)s; }
__attribute__((noinline)) void cpr(void *d, const void *s) { memcpy(d, s, sizeof(struct my_entry)); }
struct opsw { int kind; void (*copy)(void *, const void *); long pagesize; };
struct opsa { int kind; void (*copy)(void *, const void *); };
struct opsr { int kind; void (*copy)(void *, const void *); };
static struct opsw OPSW = { 1, cpw, 4096 };
static const struct opsa OPSA = { 1, cpa };
static const struct opsr OPSR = { 1, cpr };
struct opsw *volatile opswp = &OPSW;
const struct opsa *volatile opsap = &OPSA;
const struct opsr *volatile opsrp = &OPSR;
void (*volatile kept)(void *, const void *);
__attribute__((noinline)) void keep(void (*f)(void *, const void *)) { kept = f; }
int main(int argc, char **argv) {
  struct tables *t = malloc(sizeof *t);
  struct my_entry tw, ta, tr;
  struct opsa *other = malloc(sizeof *other);
  bfd_hash_table_init_n(&t->syms, my_newfunc, 61);
  struct my_entry *h = (struct my_entry *)bfd_hash_lookup(&t->syms, argv[0], 1, 0);
  *((long *)((char *)opswp + (argc > 2 ? 16 : 0))) = argc;
  other->copy = cpa2;
  keep(opsrp->copy);
  opswp->copy(&tw, h);
  opsap->copy(&ta, h);
  opsrp->copy(&tr, h);
  return tw.func != NULL || ta.func != NULL || tr.func != NULL || other->copy == NULL;
}
