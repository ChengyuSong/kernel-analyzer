// t_cells_container_union_nodi.c — class 2 without debug info (the
// kernel's IR): the union's members are not in the IR, so the premise is
// an ASSUMPTION "inside the union" at the site (the struct fits the
// union); the writes are storage inside a union, counted.
// CFLAGS: -O2 -g0
// LOG: storage inside a union \(a declared slot in the IR's member, which is clang's representative; counted, not a write of the slot\): [1-9] writes
// LOG: ASSUMPTION premise, inside a union: main: .*\(arg0, struct.llist_node\): inside the union at struct.bulk\+0, \+0 \(members not in the IR\)
// LOG: 0 disagree \(FAIL\), 2 inside a union
// NOLOG: storage FAIL
#include <stddef.h>
#include <stdbool.h>
typedef void (*fn)(void);
struct llist_node { struct llist_node *next; };
struct llist_head { struct llist_node *first; };
#define READ_ONCE(x) (*(volatile __typeof__(x) *)&(x))
#define container_of(p, T, m) ((T *)((char *)(p)-offsetof(T, m)))
static inline struct llist_node *cmpxchg_node(struct llist_node **ptr, struct llist_node *old, struct llist_node *new) {
  struct llist_node *ret;
  asm volatile("lock; cmpxchgq %2,%1" : "=a"(ret), "+m"(*ptr) : "r"(new), "0"(old) : "memory");
  return ret;
}
__attribute__((noinline)) bool llist_add_batch(struct llist_node *new_first, struct llist_node *new_last,
                                               struct llist_head *head) {
  struct llist_node *first;
  do {
    new_last->next = first = READ_ONCE(head->first);
  } while (cmpxchg_node(&head->first, first, new_first) != first);
  return !first;
}
__attribute__((noinline)) struct llist_node *llist_del_first(struct llist_head *head) {
  struct llist_node *entry, *old_entry, *next;
  entry = READ_ONCE(head->first);
  for (;;) {
    if (entry == NULL) return NULL;
    old_entry = entry;
    next = READ_ONCE(entry->next);
    entry = cmpxchg_node(&head->first, old_entry, next);
    if (entry == old_entry) break;
  }
  return entry;
}
__attribute__((noinline)) struct llist_node *llist_reverse_order(struct llist_node *head) {
  struct llist_node *new_head = NULL;
  while (head) {
    struct llist_node *tmp = head;
    head = head->next;
    tmp->next = new_head;
    new_head = tmp;
  }
  return new_head;
}
struct bulk {
  union {
    struct llist_node llist;
    unsigned long nr_records;
  };
  void *records[4];
};
struct cache { int n; struct llist_head bkv; } K;
__attribute__((noinline)) void bump(struct bulk *b) { b->nr_records++; }
__attribute__((noinline)) void set_count(struct bulk *b, unsigned long n) { b->nr_records = n; }
unsigned long external_count(void);
static struct bulk B1;
int main(void) {
  llist_add_batch(&B1.llist, &B1.llist, &K.bkv);
  struct bulk *b = (struct bulk *)llist_del_first(&K.bkv);
  if (!b) return 0;
  b->nr_records = 0;
  bump(b);
  set_count(b, external_count());
  return (int)b->nr_records;
}
