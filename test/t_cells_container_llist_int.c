// t_cells_container_llist_int.c — a link word reused as an integer (plan
// 3.55 R4; the kfree_rcu bulk page: nr_records over llist_node.next, by a
// cast as in 5.18, not a union: a union is class 2, t_cells_container_union).
// A cached page leaves the llist through llist_del_first and owner code uses
// its first word as a count: zeroing it is a null store, bumping it is
// arithmetic over a load of the same cell (R4, admitted and counted). A
// store of another integer into the same word fails O1 with its site.
// CFLAGS: -O2
// LOG: Container: llist \(hand, report\)
// LOG: storage writes admitted: .*link word reused as integer: self-derived \(R4\) 1
// LOG: storage FAIL a store into struct.llist_node\+0 outside the rows: 1 sites
// LOG:     set_count: store i64
// LOG: REPORT ONLY: the obligations fail \(rows not applied\)
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
  struct llist_node llist;
  void *records[4];
};
#define NR(b) (*(unsigned long *)&(b)->llist.next)
struct cache { int n; struct llist_head bkv; } K;
__attribute__((noinline)) void bump(struct bulk *b) { NR(b)++; }
__attribute__((noinline)) void set_count(struct bulk *b, unsigned long n) { NR(b) = n; }
unsigned long external_count(void);
static struct bulk B1;
int main(void) {
  llist_add_batch(&B1.llist, &B1.llist, &K.bkv);
  struct bulk *b = (struct bulk *)llist_del_first(&K.bkv);
  if (!b) return 0;
  NR(b) = 0;
  bump(b);
  set_count(b, external_count());
  return (int)NR(b);
}
