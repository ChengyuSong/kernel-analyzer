// t_cells_container_report.c — a report block applies no row (plan 3.55 R3
// D1): two llists, each with its own work item; llist_del_first on P1 would
// return only P1's item if the rows were applied, and returns both through
// the body's shared return here. The container is checked (its obligations
// hold) and its rows are never applied: no row links, both targets.
// CFLAGS: -O2
// LOG: Container: llist \(hand, report\)
// LOG: REPORT ONLY: the obligations hold \(rows not applied\)
// NOLOG: container rows: [1-9][0-9]* row links
// NOLOG: VERIFIED \(rows applied\)
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
struct work { fn f; struct llist_node node; };
struct pool { int n; struct llist_head head; } P1, P2;
void a(void) {}
void b(void) {}
int main(void) {
  static struct work w1 = {a}, w2 = {b};
  llist_add_batch(&w1.node, &w1.node, &P1.head);
  llist_add_batch(&w2.node, &w2.node, &P2.head);
  struct llist_node *n = llist_del_first(&P1.head);
  if (n) container_of(n, struct work, node)->f(); // CHECK: a b
  return llist_del_first(&P2.head) != NULL;
}
