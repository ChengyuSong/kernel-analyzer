// t_cells_container_naming.c — naming as on the kernel IR (plan 3.55 R3
// D3): -g0 -fno-strict-aliasing leaves offset-0 accesses with no struct GEP,
// no TBAA and no debug info. llist_reverse_order's and owner code's reads of
// `next` through a node loaded from the list are named by no rule (a loaded
// value's pointee: rule (2), not built), so the container fails on naming
// with the sites listed; never a pass.
// CFLAGS: -O2 -g0 -fno-strict-aliasing
// LOG: Container: llist \(hand, report\)
// LOG: naming FAIL: [1-9][0-9]* accesses through owner or element values that no rule names
// LOG: O1 FAIL
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
struct work { fn f; struct llist_node node; };
struct pool { int n; struct llist_head head; } P;
void a(void) {}
int main(void) {
  static struct work w1 = {a};
  llist_add_batch(&w1.node, &w1.node, &P.head);
  struct llist_node *n = llist_del_first(&P.head);
  int k = 0;
  for (struct llist_node *p = n; p; p = p->next) k++; // llist_for_each
  return k + (llist_reverse_order(n) != NULL);
}
