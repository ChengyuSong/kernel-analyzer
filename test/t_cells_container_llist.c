// t_cells_container_llist.c — the llist report block (plan 3.55 R3/R5) on
// the kernel's shapes: llist_add_batch and llist_del_first update the head
// with the x86 `lock; cmpxchgq` asm (an indirect output `=*m` and a tied old
// value), read by the checker through the graph build's asm model (D4):
// the asm stores new_first (an element) and the tied old value (a same-cell
// re-store) into head->first, and its result is a load of head->first.
// llist_add(n, head) is llist_add_batch(n, n, head) (two ELEM arguments),
// and owner code walks the list llist_del_first hands back.
// CFLAGS: -O2
// LOG: Container: llist \(hand, report\)
// LOG: storage \(hand, declared\): handle struct.llist_head\+0; link struct.llist_node\+0; link word none; unused declared storage none
// LOG: O1 PASS
// LOG: storage writes admitted: .*same-cell re-stores \(R4\) [1-9]
// LOG: O2 PASS
// LOG: O3 PASS
// LOG: O4 PASS
// LOG: REPORT ONLY: the obligations hold \(rows not applied\)
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
void b(void) {}
int main(void) {
  static struct work w1 = {a}, w2 = {b};
  llist_add_batch(&w1.node, &w1.node, &P.head);
  llist_add_batch(&w2.node, &w2.node, &P.head);
  struct llist_node *n = llist_del_first(&P.head);
  if (n) container_of(n, struct work, node)->f(); // CHECK: a b
  return llist_reverse_order(n) != NULL;
}
