// t_cells_container_del_all.c — an inlined llist_del_all (Fable 2026-10-16
// Q2): `xchg(&head->first, NULL)` as inline asm, whose result the asm model
// (D4) reads as the slot's old value: an operand both read and written is a
// load into the result. The detached chain's nodes are then elements of the
// head, rebuilding it (`pos->next = first`) is owner-code relinks, and
// llist_add_batch re-adds it on the same head (i915_active's barrier
// tasks: i915_active_add_request and three more).
// CFLAGS: -O2 -g0
// LOG: Container: llist \(hand, report\)
// LOG: owner-code relinks [1-9]
// NOLOG: llist_node\+0 outside the rows
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
static inline struct llist_node *xchg_node(struct llist_node **ptr, struct llist_node *new) {
  struct llist_node *ret;
  asm volatile("xchgq %0,%1" : "=r"(ret), "+m"(*ptr) : "0"(new) : "memory");
  return ret;
}
static inline struct llist_node *llist_del_all(struct llist_head *head) { return xchg_node(&head->first, NULL); }
struct item { long k; struct llist_node node; };
struct engine { int x; struct llist_head barrier_tasks; } E;
__attribute__((noinline)) void reap(struct engine *e) {
  struct llist_node *pos, *next, *first = NULL, *last = NULL;
  for (pos = llist_del_all(&e->barrier_tasks); pos; pos = next) {
    next = pos->next;
    if (container_of(pos, struct item, node)->k) continue;
    pos->next = first;
    first = pos;
    if (!last) last = pos;
  }
  if (first) llist_add_batch(first, last, &e->barrier_tasks);
}
static struct item I1;
int main(void) {
  llist_add_batch(&I1.node, &I1.node, &E.barrier_tasks);
  reap(&E);
  return llist_del_first(&E.barrier_tasks) != NULL;
}
