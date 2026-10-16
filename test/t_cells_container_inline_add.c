// t_cells_container_inline_add.c — an inline insert with no row symbol
// (Fable 2026-10-15, (D)): rethook_hook's __llist_add (static inline, so no
// symbol to row) stores an element into a handle in a function that calls
// no row. An honest FAIL in its own class, counted and listed.
// CFLAGS: -O2
// LOG: storage FAIL an inline insert with no row symbol \(an element into struct.llist_head\+0 in a function that calls no row\): 1 sites
// LOG:     hook: store ptr
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
struct node { long v; struct llist_node llist; };
struct task { int pid; struct llist_head rethooks; } T;
static inline void __llist_add(struct llist_node *new, struct llist_head *head) {
  new->next = head->first;
  head->first = new;
}
__attribute__((noinline)) void hook(struct node *n) { __llist_add(&n->llist, &T.rethooks); }
static struct node N1;
int main(void) {
  hook(&N1);
  struct llist_node *f = llist_del_first(&T.rethooks);
  return f != NULL;
}
