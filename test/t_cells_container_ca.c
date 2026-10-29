// t_cells_container_ca.c — a verified container's insert row applied per
// call site (CA, Fable 2026-10-28): ca_llist_add's body stores the element
// into head->first (the x86 cmpxchg asm) and the old first into the
// element's link through its formals, so every caller's element reached
// every caller's head; under CA those body stores are not made and each
// call site writes its own element into its own head (and the head's
// elements into its element's link). Two callers insert a struct A and a
// struct B into two heads; owner code walks HB inline. The container is
// declared in the case's own summary file; its IR-cmpxchg insert row
// (ca_llist_add2) is t_cells_container_ca_atomic.ll's.
// CFLAGS: -O2
// KAFLAGS: --func-summaries=t_cells_container_ca.fs
// LOG: Container: ca_llist \(hand\)
// LOG: VERIFIED \(rows applied\)
// LOG: container ca_llist: rows applied per site \(CA\): 2 insert sites
#include <stddef.h>
#include <stdbool.h>
typedef void (*fn)(void);
struct ca_node { struct ca_node *next; };
struct ca_head { struct ca_node *first; };
#define READ_ONCE(x) (*(volatile __typeof__(x) *)&(x))
#define container_of(p, T, m) ((T *)((char *)(p)-offsetof(T, m)))
static inline struct ca_node *cmpxchg_node(struct ca_node **ptr, struct ca_node *old, struct ca_node *new) {
  struct ca_node *ret;
  asm volatile("lock; cmpxchgq %2,%1" : "=a"(ret), "+m"(*ptr) : "r"(new), "0"(old) : "memory");
  return ret;
}
__attribute__((noinline)) bool ca_llist_add(struct ca_node *new, struct ca_head *head) {
  struct ca_node *first;
  do {
    new->next = first = READ_ONCE(head->first);
  } while (cmpxchg_node(&head->first, first, new) != first);
  return !first;
}
__attribute__((noinline)) struct ca_node *ca_llist_del_first(struct ca_head *head) {
  struct ca_node *entry, *old_entry, *next;
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
struct A { struct ca_node n; fn f; };
struct B { struct ca_node n; fn g; };
struct ca_head HA, HB;
void fa(void) {}
void fb(void) {}
__attribute__((noinline)) void put_a(struct A *a) { a->f = fa; ca_llist_add(&a->n, &HA); }
__attribute__((noinline)) void put_b(struct B *b) { b->g = fb; ca_llist_add(&b->n, &HB); }
int main(void) {
  static struct A a;
  static struct B b;
  put_a(&a);
  put_b(&b);
  for (struct ca_node *p = HB.first; p; p = p->next) container_of(p, struct B, n)->g(); // CHECK: fb
  return ca_llist_del_first(&HA) != NULL;
}
