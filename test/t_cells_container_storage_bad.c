// t_cells_container_storage_bad.c — the declared storage is a proposal the
// engine checks from both sides (plan 3.55 R3 D2, Fable 2026-10-15). This
// program's rb_node has a fourth pointer, rb_hint, that rb_insert_color
// stores an element into: the rbtree block does not declare it, so O1 fails
// "an element stored outside the declared storage" with the site. And the
// program has rb_root_cached but never writes rb_leftmost, which the block
// declares: counted as unused declared storage, not a failure.
// CFLAGS: -O2
// LOG: Container: rbtree \(hand, report\)
// LOG: storage FAIL an element stored outside the declared storage: 1 sites
// LOG:     rb_insert_color: store ptr %0, ptr
// LOG: unused declared storage struct.rb_root_cached\+8$
// LOG: REPORT ONLY: the obligations fail \(rows not applied\)
// NOLOG: unused declared storage .*no such field
#include <stddef.h>
struct rb_node {
  unsigned long __rb_parent_color;
  struct rb_node *rb_right;
  struct rb_node *rb_left;
  struct rb_node *rb_hint;
} __attribute__((aligned(sizeof(long))));
struct rb_root { struct rb_node *rb_node; };
struct rb_root_cached { struct rb_root rb_root; struct rb_node *rb_leftmost; };
#define rb_parent(r) ((struct rb_node *)((r)->__rb_parent_color & ~3UL))
__attribute__((noinline)) void rb_insert_color(struct rb_node *node, struct rb_root *root) {
  struct rb_node *parent = rb_parent(node);
  if (!parent) {
    node->rb_left = node->rb_right = NULL;
    node->__rb_parent_color = 1;
    root->rb_node = node;
    return;
  }
  parent->rb_hint = node; // an element into an undeclared slot
}
__attribute__((noinline)) struct rb_node *rb_first(const struct rb_root *root) {
  struct rb_node *n = root->rb_node;
  if (!n) return NULL;
  while (n->rb_left) n = n->rb_left;
  return n;
}
struct rb_root_cached C;
struct rb_node N1;
int main(void) {
  rb_insert_color(&N1, &C.rb_root);
  return rb_first(&C.rb_root) != NULL && C.rb_leftmost == NULL;
}
