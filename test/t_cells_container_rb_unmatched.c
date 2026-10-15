// t_cells_container_rb_unmatched.c — an implicit insert with no insert row
// call (plan 3.55 R3 D6): owner code reads the tree through rb_first (a row
// on &T.root, so the function is owner code), descends to a leaf slot and
// links a node there, but never calls rb_insert_color on it. The link store
// is listed UNMATCHED and fails O1 with its site.
// CFLAGS: -O2
// LOG: Container: rbtree \(hand, report\)
// LOG: implicit inserts 0 matched, 1 unmatched
// LOG: implicit insert UNMATCHED: graft: store ptr
// LOG: O1 FAIL\(an implicit insert with no insert row call on the same element and owner: 1 \[graft: store ptr
// LOG: REPORT ONLY: the obligations fail \(rows not applied\)
#include <stddef.h>
struct rb_node {
  unsigned long __rb_parent_color;
  struct rb_node *rb_right;
  struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));
struct rb_root { struct rb_node *rb_node; };
#define rb_parent(r) ((struct rb_node *)((r)->__rb_parent_color & ~3UL))
__attribute__((noinline)) void rb_insert_color(struct rb_node *node, struct rb_root *root) {
  if (!rb_parent(node)) {
    node->rb_left = node->rb_right = NULL;
    node->__rb_parent_color = 1;
    root->rb_node = node;
  }
}
__attribute__((noinline)) struct rb_node *rb_first(const struct rb_root *root) {
  struct rb_node *n = root->rb_node;
  if (!n) return NULL;
  while (n->rb_left) n = n->rb_left;
  return n;
}
struct tree { int n; struct rb_root root; } T;
struct rb_node N1, N2;
__attribute__((noinline)) int graft(struct rb_node *node) {
  struct rb_node *first = rb_first(&T.root);
  struct rb_node **p = &T.root.rb_node;
  while (*p) p = &(*p)->rb_left;
  node->rb_left = node->rb_right = NULL;
  *p = node; // linked, never inserted
  return first != NULL;
}
int main(void) {
  rb_insert_color(&N1, &T.root);
  return graft(&N2);
}
