// t_cells_container_inlined_remove.c — an inlined remove (Fable 2026-10-15):
// rb_erase_cached / rb_erase_augmented inlined into owner code. The removed
// node reaches no row; its parent (decoded from the node's own parent word)
// reaches __rb_erase_color's ELEM. Under the link invariant (the remove
// row's ELEM premise) the node is an element, listed per site, and
// __rb_change_child's stores are owner-code relinks. The leftmost update's
// rb_next(node) joins the function's only owner group: an ASSUMPTION too
// (remove_inline); remove_plain has no row on the node at all.
// CFLAGS: -O2 -g0 -fno-strict-aliasing
// MODULE: t2_cells_rblib.c
// LOG: ASSUMPTION inlined remove: node assumed an element by its parent word: remove_plain:
// LOG: ASSUMPTION traverse element joined the function's only owner group: remove_inline:
// LOG: owner-code relinks [1-9]
// NOLOG: outside the rows
// NOLOG: implicit insert UNMATCHED
#include "cells_rb.h"
typedef void (*fn)(void);
struct item { long key; fn f; struct rb_node node; };
struct rb_root_cached TC;
static void rot(struct rb_node *o, struct rb_node *n) {}
__attribute__((noinline)) void remove_inline(struct item *it) {
  struct rb_node *node = &it->node;
  if (TC.rb_leftmost == node) TC.rb_leftmost = rb_next(node);
  struct rb_node *child = node->rb_right, *tmp = node->rb_left;
  struct rb_node *parent = rb_parent(node), *rebalance = NULL;
  if (!tmp) {
    __rb_change_child(node, child, parent, &TC.rb_root);
    if (child) child->__rb_parent_color = node->__rb_parent_color;
    else rebalance = parent;
  } else if (!child) {
    __rb_change_child(node, tmp, parent, &TC.rb_root);
    tmp->__rb_parent_color = node->__rb_parent_color;
  }
  if (rebalance) __rb_erase_color(rebalance, &TC.rb_root, rot);
}
// The plain inlined remove: no row on the node, only its parent's rebalance.
__attribute__((noinline)) void remove_plain(struct item *it, struct rb_root *root) {
  struct rb_node *node = &it->node;
  struct rb_node *child = node->rb_right;
  struct rb_node *parent = rb_parent(node);
  if (!node->rb_left) {
    __rb_change_child(node, child, parent, root);
    if (child) child->__rb_parent_color = node->__rb_parent_color;
    else if (parent) __rb_erase_color(parent, root, rot);
  }
}
struct rb_root R2;
void a(void) {}
int main(void) {
  static struct item i1 = {1, a};
  i1.node.__rb_parent_color = 1;
  TC.rb_root.rb_node = &i1.node;
  rb_insert_color(&i1.node, &TC.rb_root);
  TC.rb_leftmost = rb_first(&TC.rb_root);
  container_of(TC.rb_leftmost, struct item, node)->f();
  remove_inline(&i1);
  static struct item i2 = {2, a};
  i2.node.__rb_parent_color = 1;
  R2.rb_node = &i2.node;
  rb_insert_color(&i2.node, &R2);
  remove_plain(&i2, &R2);
  return 0;
}
