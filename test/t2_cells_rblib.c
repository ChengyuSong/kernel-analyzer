// t2_cells_rblib.c — the rbtree rows (lib/rbtree.c shapes, simplified:
// the case checks the containers' shapes, not the balancing).
#include "cells_rb.h"
static inline void rb_set_parent_color(struct rb_node *rb, struct rb_node *p, int color) {
  rb->__rb_parent_color = (unsigned long)p | color;
}
__attribute__((noinline)) void rb_insert_color(struct rb_node *node, struct rb_root *root) {
  struct rb_node *parent = rb_parent(node);
  if (!parent) {
    rb_set_parent_color(node, NULL, 1);
    root->rb_node = node;
    return;
  }
  struct rb_node *gparent = rb_parent(parent);
  if (gparent && gparent->rb_left == parent && parent->rb_right == node) {
    struct rb_node *tmp = node->rb_left;
    parent->rb_right = tmp;
    if (tmp) rb_set_parent_color(tmp, parent, 0);
    node->rb_left = parent;
    rb_set_parent_color(parent, node, 0);
    gparent->rb_left = node;
    rb_set_parent_color(node, gparent, 1);
  }
}
__attribute__((noinline)) void __rb_erase_color(struct rb_node *parent, struct rb_root *root,
                                                void (*augment_rotate)(struct rb_node *, struct rb_node *)) {
  struct rb_node *sibling = parent->rb_right;
  if (sibling && !(sibling->__rb_parent_color & 1)) {
    struct rb_node *tmp1 = sibling->rb_left;
    WRITE_ONCE(parent->rb_right, tmp1);
    WRITE_ONCE(sibling->rb_left, parent);
    rb_set_parent_color(tmp1, parent, 1);
    struct rb_node *gp = rb_parent(parent);
    sibling->__rb_parent_color = parent->__rb_parent_color;
    parent->__rb_parent_color = (unsigned long)sibling;
    __rb_change_child(parent, sibling, gp, root);
    augment_rotate(parent, sibling);
  }
}
static void dummy_rotate(struct rb_node *old, struct rb_node *new) {}
__attribute__((noinline)) void rb_erase(struct rb_node *node, struct rb_root *root) {
  struct rb_node *child = node->rb_right ? node->rb_right : node->rb_left;
  struct rb_node *parent = rb_parent(node);
  __rb_change_child(node, child, parent, root);
  if (child) rb_set_parent(child, parent);
  else if (parent) __rb_erase_color(parent, root, dummy_rotate);
}
__attribute__((noinline)) struct rb_node *rb_first(const struct rb_root *root) {
  struct rb_node *n = root->rb_node;
  if (!n) return NULL;
  while (n->rb_left) n = n->rb_left;
  return n;
}
__attribute__((noinline)) struct rb_node *rb_next(const struct rb_node *node) {
  struct rb_node *parent;
  if (node->__rb_parent_color == (unsigned long)node) return NULL; // RB_EMPTY_NODE
  if (node->rb_right) {
    node = node->rb_right;
    while (node->rb_left) node = node->rb_left;
    return (struct rb_node *)node;
  }
  while ((parent = rb_parent(node)) && node == parent->rb_right) node = parent;
  return parent;
}
__attribute__((noinline)) void rb_replace_node(struct rb_node *victim, struct rb_node *new, struct rb_root *root) {
  struct rb_node *parent = rb_parent(victim);
  *new = *victim; // the victim's link record, parent word and color included
  if (victim->rb_left) rb_set_parent(victim->rb_left, new);
  if (victim->rb_right) rb_set_parent(victim->rb_right, new);
  __rb_change_child(victim, new, parent, root);
}
