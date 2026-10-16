// cells_rb.h — the 5.18 rbtree shapes the container cases share
// (include/linux/rbtree.h, rbtree_augmented.h): the node with its parent
// word (parent | color, a link word), the roots, and the inline helpers the
// kernel inlines into owner code (rb_link_node, __rb_change_child, the
// cached leftmost update, the augmented erase's relinks). The row functions
// are in t2_cells_rblib.c.
#include <stddef.h>
struct rb_node {
  unsigned long __rb_parent_color;
  struct rb_node *rb_right;
  struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));
struct rb_root { struct rb_node *rb_node; };
struct rb_root_cached { struct rb_root rb_root; struct rb_node *rb_leftmost; };
#define rb_parent(r) ((struct rb_node *)((r)->__rb_parent_color & ~3UL))
#define container_of(p, T, m) ((T *)((char *)(p)-offsetof(T, m)))
#define WRITE_ONCE(x, v) (*(volatile __typeof__(x) *)&(x) = (v))
void rb_insert_color(struct rb_node *, struct rb_root *);
void rb_erase(struct rb_node *, struct rb_root *);
struct rb_node *rb_next(const struct rb_node *);
struct rb_node *rb_first(const struct rb_root *);
void rb_replace_node(struct rb_node *victim, struct rb_node *new, struct rb_root *root);
void __rb_erase_color(struct rb_node *parent, struct rb_root *root,
                      void (*augment_rotate)(struct rb_node *old, struct rb_node *new));
static inline void rb_link_node(struct rb_node *node, struct rb_node *parent, struct rb_node **rb_link) {
  node->__rb_parent_color = (unsigned long)parent;
  node->rb_left = node->rb_right = NULL;
  *rb_link = node;
}
static inline void __rb_change_child(struct rb_node *old, struct rb_node *new, struct rb_node *parent,
                                     struct rb_root *root) {
  if (parent) {
    if (parent->rb_left == old) WRITE_ONCE(parent->rb_left, new);
    else WRITE_ONCE(parent->rb_right, new);
  } else {
    WRITE_ONCE(root->rb_node, new);
  }
}
static inline void rb_set_parent(struct rb_node *rb, struct rb_node *p) {
  rb->__rb_parent_color = (rb->__rb_parent_color & 1) | (unsigned long)p;
}
