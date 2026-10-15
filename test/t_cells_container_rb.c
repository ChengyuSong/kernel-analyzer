// t_cells_container_rb.c — the rbtree report block (plan 3.55 R3/R5) on the
// kernel's shapes: rb_link_node's descent inline in owner code (a phi over
// &root->rb_node and &parent->rb_left/rb_right) followed by rb_insert_color
// on the same node and root (an implicit insert, matched), RB_CLEAR_NODE's
// self-link (R2), __rb_parent_color as a link word (parent | color, R1),
// and rb_first/rb_next traversal. Report only: the rows are not applied,
// the icall keeps both targets.
// CFLAGS: -O2
// LOG: Container: rbtree \(hand, report\)
// LOG: storage \(hand, declared\): handle struct.rb_root\+0; link struct.rb_node\+16 struct.rb_node\+8; link word struct.rb_node\+0; unused declared storage struct.rb_root_cached\+8
// LOG: implicit inserts 1 matched, 0 unmatched
// LOG: self-link stores \(R2\) [1-9]
// LOG: link word struct.rb_node\+0: R1 PASS
// LOG: O1 PASS
// LOG: REPORT ONLY: the obligations hold \(rows not applied\)
// NOLOG: VERIFIED \(rows applied\)
#include <stddef.h>
typedef void (*fn)(void);
struct rb_node {
  unsigned long __rb_parent_color;
  struct rb_node *rb_right;
  struct rb_node *rb_left;
} __attribute__((aligned(sizeof(long))));
struct rb_root { struct rb_node *rb_node; };
struct rb_root_cached { struct rb_root rb_root; struct rb_node *rb_leftmost; };
#define rb_parent(r) ((struct rb_node *)((r)->__rb_parent_color & ~3UL))
#define container_of(p, T, m) ((T *)((char *)(p)-offsetof(T, m)))
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
__attribute__((noinline)) void rb_erase(struct rb_node *node, struct rb_root *root) {
  struct rb_node *child = node->rb_right ? node->rb_right : node->rb_left;
  struct rb_node *parent = rb_parent(node);
  if (child) rb_set_parent_color(child, parent, 0);
  if (!parent) root->rb_node = child;
  else if (parent->rb_left == node) parent->rb_left = child;
  else parent->rb_right = child;
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
struct item { long key; fn f; struct rb_node node; };
struct tree { int n; struct rb_root root; } T;
__attribute__((noinline)) void add(struct item *it) {
  struct rb_node **p = &T.root.rb_node, *parent = NULL;
  while (*p) {
    parent = *p;
    p = it->key < container_of(parent, struct item, node)->key ? &parent->rb_left : &parent->rb_right;
  }
  it->node.__rb_parent_color = (unsigned long)parent; // rb_link_node
  it->node.rb_left = it->node.rb_right = NULL;
  *p = &it->node;
  rb_insert_color(&it->node, &T.root);
}
__attribute__((noinline)) void init(struct item *it) { it->node.__rb_parent_color = (unsigned long)&it->node; }
void a(void) {}
void b(void) {}
int main(void) {
  static struct item i1 = {1, a}, i2 = {2, b};
  init(&i1);
  init(&i2);
  add(&i1);
  add(&i2);
  for (struct rb_node *n = rb_first(&T.root); n; n = rb_next(n))
    container_of(n, struct item, node)->f(); // CHECK: a b
  rb_erase(&i1.node, &T.root);
  return 0;
}
