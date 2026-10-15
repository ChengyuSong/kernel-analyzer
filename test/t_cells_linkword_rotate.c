// CFLAGS: -O2
// Plan 3.55 R1, the rotation shape (__rb_rotate_set_parents, rb_set_parent):
// a node's word copied into another node's word, and the color carried from
// a load of the word onto a new parent (rb_color(rb) + p): copies and tag
// values are tagged words, so the field passes.
// LOG: LinkWord: struct.rb_node\+0: PASS; stores .*copy [1-9].*copies [1-9]
// NOLOG: FAIL struct.rb_node
struct rb_node {
  unsigned long __rb_parent_color;
  struct rb_node *rb_right, *rb_left;
} __attribute__((aligned(sizeof(long))));
#define rb_parent(r) ((struct rb_node *)((r)->__rb_parent_color & ~3UL))
#define rb_color(r) ((r)->__rb_parent_color & 1)
static inline void rb_set_parent(struct rb_node *rb, struct rb_node *p) {
  rb->__rb_parent_color = rb_color(rb) + (unsigned long)p;
}
static inline void rb_set_parent_color(struct rb_node *rb, struct rb_node *p, int color) {
  rb->__rb_parent_color = (unsigned long)p + color;
}
static inline void rotate_set_parents(struct rb_node *old, struct rb_node *new, int color) {
  new->__rb_parent_color = old->__rb_parent_color;
  rb_set_parent_color(old, new, color);
}
void rotate_left(struct rb_node *node) {
  struct rb_node *r = node->rb_right;
  node->rb_right = r->rb_left;
  if (r->rb_left) rb_set_parent(r->rb_left, node);
  r->rb_left = node;
  rotate_set_parents(node, r, 0);
}
struct rb_node *up(struct rb_node *n) { return rb_parent(n); }
struct rb_node a, b;
int main(void) {
  a.rb_right = &b;
  rotate_left(&a);
  return up(&a) == &b;
}
