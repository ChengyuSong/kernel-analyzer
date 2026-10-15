// CFLAGS: -O2
// Plan 3.55 R1: rb_node.__rb_parent_color (parent | color) is a link word:
// stores are ptrtoint(p) (link), p + color (rb_set_parent_color), the
// node's own address (RB_CLEAR_NODE: a self-link); reads mask the tag
// (rb_parent), compare (RB_EMPTY_NODE), or, in gparent, convert unmasked
// (rb_red_parent: the program relies on tag 0, stated as an assumption).
// LOG: LinkWord: struct.rb_node\+0: PASS with 2 assumptions; .*self-link [1-9],
// LOG: ASSUMPTION struct.rb_node\+0: the program relies on tag 0 at this read: gparent:
// LOG: LinkWord: 1 integer fields read as pointers: 0 pass, 1 pass with assumptions
struct rb_node {
  unsigned long __rb_parent_color;
  struct rb_node *rb_right, *rb_left;
} __attribute__((aligned(sizeof(long))));
#define rb_parent(r) ((struct rb_node *)((r)->__rb_parent_color & ~3UL))
#define RB_EMPTY_NODE(n) ((n)->__rb_parent_color == (unsigned long)(n))
#define RB_CLEAR_NODE(n) ((n)->__rb_parent_color = (unsigned long)(n))
static inline void rb_set_parent_color(struct rb_node *rb, struct rb_node *p, int color) {
  rb->__rb_parent_color = (unsigned long)p + color;
}
static inline struct rb_node *rb_red_parent(struct rb_node *red) { return (struct rb_node *)red->__rb_parent_color; }
void rb_link_node(struct rb_node *n, struct rb_node *parent, struct rb_node **link) {
  n->__rb_parent_color = (unsigned long)parent;
  n->rb_left = n->rb_right = 0;
  *link = n;
}
void make_black(struct rb_node *n, struct rb_node *p) { rb_set_parent_color(n, p, 1); }
void clear(struct rb_node *n) { RB_CLEAR_NODE(n); }
struct rb_node *rb_next(struct rb_node *node) {
  struct rb_node *parent;
  if (RB_EMPTY_NODE(node)) return 0;
  if (node->rb_right) {
    node = node->rb_right;
    while (node->rb_left) node = node->rb_left;
    return node;
  }
  while ((parent = rb_parent(node)) && node == parent->rb_right) node = parent;
  return parent;
}
struct rb_node *gparent(struct rb_node *node) { return rb_red_parent(rb_red_parent(node)); }
struct rb_node a, b, *root;
int main(void) {
  rb_link_node(&a, 0, &root);
  rb_link_node(&b, &a, &a.rb_right);
  make_black(&a, 0);
  clear(&b);
  return rb_next(&a) == gparent(&b);
}
