// CFLAGS: -O2 -g0 -fno-strict-aliasing
// Plan 3.55 R1 naming (the kernel's build: no debug info, no TBAA): an
// offset-0 access through a formal has no struct GEP, so its field is named
// by its sibling GEPs (n is also the base of `n->rb_right`: an rb_node). A
// base GEP'd as two unrelated structs (rb_node and other) is a pun: its offset-0 access stays
// unnamed and is counted.
// LOG: LinkWord: struct.rb_node\+0: PASS
// LOG: by sibling GEPs, 0 by formal provenance, 0 by a named base plus a byte offset; 1 unnamed that would feed a link word, in 1 functions \(pun 1\)
struct rb_node {
  unsigned long __rb_parent_color;
  struct rb_node *rb_right, *rb_left;
} __attribute__((aligned(sizeof(long))));
struct other { int a; long x; };
void clear(struct rb_node *n) {
  n->__rb_parent_color = (unsigned long)n;
  n->rb_right = 0;
}
struct rb_node *parent(struct rb_node *n) {
  return n->rb_left ? n->rb_left : (struct rb_node *)(n->__rb_parent_color & ~3UL);
}
void pun(void *p) {
  ((struct rb_node *)p)->__rb_parent_color = (unsigned long)p;
  ((struct rb_node *)p)->rb_left = 0;
  ((struct other *)p)->x = 1;
}
struct rb_node a;
int main(void) {
  clear(&a);
  pun(&a);
  return parent(&a) == &a;
}
