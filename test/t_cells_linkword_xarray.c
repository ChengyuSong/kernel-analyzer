// CFLAGS: -O2
// Plan 3.55 R1 addendum: XArray-shaped pointer fields receive encoded words
// (a node | 2, values (v << 1) | 1, internal constants (v << 2) | 2) besides
// untagged pointers; reads decode a node by subtracting 2 and test the low
// bits. Step 1 reports the shapes by the (b) clauses, no verdict.
// LOG: LinkWord: struct.xarray\+8: encoded pointer field .*node link \(tag 2\) [1-9]
// LOG: LinkWord: struct.xa_node\+8: encoded pointer field .*internal constant [1-9].*untagged pointer [1-9].*value encoding [1-9]
// LOG: subtract-decode [1-9]
// LOG: low-bit test [1-9]
struct xa_node { struct xa_node *parent; void *slots[4]; };
struct xarray { int xa_lock; unsigned xa_flags; void *xa_head; }; // xa_head past offset 0, as in the kernel (a GEP names it)
static inline void *xa_mk_node(struct xa_node *n) { return (void *)((unsigned long)n | 2); }
static inline struct xa_node *xa_to_node(void *e) { return (struct xa_node *)((unsigned long)e - 2); }
static inline int xa_is_node(void *e) { return ((unsigned long)e & 3) == 2 && (unsigned long)e > 4096; }
static inline void *xa_mk_value(unsigned long v) { return (void *)((v << 1) | 1); }
void grow(struct xarray *xa, struct xa_node *n) {
  n->slots[0] = xa->xa_head;
  xa->xa_head = xa_mk_node(n);
}
void put_value(struct xa_node *n, unsigned i, unsigned long v) { n->slots[i & 3] = xa_mk_value(v); }
void put_retry(struct xa_node *n) { n->slots[1] = (void *)((256UL << 2) | 2); }
void put_ptr(struct xa_node *n, unsigned i, void *p) { n->slots[i & 3] = p; }
void *walk(struct xarray *xa) {
  void *e = xa->xa_head;
  while (xa_is_node(e)) e = xa_to_node(e)->slots[0];
  return e;
}
struct xarray xa;
struct xa_node node;
int item;
int main(void) {
  put_ptr(&node, 2, &item);
  grow(&xa, &node);
  put_value(&node, 3, 7);
  put_retry(&node);
  return walk(&xa) == &item;
}
