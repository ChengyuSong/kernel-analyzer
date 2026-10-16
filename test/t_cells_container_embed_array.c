// t_cells_container_embed_array.c — class 1 (Fable 2026-10-15): a row's
// OWNER actual inside an array member of another struct (latch_tree_root's
// rb_root tree[2]) agrees with the premise through the struct analyzer's
// embedding table, per array element; the old walk (struct members only)
// named it latch+16 and failed.
// CFLAGS: -O2
// MODULE: t2_cells_rblib.c
// LOG: row premise \(1c\): owner struct.rb_root, element struct.rb_node; 5 call-site arguments: 5 agree
// LOG: implicit inserts 2 matched, 0 unmatched
// NOLOG: premise FAIL
// NOLOG: embedding table disagrees
#include "cells_rb.h"
typedef void (*fn)(void);
struct latch { unsigned seq; struct rb_root tree[2]; };
struct item { long key; fn f; struct rb_node node[2]; };
struct latch L;
__attribute__((noinline)) void add(struct item *it) {
  for (int i = 0; i < 2; i++) {
    it->node[i].__rb_parent_color = 0;
    it->node[i].rb_left = it->node[i].rb_right = NULL;
    L.tree[i].rb_node = &it->node[i];
    rb_insert_color(&it->node[i], &L.tree[i]);
  }
}
void a(void) {}
int main(void) {
  static struct item i1 = {1, a};
  add(&i1);
  struct rb_node *n = rb_first(&L.tree[1]);
  if (n) container_of(n, struct item, node[1])->f();
  return 0;
}
