// t_cells_container_cached.c — 4(b) and the phi pairing (Fable 2026-10-15):
// rb_insert_color_cached inlined into owner code. The leftmost store
// (rb_root_cached+8, a HANDLE of the owner) and rb_link_node's `*link =
// node` pair with the rb_insert_color call on the cached root's rb_root
// (+0: one owner by object and offset), the stored node reaching the call's
// element through a phi.
// CFLAGS: -O2 -g0 -fno-strict-aliasing
// MODULE: t2_cells_rblib.c
// LOG: implicit inserts [2-9] matched, 0 unmatched
// NOLOG: outside the rows
// NOLOG: implicit insert UNMATCHED
#include "cells_rb.h"
#include <stdbool.h>
typedef void (*fn)(void);
struct item { long key; fn f; struct rb_node node; };
struct rb_root_cached TC;
__attribute__((noinline)) void insert_cached(struct item *it) {
  struct rb_node **link = &TC.rb_root.rb_node, *parent = NULL;
  bool leftmost = true;
  while (*link) {
    parent = *link;
    if (it->key < container_of(parent, struct item, node)->key) {
      link = &parent->rb_left;
    } else {
      link = &parent->rb_right;
      leftmost = false;
    }
  }
  if (leftmost) TC.rb_leftmost = &it->node;
  rb_link_node(&it->node, parent, link);
  rb_insert_color(&it->node, &TC.rb_root);
}
void a(void) {}
void b(void) {}
int main(void) {
  static struct item i1 = {1, a}, i2 = {2, b};
  insert_cached(&i1);
  insert_cached(&i2);
  container_of(TC.rb_leftmost, struct item, node)->f();
  return 0;
}
