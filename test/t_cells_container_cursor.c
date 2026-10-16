// t_cells_container_cursor.c — an element pointer kept in a plain field
// (Fable 2026-10-16): ext4_readdir's `info->curr_node = rb_next(info->curr_node)`
// keeps a traverse result in a cursor field outside the declared storage.
// O1 constrains stores into declared slots and stores of link values, not
// every copy of an element pointer: counted, never a FAIL. (step's value is
// rb_next of the cursor read back from the plain field: whether that read is
// derived is the closed-cursor check, S7, with its own case.)
// CFLAGS: -O2 -g0 -fno-strict-aliasing
// MODULE: t2_cells_rblib.c
// LOG: an element pointer kept in a plain field [1-9]
// LOG: an element pointer kept in a plain field: start:
// NOLOG: an element stored outside the declared storage
#include "cells_rb.h"
typedef void (*fn)(void);
struct item { long key; fn f; struct rb_node node; };
struct dir_info { struct rb_root root; struct rb_node *curr_node; };
__attribute__((noinline)) void start(struct dir_info *info) { info->curr_node = rb_first(&info->root); }
__attribute__((noinline)) void step(struct dir_info *info) { info->curr_node = rb_next(info->curr_node); }
void a(void) {}
int main(void) {
  static struct item i1 = {1, a};
  static struct dir_info D;
  rb_insert_color(&i1.node, &D.root);
  start(&D);
  step(&D);
  if (D.curr_node) container_of(D.curr_node, struct item, node)->f();
  return 0;
}
