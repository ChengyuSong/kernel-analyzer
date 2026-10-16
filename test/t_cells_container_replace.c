// t_cells_container_replace.c — rb_replace_node (Fable 2026-10-15, (E)):
// `*new = *victim` copies the victim's link record, its parent word and
// color included (the new node takes the victim's place: both are ELEMs of
// the row), admitted as a copy of an element's links; the children's
// parent words set from `new` with their own color bit (ptrtoint, or with a
// tag extract, into a declared LINKWORD) are link stores, not an escape.
// CFLAGS: -O2 -g0 -fno-strict-aliasing
// MODULE: t2_cells_rblib.c
// LOG: copies of an element's links \(with the link word's tag\) [1-9]
// NOLOG: O3 FAIL.*rb_replace_node
#include "cells_rb.h"
typedef void (*fn)(void);
struct item { long key; fn f; struct rb_node node; };
struct rb_root T;
void a(void) {}
void b(void) {}
int main(void) {
  static struct item i1 = {1, a}, i2 = {1, b};
  i1.node.__rb_parent_color = 1;
  T.rb_node = &i1.node;
  rb_insert_color(&i1.node, &T);
  rb_replace_node(&i1.node, &i2.node, &T);
  container_of(rb_first(&T), struct item, node)->f();
  return 0;
}
