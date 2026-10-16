// t_cells_container_past_layout.c — class 3 (Fable 2026-10-15): a GEP
// contributes a byte offset to its base's name; its source type names the
// base only at leading index 0. alarm_fired's container_of(t, struct alarm,
// timer) steps 32 bytes before a base named hrtimer: "a step past the
// layout of hrtimer", an ASSUMPTION at the row call, not a FAIL. A byte
// step inside a named base (the uuid node 24 bytes into a hash cell) is
// named by the base plus the offset and agrees.
// CFLAGS: -O2 -g0 -fno-strict-aliasing
// MODULE: t2_cells_rblib.c
// LOG: ASSUMPTION premise, a step past the layout of alarm_fired: .*\(arg0, struct.rb_node\): struct.hrtimer-32
// LOG: agree \([1-9] named by a base plus a byte offset
// NOLOG: premise FAIL
#include "cells_rb.h"
struct timerqueue_node { struct rb_node node; long expires; };
struct hrtimer { struct timerqueue_node node; long _softexpires; void (*function)(struct hrtimer *); };
struct alarm { struct timerqueue_node node; struct hrtimer timer; int state; };
struct hash_cell { struct rb_node name_node; struct rb_node uuid_node; const char *name; };
struct rb_root R, U;
__attribute__((noinline)) void alarm_fired(struct hrtimer *t) {
  struct alarm *a = container_of(t, struct alarm, timer);
  t->_softexpires = 0;
  rb_erase(&a->node.node, &R);
}
__attribute__((noinline)) void add_uuid(struct hash_cell *hc) {
  hc->name = "x";
  struct rb_node *n = (struct rb_node *)((char *)hc + offsetof(struct hash_cell, uuid_node));
  n->__rb_parent_color = 0;
  n->rb_left = n->rb_right = NULL;
  U.rb_node = n;
  rb_insert_color(n, &U);
}
struct alarm A;
struct hash_cell H;
int main(void) {
  alarm_fired(&A.timer);
  add_uuid(&H);
  return 0;
}
