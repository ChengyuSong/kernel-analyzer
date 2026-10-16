// t_cells_linkword_union.c — class 2 in R1 (the 5.18 timerfd_ctx shape,
// Fable 2026-10-15): `union { struct hrtimer tmr; struct alarm alarm; }`
// is typed in the IR as its alarm member (clang's representative), so
// hrtimer_set_expires's write of tmr._softexpires (+32) lands on
// alarm.timer.node.node.__rb_parent_color, named rb_node+0 by the old walk
// (a "store: constant >= 8" FAIL of the link word). The name stops at the
// union: storage inside a union, counted, not an access of the link word.
// The union sits after a field so that clang 18 (opaque pointers) keeps
// the path through it in one struct GEP, as clang 14's IR does.
// CFLAGS: -O2 -g0 -fno-strict-aliasing
// MODULE: t2_cells_rblib.c
// LOG: LinkWord: storage inside a union \(the IR's member is clang's representative\): [1-9][0-9]* accesses
// NOLOG: FAIL struct.rb_node\+0: store: argument at settime
// NOLOG: FAIL struct.rb_node\+0: load: returned at gettime
#include "cells_rb.h"
struct timerqueue_node { struct rb_node node; long expires; };
struct hrtimer { struct timerqueue_node node; long _softexpires; void *function; void *base; };
struct alarm { struct timerqueue_node node; struct hrtimer timer; void *function; int type, state; void *data; };
struct timerfd_ctx { long tintv; union { struct hrtimer tmr; struct alarm alarm; } t; int clockid; };
struct rb_root R;
__attribute__((noinline)) void settime(struct timerfd_ctx *ctx, long texp) {
  ctx->t.tmr.node.expires = texp;
  ctx->t.tmr._softexpires = texp; // hrtimer_set_expires
}
__attribute__((noinline)) long gettime(struct timerfd_ctx *ctx) { return ctx->t.tmr._softexpires; }
__attribute__((noinline)) void arm(struct timerfd_ctx *ctx) {
  struct rb_node *n = &ctx->t.alarm.timer.node.node;
  n->__rb_parent_color = 0;
  n->rb_left = n->rb_right = NULL;
  R.rb_node = n;
  rb_insert_color(n, &R);
}
struct timerfd_ctx C;
int main(void) {
  settime(&C, 1L << 40);
  arm(&C);
  return gettime(&C) > 0 && rb_first(&R) != NULL;
}
