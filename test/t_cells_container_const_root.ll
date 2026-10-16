; // t_cells_container_const_root.ll — a root read through a constant
; // address (Fable 2026-10-16 S2): __mod_tree_insert's latch tree, whose
; // root `&mod_tree.root.tree[0]` is a constant GEP. The constant slot is
; // known before the derivation, so the descent from its load is derived and
; // rb_link_node_rcu's `*link = node` and the parent word pair with the
; // rb_insert_color call.
; // CFLAGS: -O2 -g0 -fno-strict-aliasing
; // MODULE: t2_cells_rblib.c
; // LOG: implicit inserts [1-9] matched, 0 unmatched
; // LOG: link stores on the inserted element [1-9]
; // NOLOG: outside the rows
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"
%struct.rb_node = type { i64, ptr, ptr }
%struct.rb_root = type { ptr }
%struct.latch_root = type { i64, [2 x %struct.rb_root] }
%struct.latch_node = type { i64, [2 x %struct.rb_node] }
@L = global %struct.latch_root zeroinitializer

define void @latch_insert(ptr %0) {
  %e = getelementptr inbounds %struct.latch_node, ptr %0, i64 0, i32 1, i64 0
  %r = load ptr, ptr getelementptr inbounds (%struct.latch_root, ptr @L, i64 0, i32 1, i64 0, i32 0), align 8
  %z = icmp eq ptr %r, null
  br i1 %z, label %done, label %walk

walk:
  %n = phi ptr [ %r, %1 ], [ %c, %walk ]
  %lt = icmp ult ptr %e, %n
  %left = getelementptr inbounds %struct.rb_node, ptr %n, i64 0, i32 2
  %right = getelementptr inbounds %struct.rb_node, ptr %n, i64 0, i32 1
  %s = select i1 %lt, ptr %left, ptr %right
  %c = load ptr, ptr %s, align 8
  %cz = icmp eq ptr %c, null
  br i1 %cz, label %found, label %walk

found:
  %pw = ptrtoint ptr %n to i64
  br label %done

done:
  %link = phi ptr [ %s, %found ], [ getelementptr inbounds (%struct.latch_root, ptr @L, i64 0, i32 1, i64 0, i32 0), %1 ]
  %par = phi i64 [ %pw, %found ], [ 0, %1 ]
  %w = getelementptr inbounds %struct.rb_node, ptr %e, i64 0, i32 0
  store i64 %par, ptr %w, align 8
  store volatile ptr %e, ptr %link, align 8
  tail call void @rb_insert_color(ptr noundef %e, ptr noundef getelementptr inbounds (%struct.latch_root, ptr @L, i64 0, i32 1, i64 0))
  ret void
}
declare void @rb_insert_color(ptr, ptr)
