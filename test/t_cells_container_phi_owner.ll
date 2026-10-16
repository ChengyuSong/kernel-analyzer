; // t_cells_container_phi_owner.ll — owner and element through phis of
; // equal steps (Fable 2026-10-16 S3): rt_mutex_enqueue's inlined
; // rb_add_cached computes `&lock->waiters` and `&waiter->tree_entry` on the
; // empty-tree and the descent paths and passes the phis to rb_insert_color.
; // A phi whose entries agree on object and offset is that object and offset,
; // so the stores on both paths pair with the call.
; // CFLAGS: -O2 -g0 -fno-strict-aliasing
; // MODULE: t2_cells_rblib.c
; // LOG: implicit inserts [3-9] matched, 0 unmatched
; // LOG: link stores on the inserted element [1-9]
; // NOLOG: outside the rows
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"
%struct.rb_node = type { i64, ptr, ptr }
%struct.rb_root = type { ptr }
%struct.rb_root_cached = type { %struct.rb_root, ptr }
%struct.lock = type { i64, %struct.rb_root_cached }
%struct.waiter = type { i64, %struct.rb_node, i32 }

define void @enqueue(ptr %0, ptr %1) {
  %h = getelementptr inbounds %struct.lock, ptr %0, i64 0, i32 1, i32 0, i32 0
  %r = load ptr, ptr %h, align 8
  %z = icmp eq ptr %r, null
  br i1 %z, label %empty, label %walk

empty:
  %o1 = getelementptr inbounds %struct.lock, ptr %0, i64 0, i32 1
  %e1 = getelementptr inbounds %struct.waiter, ptr %1, i64 0, i32 1
  %h1 = getelementptr inbounds %struct.rb_root_cached, ptr %o1, i64 0, i32 0, i32 0
  store ptr %e1, ptr %h1, align 8
  br label %join

walk:
  %n = phi ptr [ %r, %2 ], [ %c, %walk ]
  %prio = getelementptr inbounds %struct.waiter, ptr %1, i64 0, i32 2
  %p = load i32, ptr %prio, align 4
  %lt = icmp slt i32 %p, 0
  %left = getelementptr inbounds %struct.rb_node, ptr %n, i64 0, i32 2
  %right = getelementptr inbounds %struct.rb_node, ptr %n, i64 0, i32 1
  %s = select i1 %lt, ptr %left, ptr %right
  %c = load ptr, ptr %s, align 8
  %cz = icmp eq ptr %c, null
  br i1 %cz, label %found, label %walk

found:
  %e2 = getelementptr inbounds %struct.waiter, ptr %1, i64 0, i32 1
  %pw = ptrtoint ptr %n to i64
  %w = getelementptr inbounds %struct.rb_node, ptr %e2, i64 0, i32 0
  store i64 %pw, ptr %w, align 8
  store ptr %e2, ptr %s, align 8
  %o2 = getelementptr inbounds %struct.lock, ptr %0, i64 0, i32 1
  br label %join

join:
  %o = phi ptr [ %o1, %empty ], [ %o2, %found ]
  %e = phi ptr [ %e1, %empty ], [ %e2, %found ]
  %lm = getelementptr inbounds %struct.rb_root_cached, ptr %o, i64 0, i32 1
  store ptr %e, ptr %lm, align 8
  %root = getelementptr inbounds %struct.rb_root_cached, ptr %o, i64 0, i32 0
  tail call void @rb_insert_color(ptr noundef %e, ptr noundef %root)
  ret void
}
declare void @rb_insert_color(ptr, ptr)
