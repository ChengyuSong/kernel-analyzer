; // t_cells_container_bytestep.ll — a descent by byte arithmetic (Fable
; // 2026-10-16 S4): interval_tree_generic's insert as clang-14 compiles
; // memtype_check_insert. The node is turned back into its struct
; // (`gep %struct.rb_node, %n, -1, 0`, node - 24) and stepped by a word index
; // that is a select of two constants (rb_left at +16, rb_right at +8 of the
; // node); `gep ptr, %b, 3` is the node itself. By bytes from a derived node,
; // each step lands on a declared slot of rb_node, so the child read is
; // derived, the link store pairs with the insert, and the parent word is a
; // link store on the inserted element.
; // CFLAGS: -O2 -g0 -fno-strict-aliasing
; // MODULE: t2_cells_rblib.c
; // LOG: implicit inserts [1-9] matched, 0 unmatched
; // LOG: link stores on the inserted element [1-9]
; // NOLOG: outside the rows
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"
%struct.rb_node = type { i64, ptr, ptr }
%struct.rb_root = type { ptr }
%struct.memtype = type { i64, i64, i64, %struct.rb_node }
@memtype_root = global %struct.rb_root zeroinitializer

define void @memtype_insert(ptr %0) {
  %key = getelementptr inbounds %struct.memtype, ptr %0, i64 0, i32 0
  %k = load i64, ptr %key, align 8
  %r = load ptr, ptr @memtype_root, align 8
  %z = icmp eq ptr %r, null
  br i1 %z, label %done, label %walk

walk:
  %n = phi ptr [ %r, %1 ], [ %c, %walk ]
  %b = getelementptr %struct.rb_node, ptr %n, i64 -1, i32 0
  %nk = load i64, ptr %b, align 8
  %lt = icmp ult i64 %k, %nk
  %idx = select i1 %lt, i64 5, i64 4
  %slot = getelementptr inbounds ptr, ptr %b, i64 %idx
  %c = load ptr, ptr %slot, align 8
  %cz = icmp eq ptr %c, null
  br i1 %cz, label %found, label %walk

found:
  %self = getelementptr inbounds ptr, ptr %b, i64 3
  %pw = ptrtoint ptr %self to i64
  br label %done

done:
  %link = phi ptr [ %slot, %found ], [ @memtype_root, %1 ]
  %par = phi i64 [ %pw, %found ], [ 0, %1 ]
  %e = getelementptr inbounds %struct.memtype, ptr %0, i64 0, i32 3
  %w = getelementptr inbounds %struct.rb_node, ptr %e, i64 0, i32 0
  store i64 %par, ptr %w, align 8
  store ptr %e, ptr %link, align 8
  tail call void @rb_insert_color(ptr noundef %e, ptr noundef @memtype_root)
  ret void
}
declare void @rb_insert_color(ptr, ptr)
