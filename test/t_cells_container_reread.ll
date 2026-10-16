; // t_cells_container_reread.ll — the owner read twice (Fable 2026-10-16
; // S6): insert_header reads the tree root from one named slot for the
; // handle and again for the row's owner. Two loads of one named slot are
; // one value when every write between them is named and none has the
; // slot's name: checked (insert_checked). An unnamed write or a call to a
; // function that is not a row between them makes it a per-site
; // ASSUMPTION (insert_assumed). A write of the slot itself keeps them apart:
; // the store through the first read is a store outside the rows
; // (insert_moved).
; // CFLAGS: -O2 -g0 -fno-strict-aliasing
; // MODULE: t2_cells_rblib.c
; // LOG: owner re-read from the same slot \(S6\): 1 checked .*, 1 ASSUMPTION
; // LOG: ASSUMPTION owner re-read from the same slot: insert_assumed: .*%root2 = load ptr, ptr %rA
; // LOG: implicit insert matched: insert_checked: store ptr %e, ptr %h
; // LOG: implicit insert matched: insert_assumed: store ptr %e, ptr %h
; // LOG: storage FAIL a store into struct.rb_root\+0 outside the rows: 1 sites
; // LOG: O1 FAIL\(a store into struct.rb_root\+0 outside the rows: 1 \[insert_moved: store ptr %e, ptr %h
; // NOLOG: implicit insert UNMATCHED: insert_(checked|assumed)
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"
%struct.rb_node = type { i64, ptr, ptr }
%struct.rb_root = type { ptr }
%struct.dir = type { i64, ptr }
%struct.entry = type { i64, %struct.rb_node, ptr }

define void @insert_checked(ptr %0, ptr %1) {
  %rA = getelementptr inbounds %struct.dir, ptr %0, i64 0, i32 1
  %root1 = load ptr, ptr %rA, align 8
  %h = getelementptr inbounds %struct.rb_root, ptr %root1, i64 0, i32 0
  %e = getelementptr inbounds %struct.entry, ptr %1, i64 0, i32 1
  %w = getelementptr inbounds %struct.rb_node, ptr %e, i64 0, i32 0
  store i64 0, ptr %w, align 8
  %x = getelementptr inbounds %struct.entry, ptr %1, i64 0, i32 2
  store ptr null, ptr %x, align 8
  store ptr %e, ptr %h, align 8
  %root2 = load ptr, ptr %rA, align 8
  tail call void @rb_insert_color(ptr noundef %e, ptr noundef %root2)
  ret void
}

define void @insert_assumed(ptr %0, ptr %1) {
  %rA = getelementptr inbounds %struct.dir, ptr %0, i64 0, i32 1
  %root1 = load ptr, ptr %rA, align 8
  %h = getelementptr inbounds %struct.rb_root, ptr %root1, i64 0, i32 0
  %e = getelementptr inbounds %struct.entry, ptr %1, i64 0, i32 1
  %w = getelementptr inbounds %struct.rb_node, ptr %e, i64 0, i32 0
  store i64 0, ptr %w, align 8
  store ptr %e, ptr %h, align 8
  tail call void @log_insert(ptr noundef %1)
  %root2 = load ptr, ptr %rA, align 8
  tail call void @rb_insert_color(ptr noundef %e, ptr noundef %root2)
  ret void
}

define void @insert_moved(ptr %0, ptr %1, ptr %2) {
  %rA = getelementptr inbounds %struct.dir, ptr %0, i64 0, i32 1
  %root1 = load ptr, ptr %rA, align 8
  %h = getelementptr inbounds %struct.rb_root, ptr %root1, i64 0, i32 0
  %e = getelementptr inbounds %struct.entry, ptr %1, i64 0, i32 1
  %w = getelementptr inbounds %struct.rb_node, ptr %e, i64 0, i32 0
  store i64 0, ptr %w, align 8
  store ptr %e, ptr %h, align 8
  store ptr %2, ptr %rA, align 8
  %root2 = load ptr, ptr %rA, align 8
  tail call void @rb_insert_color(ptr noundef %e, ptr noundef %root2)
  ret void
}
declare void @rb_insert_color(ptr, ptr)
declare void @log_insert(ptr)
