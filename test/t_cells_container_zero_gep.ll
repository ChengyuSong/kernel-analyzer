; // t_cells_container_zero_gep.ll — an element at +0 of its object through
; // a zero-index struct GEP (Fable 2026-10-16 S1; the kernel's clang-14 IR
; // keeps `gep %struct.epitem, %1, 0, 0`, clang-18 folds it, hence assembly):
; // ep_remove's inlined rb_erase_cached. The group's element and rb_next's
; // actual are one element by object and offset, so the leftmost update
; // stores a derived value into a derived slot: an owner-code relink, not an
; // implicit insert without an insert row.
; // CFLAGS: -O2 -g0 -fno-strict-aliasing
; // MODULE: t2_cells_rblib.c
; // LOG: owner-code relinks [1-9]
; // NOLOG: implicit insert UNMATCHED
; // NOLOG: outside the rows
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"
%struct.rb_node = type { i64, ptr, ptr }
%struct.rb_root = type { ptr }
%struct.rb_root_cached = type { %struct.rb_root, ptr }
%struct.epitem = type { %struct.rb_node, ptr }
%struct.eventpoll = type { i64, %struct.rb_root_cached }

define void @ep_remove(ptr %0, ptr %1) {
  %3 = getelementptr inbounds %struct.epitem, ptr %1, i64 0, i32 0
  %4 = getelementptr inbounds %struct.eventpoll, ptr %0, i64 0, i32 1, i32 1
  %5 = load ptr, ptr %4, align 8
  %6 = icmp eq ptr %5, %3
  br i1 %6, label %7, label %9

7:
  %8 = tail call ptr @rb_next(ptr noundef %3)
  store ptr %8, ptr %4, align 8
  br label %9

9:
  %10 = getelementptr inbounds %struct.eventpoll, ptr %0, i64 0, i32 1, i32 0
  tail call void @rb_erase(ptr noundef %3, ptr noundef %10)
  ret void
}
declare ptr @rb_next(ptr)
declare void @rb_erase(ptr, ptr)
