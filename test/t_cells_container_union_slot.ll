; // t_cells_container_union_slot.ll — a container slot inside a union
; // (Fable 2026-10-16 S5): vma_interval_tree_remove's node is
; // `&vma->shared.rb`, inside vm_area_struct's union, whose IR member is
; // clang's representative; without debug info the premise is an ASSUMPTION
; // "inside the union". Under that same assumption the actual's declared
; // slots at actual + k are its slots: the node's rb_right read through the
; // union is a link read, and storing it into the cached leftmost is an
; // owner-code relink, not a store outside the rows. Listed once per actual.
; // CFLAGS: -O2 -g0 -fno-strict-aliasing
; // MODULE: t2_cells_rblib.c
; // LOG: ASSUMPTION premise, inside a union: vma_remove_leftmost: .*\(arg0, struct.rb_node\): inside the union at struct.vma\+16
; // LOG: slots at a union actual \(S5\): [1-9][0-9]* addresses, 1 actuals
; // LOG: ASSUMPTION \(the premise's\) declared slots at a union actual \+ k: vma_remove_leftmost: .*rb_erase
; // LOG: owner-code relinks [1-9]
; // NOLOG: outside the rows
; // NOLOG: implicit insert UNMATCHED
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"
%struct.rb_node = type { i64, ptr, ptr }
%struct.rb_root = type { ptr }
%struct.rb_root_cached = type { %struct.rb_root, ptr }
%struct.anon = type { %struct.rb_node, i64 }
%union.anon = type { %struct.anon }
%struct.vma = type { i64, i64, %union.anon }

define void @vma_remove_leftmost(ptr %0, ptr %1) {
  %e = getelementptr inbounds %struct.vma, ptr %0, i64 0, i32 2, i32 0, i32 0
  %lmA = getelementptr inbounds %struct.rb_root_cached, ptr %1, i64 0, i32 1
  %lm = load ptr, ptr %lmA, align 8
  %is = icmp eq ptr %lm, %e
  br i1 %is, label %upd, label %out

upd:
  %rrA = getelementptr inbounds %struct.vma, ptr %0, i64 0, i32 2, i32 0, i32 0, i32 1
  %rr = load ptr, ptr %rrA, align 8
  store ptr %rr, ptr %lmA, align 8
  br label %out

out:
  %root = getelementptr inbounds %struct.rb_root_cached, ptr %1, i64 0, i32 0
  tail call void @rb_erase(ptr noundef %e, ptr noundef %root)
  ret void
}
declare void @rb_erase(ptr, ptr)
