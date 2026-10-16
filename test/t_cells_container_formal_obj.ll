; // t_cells_container_formal_obj.ll — a descent from a formal object's node
; // (Fable 2026-10-16 Q1): vma_interval_tree_insert_after(node, prev, root)
; // starts at prev's rb_right, prev a formal used as a container object, its
; // node at the element actual's own offset (+16, inside the union as the
; // actual's). Per site an ASSUMPTION "descent from a formal object's node
; // at +e", the S7 formal premise in another dress; the parent word is
; // `&parent->shared.rb` with parent a phi of container_of(node) and prev:
; // every entry's object has an element at +16 (the phi meet over objects).
; // CFLAGS: -O2 -g0 -fno-strict-aliasing
; // MODULE: t2_cells_rblib.c
; // LOG: ASSUMPTION descent from a formal object's node at \+e, assumed an element: insert_after: ptr %1 at \+16
; // LOG: owner-code relinks [1-9]
; // LOG: implicit inserts 1 matched, 0 unmatched
; // NOLOG: outside the rows
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"
%struct.rb_node = type { i64, ptr, ptr }
%struct.rb_root = type { ptr }
%struct.rb_root_cached = type { %struct.rb_root, ptr }
%struct.anon = type { %struct.rb_node, i64 }
%union.anon = type { %struct.anon }
%struct.vma = type { i64, i64, %union.anon }

define void @insert_after(ptr %0, ptr %1, ptr %2) {
entry:
  %14 = getelementptr inbounds %struct.vma, ptr %1, i64 0, i32 2, i32 0, i32 0, i32 1
  %15 = load ptr, ptr %14, align 8
  %16 = icmp eq ptr %15, null
  br i1 %16, label %done, label %loop

loop:
  %29 = phi ptr [ %15, %entry ], [ %38, %loop ]
  %30 = getelementptr %struct.rb_node, ptr %29, i64 -1, i32 1
  %37 = getelementptr inbounds %struct.vma, ptr %30, i64 0, i32 2, i32 0, i32 0, i32 2
  %38 = load ptr, ptr %37, align 8
  %39 = icmp eq ptr %38, null
  br i1 %39, label %last, label %loop

last:
  br label %done

done:
  %45 = phi ptr [ %30, %last ], [ %1, %entry ]
  %46 = phi ptr [ %37, %last ], [ %14, %entry ]
  %48 = getelementptr inbounds %struct.vma, ptr %0, i64 0, i32 2, i32 0, i32 0
  %49 = getelementptr inbounds %struct.vma, ptr %45, i64 0, i32 2, i32 0, i32 0
  %50 = ptrtoint ptr %49 to i64
  %51 = getelementptr inbounds %struct.rb_node, ptr %48, i64 0, i32 0
  store i64 %50, ptr %51, align 8
  store ptr %48, ptr %46, align 8
  %54 = getelementptr inbounds %struct.rb_root_cached, ptr %2, i64 0, i32 0
  tail call void @rb_insert_color(ptr noundef %48, ptr noundef %54)
  ret void
}
declare void @rb_insert_color(ptr, ptr)
