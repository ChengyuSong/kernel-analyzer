; // t_cells_container_descent.ll — descents that start at a node not
; // derived from the owner (Fable 2026-10-16 S7), never a FAIL:
; // - insert_from (insert_vmap_area_augment's find_va_links from `from`): a
; //   node from a caller formal is a listed ASSUMPTION "descent from a node
; //   assumed an element";
; // - frag_insert (inet_frag_queue_insert's q->fragments_tail): a node read
; //   back from a plain field of the owner's object is derived when every
; //   store into that field, program-wide by name, stores an element of the
; //   owner or null: a CLOSED CURSOR (struct.fq+16);
; // - frag_insert2: the same shape, but frag_set2 stores another value into
; //   the field, so the read is a per-site ASSUMPTION (struct.fq2+16).
; // CFLAGS: -O2 -g0 -fno-strict-aliasing
; // MODULE: t2_cells_rblib.c
; // LOG: ASSUMPTION descent from a node assumed an element: insert_from: +%n = phi ptr \[ %1, %entry \]
; // LOG: cursor field struct.fq\+16 CLOSED CURSOR \(every store an element of the owner, at \+0\)
; // LOG: cursor field struct.fq2\+16 not closed
; // LOG: ASSUMPTION a node read back from a plain field: frag_insert2: +%tail = load ptr, ptr %tailA.*\(struct.fq2\+16, \+0\)
; // NOLOG: ASSUMPTION a node read back from a plain field: frag_insert:
; // LOG: implicit inserts 3 matched, 0 unmatched
; // NOLOG: outside the rows
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"
%struct.rb_node = type { i64, ptr, ptr }
%struct.rb_root = type { ptr }
%struct.va = type { i64, %struct.rb_node }
%struct.skb = type { %struct.rb_node, i32 }
%struct.fq = type { i64, %struct.rb_root, ptr }
%struct.fq2 = type { i64, %struct.rb_root, ptr }

define void @insert_from(ptr %0, ptr %1, ptr %2) {
entry:
  %z = icmp eq ptr %1, null
  br i1 %z, label %fromroot, label %walk

walk:
  %n = phi ptr [ %1, %entry ], [ %c, %walk ]
  %ka = getelementptr inbounds %struct.va, ptr %0, i64 0, i32 0
  %k = load i64, ptr %ka, align 8
  %lt = icmp slt i64 %k, 0
  %left = getelementptr inbounds %struct.rb_node, ptr %n, i64 0, i32 2
  %right = getelementptr inbounds %struct.rb_node, ptr %n, i64 0, i32 1
  %s = select i1 %lt, ptr %left, ptr %right
  %c = load ptr, ptr %s, align 8
  %cz = icmp eq ptr %c, null
  br i1 %cz, label %link, label %walk

fromroot:
  %h = getelementptr inbounds %struct.rb_root, ptr %2, i64 0, i32 0
  br label %link

link:
  %parent = phi ptr [ %n, %walk ], [ null, %fromroot ]
  %l = phi ptr [ %s, %walk ], [ %h, %fromroot ]
  %e = getelementptr inbounds %struct.va, ptr %0, i64 0, i32 1
  %pw = ptrtoint ptr %parent to i64
  %w = getelementptr inbounds %struct.rb_node, ptr %e, i64 0, i32 0
  store i64 %pw, ptr %w, align 8
  store ptr %e, ptr %l, align 8
  tail call void @rb_insert_color(ptr noundef %e, ptr noundef %2)
  ret void
}

define void @frag_insert(ptr %0, ptr %1) {
entry:
  %tailA = getelementptr inbounds %struct.fq, ptr %0, i64 0, i32 2
  %tail = load ptr, ptr %tailA, align 8
  %z = icmp eq ptr %tail, null
  br i1 %z, label %empty, label %append

empty:
  %h = getelementptr inbounds %struct.fq, ptr %0, i64 0, i32 1, i32 0
  br label %link

append:
  %rr = getelementptr inbounds %struct.skb, ptr %tail, i64 0, i32 0, i32 1
  %pw = ptrtoint ptr %tail to i64
  %w = getelementptr inbounds %struct.skb, ptr %1, i64 0, i32 0, i32 0
  store i64 %pw, ptr %w, align 8
  br label %link

link:
  %l = phi ptr [ %h, %empty ], [ %rr, %append ]
  store ptr %1, ptr %l, align 8
  %root = getelementptr inbounds %struct.fq, ptr %0, i64 0, i32 1
  tail call void @rb_insert_color(ptr noundef %1, ptr noundef %root)
  store ptr %1, ptr %tailA, align 8
  ret void
}

define void @frag_reset(ptr %0) {
  %tailA = getelementptr inbounds %struct.fq, ptr %0, i64 0, i32 2
  store ptr null, ptr %tailA, align 8
  ret void
}

define void @frag_insert2(ptr %0, ptr %1) {
entry:
  %tailA = getelementptr inbounds %struct.fq2, ptr %0, i64 0, i32 2
  %tail = load ptr, ptr %tailA, align 8
  %z = icmp eq ptr %tail, null
  br i1 %z, label %empty, label %append

empty:
  %h = getelementptr inbounds %struct.fq2, ptr %0, i64 0, i32 1, i32 0
  br label %link

append:
  %rr = getelementptr inbounds %struct.skb, ptr %tail, i64 0, i32 0, i32 1
  br label %link

link:
  %l = phi ptr [ %h, %empty ], [ %rr, %append ]
  store ptr %1, ptr %l, align 8
  %root = getelementptr inbounds %struct.fq2, ptr %0, i64 0, i32 1
  tail call void @rb_insert_color(ptr noundef %1, ptr noundef %root)
  store ptr %1, ptr %tailA, align 8
  ret void
}

define void @frag_set2(ptr %0, ptr %1) {
  %tailA = getelementptr inbounds %struct.fq2, ptr %0, i64 0, i32 2
  store ptr %1, ptr %tailA, align 8
  ret void
}
declare void @rb_insert_color(ptr, ptr)
