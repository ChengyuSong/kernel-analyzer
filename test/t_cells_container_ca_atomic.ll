; // t_cells_container_ca_atomic.ll — the storage check visits an IR cmpxchg
; // (and atomicrmw) as a write (CA, Fable 2026-10-28): ca_llist_add2 sets the
; // handle with `cmpxchg ptr` (clang lowers a C pointer CAS to an i64 cmpxchg
; // of ptrtoints, hence hand IR), which the O1 walk did not visit, so a
; // container verified over a write it never checked. Now it is a checked
; // body write (counted), and CA skips it per site like the asm one: each
; // caller's element goes into its own head only.
; // KAFLAGS: --func-summaries=t_cells_container_ca.fs
; // LOG: storage writes admitted: .*; 2 atomic writes \(IR cmpxchg or atomicrmw\)
; // LOG: VERIFIED \(rows applied\)
; // LOG: container ca_llist: rows applied per site \(CA\): 2 insert sites, [0-9]+ edges \(handle and link writes\); [1-9] body writes
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"
%struct.ca_node = type { ptr }
%struct.ca_head = type { ptr }
%struct.A = type { %struct.ca_node, ptr }
%struct.B = type { %struct.ca_node, ptr }
@HA = global %struct.ca_head zeroinitializer
@HB = global %struct.ca_head zeroinitializer
@a = internal global %struct.A zeroinitializer
@b = internal global %struct.B zeroinitializer

define void @fa() { ret void }
define void @fb() { ret void }

define zeroext i1 @ca_llist_add2(ptr %new, ptr %head) noinline {
entry:
  br label %loop
loop:
  %hf = getelementptr inbounds %struct.ca_head, ptr %head, i64 0, i32 0
  %first = load volatile ptr, ptr %hf, align 8
  %nn = getelementptr inbounds %struct.ca_node, ptr %new, i64 0, i32 0
  store ptr %first, ptr %nn, align 8
  %pair = cmpxchg ptr %hf, ptr %first, ptr %new seq_cst seq_cst, align 8
  %ok = extractvalue { ptr, i1 } %pair, 1
  br i1 %ok, label %done, label %loop
done:
  %empty = icmp eq ptr %first, null
  ret i1 %empty
}

define ptr @ca_llist_del_first(ptr %head) noinline {
entry:
  %hf = getelementptr inbounds %struct.ca_head, ptr %head, i64 0, i32 0
  %entry0 = load volatile ptr, ptr %hf, align 8
  %isnull = icmp eq ptr %entry0, null
  br i1 %isnull, label %none, label %take
take:
  %np = getelementptr inbounds %struct.ca_node, ptr %entry0, i64 0, i32 0
  %next = load volatile ptr, ptr %np, align 8
  %pair = cmpxchg ptr %hf, ptr %entry0, ptr %next seq_cst seq_cst, align 8
  ret ptr %entry0
none:
  ret ptr null
}

define void @put_a() noinline {
  %f = getelementptr inbounds %struct.A, ptr @a, i64 0, i32 1
  store ptr @fa, ptr %f, align 8
  %r = call zeroext i1 @ca_llist_add2(ptr @a, ptr @HA)
  ret void
}

define void @put_b() noinline {
  %g = getelementptr inbounds %struct.B, ptr @b, i64 0, i32 1
  store ptr @fb, ptr %g, align 8
  %r = call zeroext i1 @ca_llist_add2(ptr @b, ptr @HB)
  ret void
}

define i32 @main() {
entry:
  call void @put_a()
  call void @put_b()
  %p0 = load ptr, ptr @HB, align 8
  br label %walk
walk:
  %p = phi ptr [ %p0, %entry ], [ %nx, %body ]
  %end = icmp eq ptr %p, null
  br i1 %end, label %out, label %body
body:
  %gp = getelementptr inbounds %struct.B, ptr %p, i64 0, i32 1
  %fn = load ptr, ptr %gp, align 8
  call void %fn()
  %nx = load ptr, ptr %p, align 8
  br label %walk
out:
  %d = call ptr @ca_llist_del_first(ptr @HA)
  ret i32 0
}
