; t_cells_carvehdr.ll -- A2' form (3) (Fable 2026-10-20): a new small
; chunk's header carve c = chunk + 16 followed by H := c + %sz is a piece of
; %sz, not chunk - 16 (4048): the rest of the chunk is the later carves'
; space. The large path malloc(%sz + 16) + 16 is %sz as before; the return
; phi is the before-bump carve (form 2). p_alloc(24) is 24 bytes: struct.base
; relabels to struct.derived.
%struct.objalloc = type { ptr, i32, ptr }
%struct.objalloc_chunk = type { ptr, ptr }
%struct.base = type { ptr, i64 }
%struct.derived = type { %struct.base, ptr }

@pool = internal global %struct.objalloc zeroinitializer, align 8

declare noalias ptr @malloc(i64)

define internal ptr @p_alloc(i64 %n) {
entry:
  %neg = icmp slt i64 %n, 0
  br i1 %neg, label %fail, label %start

start:
  %o = load ptr, ptr @pool.ptr, align 8
  %isz = icmp eq i64 %n, 0
  %a7 = add nuw i64 %n, 7
  %r8 = and i64 %a7, -8
  %sz = select i1 %isz, i64 8, i64 %r8
  %zero = icmp eq i64 %sz, 0
  %spp = getelementptr inbounds %struct.objalloc, ptr %o, i64 0, i32 1
  %space = load i32, ptr %spp, align 8
  br i1 %zero, label %fail, label %nz





nz:
  %space64 = zext i32 %space to i64
  %nofit = icmp ugt i64 %sz, %space64
  br i1 %nofit, label %new, label %bump

new:
  %big = icmp ugt i64 %sz, 511
  br i1 %big, label %bignew, label %smallnew

bignew:
  %bsz = add i64 %sz, 16
  %bc = tail call noalias ptr @malloc(i64 %bsz)
  %bcnull = icmp eq ptr %bc, null
  br i1 %bcnull, label %fail, label %binit

binit:
  %chp3 = getelementptr inbounds %struct.objalloc, ptr %o, i64 0, i32 2
  %old3 = load ptr, ptr %chp3, align 8
  %bn = getelementptr inbounds %struct.objalloc_chunk, ptr %bc, i64 0, i32 0
  store ptr %old3, ptr %bn, align 8
  %cpp3 = getelementptr inbounds %struct.objalloc, ptr %o, i64 0, i32 0
  %cur3 = load ptr, ptr %cpp3, align 8
  %bcp = getelementptr inbounds %struct.objalloc_chunk, ptr %bc, i64 0, i32 1
  store ptr %cur3, ptr %bcp, align 8
  store ptr %bc, ptr %chp3, align 8
  %bret = getelementptr inbounds i8, ptr %bc, i64 16
  br label %done

smallnew:
  %sc = tail call noalias ptr @malloc(i64 4064)
  %scnull = icmp eq ptr %sc, null
  br i1 %scnull, label %fail, label %sinit

sinit:
  %chp4 = getelementptr inbounds %struct.objalloc, ptr %o, i64 0, i32 2
  %old4 = load ptr, ptr %chp4, align 8
  %sn = getelementptr inbounds %struct.objalloc_chunk, ptr %sc, i64 0, i32 0
  store ptr %old4, ptr %sn, align 8
  %scp = getelementptr inbounds %struct.objalloc_chunk, ptr %sc, i64 0, i32 1
  store ptr null, ptr %scp, align 8
  %sret = getelementptr inbounds i8, ptr %sc, i64 16
  %cpp4 = getelementptr inbounds %struct.objalloc, ptr %o, i64 0, i32 0
  store ptr %sc, ptr %chp4, align 8
  %snext = getelementptr inbounds i8, ptr %sret, i64 %sz
  store ptr %snext, ptr %cpp4, align 8
  %st = trunc i64 %sz to i32
  %ssp = sub nuw nsw i32 4048, %st
  store i32 %ssp, ptr %spp, align 8
  br label %done

bump:
  %cpp5 = getelementptr inbounds %struct.objalloc, ptr %o, i64 0, i32 0
  %cur5 = load ptr, ptr %cpp5, align 8
  %next5 = getelementptr inbounds i8, ptr %cur5, i64 %sz
  store ptr %next5, ptr %cpp5, align 8
  %t5 = trunc i64 %sz to i32
  %sp5 = sub i32 %space, %t5
  br label %bumped

bumped:
  %spn = phi i32 [ %sp5, %bump ]
  %res = phi ptr [ %cur5, %bump ]
  store i32 %spn, ptr %spp, align 8
  %rnull = icmp eq ptr %res, null
  br i1 %rnull, label %fail, label %done

fail:
  br label %done

done:
  %r = phi ptr [ %res, %bumped ], [ null, %fail ], [ %sret, %sinit ], [ %bret, %binit ]
  ret ptr %r
}

@pool.ptr = internal global ptr @pool, align 8

define void @afn() {
  ret void
}
define void @bfn() {
  ret void
}

define i32 @main() {
entry:
  %b = call ptr @p_alloc(i64 24)
  %f = getelementptr inbounds %struct.base, ptr %b, i64 0, i32 0
  store ptr @afn, ptr %f, align 8
  %gp = getelementptr inbounds i8, ptr %b, i64 16
  store ptr @bfn, ptr %gp, align 8
  %fl = load ptr, ptr %f, align 8
  call void %fl()
  %gl = load ptr, ptr %gp, align 8
  call void %gl()
  ret i32 0
}

define void @use_derived(ptr %d) {
  %g = getelementptr inbounds %struct.derived, ptr %d, i64 0, i32 1
  store ptr null, ptr %g, align 8
  ret void
}
; LOG: size terms \(A2'\): 0 carves by "n, K when n == 0", 1 carve phis by their carve term, 1 header carves by the store H := c \+ n
; LOG: 1 relabeled to the container their size names
