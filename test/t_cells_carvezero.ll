; t_cells_carvezero.ll -- A2' form (1) (Fable 2026-10-20): a pool's two
; bumps, %sz = select(n == 0, 8, round8(n)) and a constant 8 only on the
; true edge of %sz == 0, read as "%sz, 8 when %sz == 0"; the return phi is
; the before-bump carve (form 2), the zero path's new chunk is H := chunk +
; 24 (form 3, constant). p_alloc(24) is 24 bytes: struct.base relabels to
; struct.derived.
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
  br i1 %zero, label %z, label %nz

z:
  %zfit = icmp ult i32 %space, 8
  br i1 %zfit, label %znew, label %zbump

zbump:
  %cpp = getelementptr inbounds %struct.objalloc, ptr %o, i64 0, i32 0
  %cur = load ptr, ptr %cpp, align 8
  %cur8 = getelementptr inbounds i8, ptr %cur, i64 8
  store ptr %cur8, ptr %cpp, align 8
  %sp8 = add i32 %space, -8
  br label %bumped

znew:
  %zc = tail call noalias ptr @malloc(i64 4064)
  %zcnull = icmp eq ptr %zc, null
  br i1 %zcnull, label %fail, label %zinit

zinit:
  %chp = getelementptr inbounds %struct.objalloc, ptr %o, i64 0, i32 2
  %old = load ptr, ptr %chp, align 8
  %zn = getelementptr inbounds %struct.objalloc_chunk, ptr %zc, i64 0, i32 0
  store ptr %old, ptr %zn, align 8
  %zret = getelementptr inbounds i8, ptr %zc, i64 16
  %cpp2 = getelementptr inbounds %struct.objalloc, ptr %o, i64 0, i32 0
  store ptr %zc, ptr %chp, align 8
  %znext = getelementptr inbounds i8, ptr %zc, i64 24
  store ptr %znext, ptr %cpp2, align 8
  store i32 4040, ptr %spp, align 8
  br label %done

nz:
  %space64 = zext i32 %space to i64
  %nofit = icmp ugt i64 %sz, %space64
  br i1 %nofit, label %fail, label %bump






bump:
  %cpp5 = getelementptr inbounds %struct.objalloc, ptr %o, i64 0, i32 0
  %cur5 = load ptr, ptr %cpp5, align 8
  %next5 = getelementptr inbounds i8, ptr %cur5, i64 %sz
  store ptr %next5, ptr %cpp5, align 8
  %t5 = trunc i64 %sz to i32
  %sp5 = sub i32 %space, %t5
  br label %bumped

bumped:
  %spn = phi i32 [ %sp8, %zbump ], [ %sp5, %bump ]
  %res = phi ptr [ %cur, %zbump ], [ %cur5, %bump ]
  store i32 %spn, ptr %spp, align 8
  %rnull = icmp eq ptr %res, null
  br i1 %rnull, label %fail, label %done

fail:
  br label %done

done:
  %r = phi ptr [ %res, %bumped ], [ null, %fail ], [ %zret, %zinit ]
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
; LOG: size terms \(A2'\): 1 carves by "n, K when n == 0", 1 carve phis
; LOG: 1 relabeled to the container their size names
