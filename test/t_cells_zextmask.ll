; t_cells_zextmask.ll -- A2' form (4) (Fable 2026-10-20): -O3
; bfd_hash_allocate rounds an unsigned int size as
; (zext_i32(n == 0 ? 1 : n) + 7) & 0x1fffffff8, not & -8: the sum is below
; 2^33 (2^32 - 1 + 7), so the mask 2^33 - 8 is the same as -8. h_alloc(24)
; is 24 bytes: struct.base relabels to struct.derived.
%struct.base = type { ptr, i64 }
%struct.derived = type { %struct.base, ptr }

declare noalias ptr @malloc(i64)

define internal ptr @h_alloc(i32 %n) {
  %z = icmp eq i32 %n, 0
  %s = select i1 %z, i32 1, i32 %n
  %w = zext i32 %s to i64
  %a = add nuw nsw i64 %w, 7
  %r = and i64 %a, 8589934584
  %p = tail call noalias ptr @malloc(i64 %r)
  ret ptr %p
}

define void @afn() {
  ret void
}

define i32 @main() {
entry:
  %b = call ptr @h_alloc(i32 24)
  %f = getelementptr inbounds %struct.base, ptr %b, i64 0, i32 0
  store ptr @afn, ptr %f, align 8
  %gp = getelementptr inbounds i8, ptr %b, i64 16
  store ptr @afn, ptr %gp, align 8
  %fl = load ptr, ptr %f, align 8
  call void %fl()
  ret i32 0
}

define void @use_derived(ptr %d) {
  %g = getelementptr inbounds %struct.derived, ptr %d, i64 0, i32 1
  store ptr null, ptr %g, align 8
  ret void
}
; LOG: size terms \(A2'\): .* 1 zext masks read as -al; 0 fresh functions still unknown
; LOG: 1 relabeled to the container their size names
