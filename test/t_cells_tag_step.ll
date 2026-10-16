; // t_cells_tag_step.ll — a GEP whose leading index is not 0 is a byte step
; // (fc2f459), named only by its TBAA tag (Fable 2026-10-16): -O3 writes
; // elf_link_hash_entry's fields as steps over its first member's type
; // (`gep %struct.bfd_link_hash_entry, %h, i64 1, i32 2, ...` is
; // elf_link_hash_entry+96, past the 56 bytes of bfd_link_hash_entry), and
; // TaggedFields named them by the step's own struct, past its layout
; // ("struct.bfd_link_hash_entry+96", a field that does not exist). Here
; // outer.type at +16 is written as `gep %struct.inner, %o, i64 1, i32 0`
; // without a tag: unnamed, counted.
; // LOG: a byte step\): 0 named by their TBAA tag, 1 unnamed; 1 of them at constant indices \(the GEP alone used to name them\), 1 of those past the layout
%struct.inner = type { i64, i64 }
%struct.outer = type { %struct.inner, i32, ptr }

define void @settype(ptr %o, i32 %t) {
  %p = getelementptr inbounds %struct.inner, ptr %o, i64 1, i32 0
  store i32 %t, ptr %p, align 8
  ret void
}

define i32 @main() {
  %o = alloca %struct.outer, align 8
  call void @settype(ptr %o, i32 1)
  ret i32 0
}
