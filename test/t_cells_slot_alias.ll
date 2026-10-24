; // t_cells_slot_alias.ll — rule S (Fable 2026-10-24): a summarized slot
; // may be written through an alias of its address (a zero-offset GEP, a
; // pointer cast); the reaching-store walk must see those writes. g is
; // stored directly, then f through the zero GEP, then the slot is loaded:
; // only the store of f reaches the load. A walk that missed the alias
; // write would answer [g] alone (unsound); the all-to-all product before
; // S answered [f, g].
; // Assembled as written (clang never emits a zero GEP of an alloca at -O0).
; // CHECK: f CHECK-NOT: g
; // LOG: Slots: cut main %slot: 2 writes x 1 loads = 2 pairs -> 1 reaching
define void @f() {
  ret void
}
define void @g() {
  ret void
}
define i32 @main() !dbg !6 {
  %slot = alloca ptr, align 8
  store ptr @g, ptr %slot, align 8
  %alias = getelementptr inbounds ptr, ptr %slot, i64 0
  store ptr @f, ptr %alias, align 8
  %v = load ptr, ptr %slot, align 8
  call void %v(), !dbg !9
  ret i32 0
}
!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3, !4}
!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "hand", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug)
!1 = !DIFile(filename: "t_cells_slot_alias.ll", directory: ".")
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 7, !"Dwarf Version", i32 5}
!6 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 10, type: !7, unit: !0, spFlags: DISPFlagDefinition)
!7 = !DISubroutineType(types: !8)
!8 = !{null}
!9 = !DILocation(line: 9, column: 3, scope: !6)
