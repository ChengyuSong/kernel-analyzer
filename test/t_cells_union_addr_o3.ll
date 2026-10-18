; // t_cells_union_addr_o3.ll — (C', Fable 2026-10-17) at -O3: t_cells_union_addr_typed.c
; // at -O3 with the stored address folded as LLVM folds binutils' at -O3
; // (coff_gc_sweep_symbol's `&_bfd_std_section[1]` reads `..., i64 1, i32 0`,
; // the address of the element's first member). Every object starting at the
; // address is tried, the S1 and its first member (a function pointer): the
; // S1 fits member a alone, so the store is typed a. A walk that ended at the
; // innermost level (the function pointer) would type nothing.
; // KAFLAGS: --cfl-rule-report=/dev/stdout
; // LOG: T ASSUMPTION a store over union E.u typed as member a by its value's debug type \(S1 \*, a constant address inside tab1\): wa: store ptr getelementptr inbounds \(\[2 x %struct.S1\], ptr @tab1, i64 0, i64 1, i32 0\)
; ModuleID = 't_cells_union_addr_o3.c'
source_filename = "t_cells_union_addr_o3.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.S1 = type { ptr }
%struct.S2 = type { ptr }
%struct.E = type { i32, %union.anon }
%union.anon = type { %struct.anon }
%struct.anon = type { ptr, ptr }

@tab1 = dso_local global [2 x %struct.S1] [%struct.S1 { ptr @f1 }, %struct.S1 { ptr @f1 }], align 16, !dbg !0
@tab2 = dso_local global [2 x %struct.S2] [%struct.S2 { ptr @f2 }, %struct.S2 { ptr @f2 }], align 16, !dbg !5

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable
define dso_local void @f1() #0 !dbg !28 {
  ret void, !dbg !29
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable
define dso_local void @f2() #0 !dbg !30 {
  ret void, !dbg !31
}

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(argmem: write) uwtable
define dso_local void @wa(ptr nocapture noundef writeonly %0) local_unnamed_addr #1 !dbg !32 {
  tail call void @llvm.dbg.value(metadata ptr %0, metadata !57, metadata !DIExpression()), !dbg !58
  %2 = getelementptr inbounds %struct.E, ptr %0, i64 0, i32 1, i32 0, i32 1, !dbg !59
  store ptr getelementptr inbounds ([2 x %struct.S1], ptr @tab1, i64 0, i64 1, i32 0), ptr %2, align 8, !dbg !60, !tbaa !61
  ret void, !dbg !64
}

; Function Attrs: mustprogress nofree noinline norecurse nosync nounwind willreturn memory(argmem: write) uwtable
define dso_local void @wb(ptr nocapture noundef writeonly %0, ptr noundef %1) local_unnamed_addr #1 !dbg !65 {
  tail call void @llvm.dbg.value(metadata ptr %0, metadata !69, metadata !DIExpression()), !dbg !71
  tail call void @llvm.dbg.value(metadata ptr %1, metadata !70, metadata !DIExpression()), !dbg !71
  %3 = getelementptr inbounds %struct.E, ptr %0, i64 0, i32 1, i32 0, i32 1, !dbg !72
  store ptr %1, ptr %3, align 8, !dbg !73, !tbaa !61
  ret void, !dbg !74
}

; Function Attrs: noinline nounwind uwtable
define dso_local void @use(ptr nocapture noundef readonly %0) local_unnamed_addr #2 !dbg !75 {
  tail call void @llvm.dbg.value(metadata ptr %0, metadata !77, metadata !DIExpression()), !dbg !79
  %2 = getelementptr inbounds %struct.E, ptr %0, i64 0, i32 1, i32 0, i32 1, !dbg !80
  %3 = load ptr, ptr %2, align 8, !dbg !80, !tbaa !61
  tail call void @llvm.dbg.value(metadata ptr %3, metadata !78, metadata !DIExpression()), !dbg !79
  %4 = load ptr, ptr %3, align 8, !dbg !81, !tbaa !82
  tail call void %4() #6, !dbg !85
  ret void, !dbg !86
}

; Function Attrs: nounwind uwtable
define dso_local noundef i32 @main(i32 noundef %0, ptr nocapture noundef readnone %1) local_unnamed_addr #3 !dbg !87 {
  tail call void @llvm.dbg.value(metadata i32 %0, metadata !94, metadata !DIExpression()), !dbg !97
  tail call void @llvm.dbg.value(metadata ptr %1, metadata !95, metadata !DIExpression()), !dbg !97
  %3 = tail call noalias dereferenceable_or_null(24) ptr @malloc(i64 noundef 24) #7, !dbg !98
  tail call void @llvm.dbg.value(metadata ptr %3, metadata !96, metadata !DIExpression()), !dbg !97
  %4 = icmp sgt i32 %0, 1, !dbg !99
  br i1 %4, label %5, label %6, !dbg !101

5:                                                ; preds = %2
  tail call void @wa(ptr noundef %3), !dbg !102
  br label %7, !dbg !102

6:                                                ; preds = %2
  tail call void @wb(ptr noundef %3, ptr noundef nonnull @tab2), !dbg !103
  br label %7

7:                                                ; preds = %6, %5
  tail call void @use(ptr noundef %3), !dbg !104
  ret i32 0, !dbg !105
}

; Function Attrs: mustprogress nofree nounwind willreturn allockind("alloc,uninitialized") allocsize(0) memory(inaccessiblemem: readwrite)
declare !dbg !106 noalias noundef ptr @malloc(i64 noundef) local_unnamed_addr #4

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare void @llvm.dbg.value(metadata, metadata, metadata) #5

attributes #0 = { mustprogress nofree norecurse nosync nounwind willreturn memory(none) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { mustprogress nofree noinline norecurse nosync nounwind willreturn memory(argmem: write) uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noinline nounwind uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { nounwind uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { mustprogress nofree nounwind willreturn allockind("alloc,uninitialized") allocsize(0) memory(inaccessiblemem: readwrite) "alloc-family"="malloc" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #5 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #6 = { nounwind }
attributes #7 = { nounwind allocsize(0) }

!llvm.dbg.cu = !{!2}
!llvm.module.flags = !{!20, !21, !22, !23, !24, !25, !26}
!llvm.ident = !{!27}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(name: "tab1", scope: !2, file: !3, line: 22, type: !16, isLocal: false, isDefinition: true)
!2 = distinct !DICompileUnit(language: DW_LANG_C11, file: !3, producer: "Ubuntu clang version 18.1.8 (++20240731025043+3b5b5c1ec4a3-1~exp1~20240731145144.92)", isOptimized: true, flags: "/usr/lib/llvm-18/bin/clang -g -O3 -emit-llvm -S t_cells_union_addr_o3.c -o /data/csong/tmp/cells/cpcase/t_cells_union_addr_o3.ll", runtimeVersion: 0, emissionKind: FullDebug, globals: !4, splitDebugInlining: false, nameTableKind: None)
!3 = !DIFile(filename: "t_cells_union_addr_o3.c", directory: "/data/csong/tmp/cells/wt-cp/test", checksumkind: CSK_MD5, checksum: "6e2b6fbba2dd31e2a3153a3ce935322d")
!4 = !{!0, !5}
!5 = !DIGlobalVariableExpression(var: !6, expr: !DIExpression())
!6 = distinct !DIGlobalVariable(name: "tab2", scope: !2, file: !3, line: 23, type: !7, isLocal: false, isDefinition: true)
!7 = !DICompositeType(tag: DW_TAG_array_type, baseType: !8, size: 128, elements: !14)
!8 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "S2", file: !3, line: 12, size: 64, elements: !9)
!9 = !{!10}
!10 = !DIDerivedType(tag: DW_TAG_member, name: "g", scope: !8, file: !3, line: 12, baseType: !11, size: 64)
!11 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !12, size: 64)
!12 = !DISubroutineType(types: !13)
!13 = !{null}
!14 = !{!15}
!15 = !DISubrange(count: 2)
!16 = !DICompositeType(tag: DW_TAG_array_type, baseType: !17, size: 128, elements: !14)
!17 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "S1", file: !3, line: 11, size: 64, elements: !18)
!18 = !{!19}
!19 = !DIDerivedType(tag: DW_TAG_member, name: "f", scope: !17, file: !3, line: 11, baseType: !11, size: 64)
!20 = !{i32 7, !"Dwarf Version", i32 5}
!21 = !{i32 2, !"Debug Info Version", i32 3}
!22 = !{i32 1, !"wchar_size", i32 4}
!23 = !{i32 8, !"PIC Level", i32 2}
!24 = !{i32 7, !"PIE Level", i32 2}
!25 = !{i32 7, !"uwtable", i32 2}
!26 = !{i32 7, !"debug-info-assignment-tracking", i1 true}
!27 = !{!"Ubuntu clang version 18.1.8 (++20240731025043+3b5b5c1ec4a3-1~exp1~20240731145144.92)"}
!28 = distinct !DISubprogram(name: "f1", scope: !3, file: !3, line: 20, type: !12, scopeLine: 20, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2)
!29 = !DILocation(line: 20, column: 16, scope: !28)
!30 = distinct !DISubprogram(name: "f2", scope: !3, file: !3, line: 21, type: !12, scopeLine: 21, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2)
!31 = !DILocation(line: 21, column: 16, scope: !30)
!32 = distinct !DISubprogram(name: "wa", scope: !3, file: !3, line: 24, type: !33, scopeLine: 24, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !56)
!33 = !DISubroutineType(types: !34)
!34 = !{null, !35}
!35 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !36, size: 64)
!36 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "E", file: !3, line: 13, size: 192, elements: !37)
!37 = !{!38, !40}
!38 = !DIDerivedType(tag: DW_TAG_member, name: "kind", scope: !36, file: !3, line: 14, baseType: !39, size: 32)
!39 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!40 = !DIDerivedType(tag: DW_TAG_member, name: "u", scope: !36, file: !3, line: 18, baseType: !41, size: 128, offset: 64)
!41 = distinct !DICompositeType(tag: DW_TAG_union_type, scope: !36, file: !3, line: 15, size: 128, elements: !42)
!42 = !{!43, !50}
!43 = !DIDerivedType(tag: DW_TAG_member, name: "a", scope: !41, file: !3, line: 16, baseType: !44, size: 128)
!44 = distinct !DICompositeType(tag: DW_TAG_structure_type, scope: !41, file: !3, line: 16, size: 128, elements: !45)
!45 = !{!46, !48}
!46 = !DIDerivedType(tag: DW_TAG_member, name: "next", scope: !44, file: !3, line: 16, baseType: !47, size: 64)
!47 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 64)
!48 = !DIDerivedType(tag: DW_TAG_member, name: "p", scope: !44, file: !3, line: 16, baseType: !49, size: 64, offset: 64)
!49 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !17, size: 64)
!50 = !DIDerivedType(tag: DW_TAG_member, name: "b", scope: !41, file: !3, line: 17, baseType: !51, size: 128)
!51 = distinct !DICompositeType(tag: DW_TAG_structure_type, scope: !41, file: !3, line: 17, size: 128, elements: !52)
!52 = !{!53, !54}
!53 = !DIDerivedType(tag: DW_TAG_member, name: "next", scope: !51, file: !3, line: 17, baseType: !47, size: 64)
!54 = !DIDerivedType(tag: DW_TAG_member, name: "q", scope: !51, file: !3, line: 17, baseType: !55, size: 64, offset: 64)
!55 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !8, size: 64)
!56 = !{!57}
!57 = !DILocalVariable(name: "e", arg: 1, scope: !32, file: !3, line: 24, type: !35)
!58 = !DILocation(line: 0, scope: !32)
!59 = !DILocation(line: 24, column: 57, scope: !32)
!60 = !DILocation(line: 24, column: 59, scope: !32)
!61 = !{!62, !62, i64 0}
!62 = !{!"omnipotent char", !63, i64 0}
!63 = !{!"Simple C/C++ TBAA"}
!64 = !DILocation(line: 24, column: 71, scope: !32)
!65 = distinct !DISubprogram(name: "wb", scope: !3, file: !3, line: 25, type: !66, scopeLine: 25, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !68)
!66 = !DISubroutineType(types: !67)
!67 = !{null, !35, !55}
!68 = !{!69, !70}
!69 = !DILocalVariable(name: "e", arg: 1, scope: !65, file: !3, line: 25, type: !35)
!70 = !DILocalVariable(name: "s", arg: 2, scope: !65, file: !3, line: 25, type: !55)
!71 = !DILocation(line: 0, scope: !65)
!72 = !DILocation(line: 25, column: 71, scope: !65)
!73 = !DILocation(line: 25, column: 73, scope: !65)
!74 = !DILocation(line: 25, column: 78, scope: !65)
!75 = distinct !DISubprogram(name: "use", scope: !3, file: !3, line: 26, type: !33, scopeLine: 26, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !76)
!76 = !{!77, !78}
!77 = !DILocalVariable(name: "e", arg: 1, scope: !75, file: !3, line: 26, type: !35)
!78 = !DILocalVariable(name: "s", scope: !75, file: !3, line: 27, type: !55)
!79 = !DILocation(line: 0, scope: !75)
!80 = !DILocation(line: 27, column: 25, scope: !75)
!81 = !DILocation(line: 28, column: 6, scope: !75)
!82 = !{!83, !84, i64 0}
!83 = !{!"S2", !84, i64 0}
!84 = !{!"any pointer", !62, i64 0}
!85 = !DILocation(line: 28, column: 3, scope: !75)
!86 = !DILocation(line: 29, column: 1, scope: !75)
!87 = distinct !DISubprogram(name: "main", scope: !3, file: !3, line: 30, type: !88, scopeLine: 30, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !93)
!88 = !DISubroutineType(types: !89)
!89 = !{!39, !39, !90}
!90 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !91, size: 64)
!91 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !92, size: 64)
!92 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!93 = !{!94, !95, !96}
!94 = !DILocalVariable(name: "argc", arg: 1, scope: !87, file: !3, line: 30, type: !39)
!95 = !DILocalVariable(name: "argv", arg: 2, scope: !87, file: !3, line: 30, type: !90)
!96 = !DILocalVariable(name: "e", scope: !87, file: !3, line: 31, type: !35)
!97 = !DILocation(line: 0, scope: !87)
!98 = !DILocation(line: 31, column: 17, scope: !87)
!99 = !DILocation(line: 33, column: 12, scope: !100)
!100 = distinct !DILexicalBlock(scope: !87, file: !3, line: 33, column: 7)
!101 = !DILocation(line: 33, column: 7, scope: !87)
!102 = !DILocation(line: 33, column: 17, scope: !100)
!103 = !DILocation(line: 33, column: 29, scope: !100)
!104 = !DILocation(line: 34, column: 3, scope: !87)
!105 = !DILocation(line: 35, column: 3, scope: !87)
!106 = !DISubprogram(name: "malloc", scope: !107, file: !107, line: 672, type: !108, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized)
!107 = !DIFile(filename: "/usr/include/stdlib.h", directory: "", checksumkind: CSK_MD5, checksum: "7fa2ecb2348a66f8b44ab9a15abd0b72")
!108 = !DISubroutineType(types: !109)
!109 = !{!47, !110}
!110 = !DIDerivedType(tag: DW_TAG_typedef, name: "size_t", file: !111, line: 18, baseType: !112)
!111 = !DIFile(filename: "/usr/lib/llvm-18/lib/clang/18/include/__stddef_size_t.h", directory: "", checksumkind: CSK_MD5, checksum: "2c44e821a2b1951cde2eb0fb2e656867")
!112 = !DIBasicType(name: "unsigned long", size: 64, encoding: DW_ATE_unsigned)
