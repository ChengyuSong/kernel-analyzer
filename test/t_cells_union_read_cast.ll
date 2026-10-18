; // t_cells_union_read_cast.ll — R1 (Fable 2026-10-17, a bug fix): the census
; // types a read of a union by its loaded value's uses; the typed IR that
; // clang -O0 upgraded to opaque pointers keeps a no-op `bitcast ptr %v to
; // ptr` between the load and its store into the declared local (nm-new.bc's
; // `%195 = bitcast ptr %194 to ptr` at _bfd_elf_merge_symbol's chase). The
; // walk now sees through it: use's read of u.b.q is typed b by its local
; // (an UNCHECKED read of b). Before it was untyped, and read the whole slot.
; // LOG: UnionKeys: 1 reads typed through a no-op cast of the loaded value
; // LOG: UNCHECKED read of b at use
; ModuleID = 't_cells_union_read_cast.c'
source_filename = "t_cells_union_read_cast.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.S1 = type { ptr }
%struct.S2 = type { ptr }
%struct.E = type { i32, %union.anon }
%union.anon = type { %struct.anon }
%struct.anon = type { ptr, ptr }
%struct.anon.0 = type { ptr, ptr }

@s1 = dso_local global %struct.S1 { ptr @f1 }, align 8, !dbg !0
@s2 = dso_local global %struct.S2 { ptr @f2 }, align 8, !dbg !5

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @f1() #0 !dbg !24 {
  ret void, !dbg !25
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @f2() #0 !dbg !26 {
  ret void, !dbg !27
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @wa(ptr noundef %0, ptr noundef %1) #0 !dbg !28 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
  call void @llvm.dbg.declare(metadata ptr %3, metadata !53, metadata !DIExpression()), !dbg !54
  store ptr %1, ptr %4, align 8
  call void @llvm.dbg.declare(metadata ptr %4, metadata !55, metadata !DIExpression()), !dbg !56
  %5 = load ptr, ptr %4, align 8, !dbg !57
  %6 = load ptr, ptr %3, align 8, !dbg !58
  %7 = getelementptr inbounds %struct.E, ptr %6, i32 0, i32 1, !dbg !59
  %8 = getelementptr inbounds %struct.anon, ptr %7, i32 0, i32 1, !dbg !60
  store ptr %5, ptr %8, align 8, !dbg !61
  ret void, !dbg !62
}

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @wb(ptr noundef %0, ptr noundef %1) #0 !dbg !63 {
  %3 = alloca ptr, align 8
  %4 = alloca ptr, align 8
  store ptr %0, ptr %3, align 8
  call void @llvm.dbg.declare(metadata ptr %3, metadata !66, metadata !DIExpression()), !dbg !67
  store ptr %1, ptr %4, align 8
  call void @llvm.dbg.declare(metadata ptr %4, metadata !68, metadata !DIExpression()), !dbg !69
  %5 = load ptr, ptr %4, align 8, !dbg !70
  %6 = load ptr, ptr %3, align 8, !dbg !71
  %7 = getelementptr inbounds %struct.E, ptr %6, i32 0, i32 1, !dbg !72
  %8 = getelementptr inbounds %struct.anon.0, ptr %7, i32 0, i32 1, !dbg !73
  store ptr %5, ptr %8, align 8, !dbg !74
  ret void, !dbg !75
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @use(ptr noundef %0) #0 !dbg !76 {
  %2 = alloca ptr, align 8
  %3 = alloca ptr, align 8
  store ptr %0, ptr %2, align 8
  call void @llvm.dbg.declare(metadata ptr %2, metadata !79, metadata !DIExpression()), !dbg !80
  call void @llvm.dbg.declare(metadata ptr %3, metadata !81, metadata !DIExpression()), !dbg !82
  %4 = load ptr, ptr %2, align 8, !dbg !83
  %5 = getelementptr inbounds %struct.E, ptr %4, i32 0, i32 1, !dbg !84
  %6 = getelementptr inbounds %struct.anon.0, ptr %5, i32 0, i32 1, !dbg !85
  %7 = load ptr, ptr %6, align 8, !dbg !85
  %cast7 = bitcast ptr %7 to ptr, !dbg !85
  store ptr %cast7, ptr %3, align 8, !dbg !82
  %8 = load ptr, ptr %3, align 8, !dbg !86
  %9 = getelementptr inbounds %struct.S2, ptr %8, i32 0, i32 0, !dbg !87
  %10 = load ptr, ptr %9, align 8, !dbg !87
  call void %10(), !dbg !86
  ret void, !dbg !88
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main(i32 noundef %0, ptr noundef %1) #0 !dbg !89 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca ptr, align 8
  %6 = alloca ptr, align 8
  store i32 0, ptr %3, align 4
  store i32 %0, ptr %4, align 4
  call void @llvm.dbg.declare(metadata ptr %4, metadata !95, metadata !DIExpression()), !dbg !96
  store ptr %1, ptr %5, align 8
  call void @llvm.dbg.declare(metadata ptr %5, metadata !97, metadata !DIExpression()), !dbg !98
  call void @llvm.dbg.declare(metadata ptr %6, metadata !99, metadata !DIExpression()), !dbg !100
  %7 = call noalias ptr @malloc(i64 noundef 24) #3, !dbg !101
  store ptr %7, ptr %6, align 8, !dbg !100
  %8 = load ptr, ptr %5, align 8, !dbg !102
  %9 = load i32, ptr %4, align 4, !dbg !103
  %10 = icmp sgt i32 %9, 1, !dbg !105
  br i1 %10, label %11, label %13, !dbg !106

11:                                               ; preds = %2
  %12 = load ptr, ptr %6, align 8, !dbg !107
  call void @wa(ptr noundef %12, ptr noundef @s1), !dbg !108
  br label %15, !dbg !108

13:                                               ; preds = %2
  %14 = load ptr, ptr %6, align 8, !dbg !109
  call void @wb(ptr noundef %14, ptr noundef @s2), !dbg !110
  br label %15

15:                                               ; preds = %13, %11
  %16 = load ptr, ptr %6, align 8, !dbg !111
  call void @use(ptr noundef %16), !dbg !112
  ret i32 0, !dbg !113
}

; Function Attrs: nounwind allocsize(0)
declare noalias ptr @malloc(i64 noundef) #2

attributes #0 = { noinline nounwind optnone uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #2 = { nounwind allocsize(0) "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { nounwind allocsize(0) }

!llvm.dbg.cu = !{!2}
!llvm.module.flags = !{!16, !17, !18, !19, !20, !21, !22}
!llvm.ident = !{!23}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(name: "s1", scope: !2, file: !3, line: 13, type: !13, isLocal: false, isDefinition: true)
!2 = distinct !DICompileUnit(language: DW_LANG_C11, file: !3, producer: "Ubuntu clang version 18.1.8 (++20240731025043+3b5b5c1ec4a3-1~exp1~20240731145144.92)", isOptimized: false, flags: "/usr/lib/llvm-18/bin/clang -g -O0 -emit-llvm -S t_cells_union_read_cast.c -o base.ll", runtimeVersion: 0, emissionKind: FullDebug, globals: !4, splitDebugInlining: false, nameTableKind: None)
!3 = !DIFile(filename: "t_cells_union_read_cast.c", directory: "/data/csong/tmp/cells/cpcase/r1", checksumkind: CSK_MD5, checksum: "eebb5b24613eb3db9b8737940a698a57")
!4 = !{!0, !5}
!5 = !DIGlobalVariableExpression(var: !6, expr: !DIExpression())
!6 = distinct !DIGlobalVariable(name: "s2", scope: !2, file: !3, line: 14, type: !7, isLocal: false, isDefinition: true)
!7 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "S2", file: !3, line: 3, size: 64, elements: !8)
!8 = !{!9}
!9 = !DIDerivedType(tag: DW_TAG_member, name: "g", scope: !7, file: !3, line: 3, baseType: !10, size: 64)
!10 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !11, size: 64)
!11 = !DISubroutineType(types: !12)
!12 = !{null}
!13 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "S1", file: !3, line: 2, size: 64, elements: !14)
!14 = !{!15}
!15 = !DIDerivedType(tag: DW_TAG_member, name: "f", scope: !13, file: !3, line: 2, baseType: !10, size: 64)
!16 = !{i32 7, !"Dwarf Version", i32 5}
!17 = !{i32 2, !"Debug Info Version", i32 3}
!18 = !{i32 1, !"wchar_size", i32 4}
!19 = !{i32 8, !"PIC Level", i32 2}
!20 = !{i32 7, !"PIE Level", i32 2}
!21 = !{i32 7, !"uwtable", i32 2}
!22 = !{i32 7, !"frame-pointer", i32 2}
!23 = !{!"Ubuntu clang version 18.1.8 (++20240731025043+3b5b5c1ec4a3-1~exp1~20240731145144.92)"}
!24 = distinct !DISubprogram(name: "f1", scope: !3, file: !3, line: 11, type: !11, scopeLine: 11, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !2)
!25 = !DILocation(line: 11, column: 16, scope: !24)
!26 = distinct !DISubprogram(name: "f2", scope: !3, file: !3, line: 12, type: !11, scopeLine: 12, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !2)
!27 = !DILocation(line: 12, column: 16, scope: !26)
!28 = distinct !DISubprogram(name: "wa", scope: !3, file: !3, line: 15, type: !29, scopeLine: 15, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !2, retainedNodes: !52)
!29 = !DISubroutineType(types: !30)
!30 = !{null, !31, !45}
!31 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !32, size: 64)
!32 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "E", file: !3, line: 4, size: 192, elements: !33)
!33 = !{!34, !36}
!34 = !DIDerivedType(tag: DW_TAG_member, name: "kind", scope: !32, file: !3, line: 5, baseType: !35, size: 32)
!35 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!36 = !DIDerivedType(tag: DW_TAG_member, name: "u", scope: !32, file: !3, line: 9, baseType: !37, size: 128, offset: 64)
!37 = distinct !DICompositeType(tag: DW_TAG_union_type, scope: !32, file: !3, line: 6, size: 128, elements: !38)
!38 = !{!39, !46}
!39 = !DIDerivedType(tag: DW_TAG_member, name: "a", scope: !37, file: !3, line: 7, baseType: !40, size: 128)
!40 = distinct !DICompositeType(tag: DW_TAG_structure_type, scope: !37, file: !3, line: 7, size: 128, elements: !41)
!41 = !{!42, !44}
!42 = !DIDerivedType(tag: DW_TAG_member, name: "n", scope: !40, file: !3, line: 7, baseType: !43, size: 64)
!43 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 64)
!44 = !DIDerivedType(tag: DW_TAG_member, name: "p", scope: !40, file: !3, line: 7, baseType: !45, size: 64, offset: 64)
!45 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !13, size: 64)
!46 = !DIDerivedType(tag: DW_TAG_member, name: "b", scope: !37, file: !3, line: 8, baseType: !47, size: 128)
!47 = distinct !DICompositeType(tag: DW_TAG_structure_type, scope: !37, file: !3, line: 8, size: 128, elements: !48)
!48 = !{!49, !50}
!49 = !DIDerivedType(tag: DW_TAG_member, name: "n", scope: !47, file: !3, line: 8, baseType: !43, size: 64)
!50 = !DIDerivedType(tag: DW_TAG_member, name: "q", scope: !47, file: !3, line: 8, baseType: !51, size: 64, offset: 64)
!51 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !7, size: 64)
!52 = !{}
!53 = !DILocalVariable(name: "e", arg: 1, scope: !28, file: !3, line: 15, type: !31)
!54 = !DILocation(line: 15, column: 45, scope: !28)
!55 = !DILocalVariable(name: "s", arg: 2, scope: !28, file: !3, line: 15, type: !45)
!56 = !DILocation(line: 15, column: 59, scope: !28)
!57 = !DILocation(line: 15, column: 75, scope: !28)
!58 = !DILocation(line: 15, column: 64, scope: !28)
!59 = !DILocation(line: 15, column: 67, scope: !28)
!60 = !DILocation(line: 15, column: 71, scope: !28)
!61 = !DILocation(line: 15, column: 73, scope: !28)
!62 = !DILocation(line: 15, column: 78, scope: !28)
!63 = distinct !DISubprogram(name: "wb", scope: !3, file: !3, line: 16, type: !64, scopeLine: 16, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !2, retainedNodes: !52)
!64 = !DISubroutineType(types: !65)
!65 = !{null, !31, !51}
!66 = !DILocalVariable(name: "e", arg: 1, scope: !63, file: !3, line: 16, type: !31)
!67 = !DILocation(line: 16, column: 45, scope: !63)
!68 = !DILocalVariable(name: "s", arg: 2, scope: !63, file: !3, line: 16, type: !51)
!69 = !DILocation(line: 16, column: 59, scope: !63)
!70 = !DILocation(line: 16, column: 75, scope: !63)
!71 = !DILocation(line: 16, column: 64, scope: !63)
!72 = !DILocation(line: 16, column: 67, scope: !63)
!73 = !DILocation(line: 16, column: 71, scope: !63)
!74 = !DILocation(line: 16, column: 73, scope: !63)
!75 = !DILocation(line: 16, column: 78, scope: !63)
!76 = distinct !DISubprogram(name: "use", scope: !3, file: !3, line: 17, type: !77, scopeLine: 17, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !2, retainedNodes: !52)
!77 = !DISubroutineType(types: !78)
!78 = !{null, !31}
!79 = !DILocalVariable(name: "e", arg: 1, scope: !76, file: !3, line: 17, type: !31)
!80 = !DILocation(line: 17, column: 46, scope: !76)
!81 = !DILocalVariable(name: "s", scope: !76, file: !3, line: 18, type: !51)
!82 = !DILocation(line: 18, column: 14, scope: !76)
!83 = !DILocation(line: 18, column: 18, scope: !76)
!84 = !DILocation(line: 18, column: 21, scope: !76)
!85 = !DILocation(line: 18, column: 25, scope: !76)
!86 = !DILocation(line: 19, column: 3, scope: !76)
!87 = !DILocation(line: 19, column: 6, scope: !76)
!88 = !DILocation(line: 20, column: 1, scope: !76)
!89 = distinct !DISubprogram(name: "main", scope: !3, file: !3, line: 21, type: !90, scopeLine: 21, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !2, retainedNodes: !52)
!90 = !DISubroutineType(types: !91)
!91 = !{!35, !35, !92}
!92 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !93, size: 64)
!93 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !94, size: 64)
!94 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!95 = !DILocalVariable(name: "argc", arg: 1, scope: !89, file: !3, line: 21, type: !35)
!96 = !DILocation(line: 21, column: 14, scope: !89)
!97 = !DILocalVariable(name: "argv", arg: 2, scope: !89, file: !3, line: 21, type: !92)
!98 = !DILocation(line: 21, column: 27, scope: !89)
!99 = !DILocalVariable(name: "e", scope: !89, file: !3, line: 22, type: !31)
!100 = !DILocation(line: 22, column: 13, scope: !89)
!101 = !DILocation(line: 22, column: 17, scope: !89)
!102 = !DILocation(line: 23, column: 9, scope: !89)
!103 = !DILocation(line: 24, column: 7, scope: !104)
!104 = distinct !DILexicalBlock(scope: !89, file: !3, line: 24, column: 7)
!105 = !DILocation(line: 24, column: 12, scope: !104)
!106 = !DILocation(line: 24, column: 7, scope: !89)
!107 = !DILocation(line: 24, column: 20, scope: !104)
!108 = !DILocation(line: 24, column: 17, scope: !104)
!109 = !DILocation(line: 24, column: 37, scope: !104)
!110 = !DILocation(line: 24, column: 34, scope: !104)
!111 = !DILocation(line: 25, column: 7, scope: !89)
!112 = !DILocation(line: 25, column: 3, scope: !89)
!113 = !DILocation(line: 26, column: 3, scope: !89)
