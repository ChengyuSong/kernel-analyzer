; // t_cells_anon_relinked.ll — t_cells_anon_label.c as the IR linker leaves it:
; // a colliding anonymous type is renamed again (`%struct.anon.9.932` in
; // nm-new.bc: 68 of its 107 anonymous types at -O0). Every numeric suffix
; // goes before the name is judged anonymous; at 7bb102a only the last one
; // went ("struct.anon.3"), so both globals stayed labeled.
; // LOG: anonymous structs label nothing: 2 globals and stack objects unlabeled
; // LOG: object A \[unlabeled, 16 B\]
; // NOLOG: \[struct\.anon
source_filename = "t_cells_anon_label.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.anon.3.17 = type { ptr, i32 }
%struct.anon.0.21 = type { ptr, i64 }

@A = internal global %struct.anon.3.17 zeroinitializer, align 8, !dbg !0
@B = internal global %struct.anon.0.21 zeroinitializer, align 8, !dbg !5
@sink = dso_local global ptr null, align 8, !dbg !15

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @fa() #0 !dbg !32 {
  ret void, !dbg !33
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @fb() #0 !dbg !34 {
  ret void, !dbg !35
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main(i32 noundef %0, ptr noundef %1) #0 !dbg !36 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca ptr, align 8
  store i32 0, ptr %3, align 4
  store i32 %0, ptr %4, align 4
  call void @llvm.dbg.declare(metadata ptr %4, metadata !43, metadata !DIExpression()), !dbg !44
  store ptr %1, ptr %5, align 8
  call void @llvm.dbg.declare(metadata ptr %5, metadata !45, metadata !DIExpression()), !dbg !46
  %6 = load ptr, ptr %5, align 8, !dbg !47
  store ptr @fa, ptr @A, align 8, !dbg !48
  store ptr @fb, ptr @B, align 8, !dbg !49
  %7 = load i32, ptr %4, align 4, !dbg !50
  %8 = icmp ne i32 %7, 0, !dbg !50
  %9 = zext i1 %8 to i64, !dbg !50
  %10 = select i1 %8, ptr @A, ptr @B, !dbg !50
  store volatile ptr %10, ptr @sink, align 8, !dbg !51
  %11 = load ptr, ptr @A, align 8, !dbg !52
  call void %11(), !dbg !53
  ret i32 0, !dbg !54
}

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

attributes #0 = { noinline nounwind optnone uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }

!llvm.dbg.cu = !{!2}
!llvm.module.flags = !{!24, !25, !26, !27, !28, !29, !30}
!llvm.ident = !{!31}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(name: "A", scope: !2, file: !3, line: 15, type: !19, isLocal: true, isDefinition: true)
!2 = distinct !DICompileUnit(language: DW_LANG_C11, file: !3, producer: "Ubuntu clang version 18.1.8 (++20240731025043+3b5b5c1ec4a3-1~exp1~20240731145144.92)", isOptimized: false, flags: "/usr/lib/llvm-18/bin/clang -g -O0 -S -emit-llvm t_cells_anon_label.c -o /tmp/claude-1000/-home-csong-project-kanalyzer/b3817a09-772b-4446-a618-9b8522b44a39/scratchpad/anon_label.ll", runtimeVersion: 0, emissionKind: FullDebug, globals: !4, splitDebugInlining: false, nameTableKind: None)
!3 = !DIFile(filename: "t_cells_anon_label.c", directory: "/data/csong/tmp/cells/wt-r10/test", checksumkind: CSK_MD5, checksum: "3b05714cef5cdac70ec1e2966e71a1ae")
!4 = !{!0, !5, !15}
!5 = !DIGlobalVariableExpression(var: !6, expr: !DIExpression())
!6 = distinct !DIGlobalVariable(name: "B", scope: !2, file: !3, line: 19, type: !7, isLocal: true, isDefinition: true)
!7 = distinct !DICompositeType(tag: DW_TAG_structure_type, file: !3, line: 16, size: 128, elements: !8)
!8 = !{!9, !13}
!9 = !DIDerivedType(tag: DW_TAG_member, name: "f", scope: !7, file: !3, line: 17, baseType: !10, size: 64)
!10 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !11, size: 64)
!11 = !DISubroutineType(types: !12)
!12 = !{null}
!13 = !DIDerivedType(tag: DW_TAG_member, name: "y", scope: !7, file: !3, line: 18, baseType: !14, size: 64, offset: 64)
!14 = !DIBasicType(name: "long", size: 64, encoding: DW_ATE_signed)
!15 = !DIGlobalVariableExpression(var: !16, expr: !DIExpression())
!16 = distinct !DIGlobalVariable(name: "sink", scope: !2, file: !3, line: 22, type: !17, isLocal: false, isDefinition: true)
!17 = !DIDerivedType(tag: DW_TAG_volatile_type, baseType: !18)
!18 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !10, size: 64)
!19 = distinct !DICompositeType(tag: DW_TAG_structure_type, file: !3, line: 12, size: 128, elements: !20)
!20 = !{!21, !22}
!21 = !DIDerivedType(tag: DW_TAG_member, name: "f", scope: !19, file: !3, line: 13, baseType: !10, size: 64)
!22 = !DIDerivedType(tag: DW_TAG_member, name: "x", scope: !19, file: !3, line: 14, baseType: !23, size: 32, offset: 64)
!23 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!24 = !{i32 7, !"Dwarf Version", i32 5}
!25 = !{i32 2, !"Debug Info Version", i32 3}
!26 = !{i32 1, !"wchar_size", i32 4}
!27 = !{i32 8, !"PIC Level", i32 2}
!28 = !{i32 7, !"PIE Level", i32 2}
!29 = !{i32 7, !"uwtable", i32 2}
!30 = !{i32 7, !"frame-pointer", i32 2}
!31 = !{!"Ubuntu clang version 18.1.8 (++20240731025043+3b5b5c1ec4a3-1~exp1~20240731145144.92)"}
!32 = distinct !DISubprogram(name: "fa", scope: !3, file: !3, line: 20, type: !11, scopeLine: 20, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !2)
!33 = !DILocation(line: 20, column: 16, scope: !32)
!34 = distinct !DISubprogram(name: "fb", scope: !3, file: !3, line: 21, type: !11, scopeLine: 21, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !2)
!35 = !DILocation(line: 21, column: 16, scope: !34)
!36 = distinct !DISubprogram(name: "main", scope: !3, file: !3, line: 23, type: !37, scopeLine: 23, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !2, retainedNodes: !42)
!37 = !DISubroutineType(types: !38)
!38 = !{!23, !23, !39}
!39 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !40, size: 64)
!40 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !41, size: 64)
!41 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!42 = !{}
!43 = !DILocalVariable(name: "argc", arg: 1, scope: !36, file: !3, line: 23, type: !23)
!44 = !DILocation(line: 23, column: 14, scope: !36)
!45 = !DILocalVariable(name: "argv", arg: 2, scope: !36, file: !3, line: 23, type: !39)
!46 = !DILocation(line: 23, column: 27, scope: !36)
!47 = !DILocation(line: 24, column: 9, scope: !36)
!48 = !DILocation(line: 25, column: 7, scope: !36)
!49 = !DILocation(line: 26, column: 7, scope: !36)
!50 = !DILocation(line: 27, column: 10, scope: !36)
!51 = !DILocation(line: 27, column: 8, scope: !36)
!52 = !DILocation(line: 28, column: 5, scope: !36)
!53 = !DILocation(line: 28, column: 3, scope: !36)
!54 = !DILocation(line: 29, column: 3, scope: !36)
