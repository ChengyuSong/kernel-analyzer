; // t_cells_mergedident.ll — A4 (Fable 2026-10-21): two modules llvm-linked,
; // as binutils' nm-new.bc was. b.c's struct pb and struct pc have struct pa's
; // layout ({ long; void (*)(void) }), so the IR linker merges both into
; // %struct.pa and every b.c allocation is labeled struct.pa. The identity
; // comes from the site's own debug info: setb's malloc result goes to a
; // `struct pb *` local, so its object is named struct.pb at mint (a rename;
; // its cells and the answers are unchanged). setc's result goes to a
; // `struct pb *` and a `struct pc *` local: several identities, so the IR name
; // stays and the rule report has a row. seta's struct pa is in the IR under
; // its own name: nothing to do.
; //   a.c: struct pa *p = malloc(sizeof *p); p->f = fa; ga = p;  ga->f();
; //   b.c: struct pb *p = malloc(sizeof *p); p->g = fb; gb = p;  gb->g();
; //        struct pb *p; struct pc *q; p = q = malloc(sizeof *q); q->h = fc;
; //        gc = q; gb = p;  gc->h();
; // LOG: identities the linked IR merged away: 1 objects \(1 identity / IR struct pairs; A4: 1 heap objects named at mint by their site's debug type \(of 1 allocations whose sites name one\), 0 struct-labeled heap objects with no debug type at any site \(IR name\), 0 whose site's identity is not the label's size \(IR name\), 1 allocations whose sites name several identities \(IR name\)\): struct\.pb as struct\.pa x1;
; ModuleID = 'ab.bc'
source_filename = "llvm-link"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.pa = type { i64, ptr }

@ga = dso_local global ptr null, align 8, !dbg !0
@gb = dso_local global ptr null, align 8, !dbg !14
@gc = dso_local global ptr null, align 8, !dbg !19

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @fa() #0 !dbg !39 {
  ret void, !dbg !40
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @seta() #0 !dbg !41 {
  %1 = alloca ptr, align 8
  call void @llvm.dbg.declare(metadata ptr %1, metadata !43, metadata !DIExpression()), !dbg !44
  %2 = call noalias ptr @malloc(i64 noundef 16) #3, !dbg !45
  store ptr %2, ptr %1, align 8, !dbg !44
  %3 = load ptr, ptr %1, align 8, !dbg !46
  %4 = getelementptr inbounds %struct.pa, ptr %3, i32 0, i32 1, !dbg !47
  store ptr @fa, ptr %4, align 8, !dbg !48
  %5 = load ptr, ptr %1, align 8, !dbg !49
  store ptr %5, ptr @ga, align 8, !dbg !50
  ret void, !dbg !51
}

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: nounwind allocsize(0)
declare noalias ptr @malloc(i64 noundef) #2

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @calla() #0 !dbg !52 {
  %1 = load ptr, ptr @ga, align 8, !dbg !53
  %2 = getelementptr inbounds %struct.pa, ptr %1, i32 0, i32 1, !dbg !54
  %3 = load ptr, ptr %2, align 8, !dbg !54
  call void %3(), !dbg !53
  ret void, !dbg !55
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @fb() #0 !dbg !56 {
  ret void, !dbg !57
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @fc() #0 !dbg !58 {
  ret void, !dbg !59
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @setb() #0 !dbg !60 {
  %1 = alloca ptr, align 8
  call void @llvm.dbg.declare(metadata ptr %1, metadata !61, metadata !DIExpression()), !dbg !62
  %2 = call noalias ptr @malloc(i64 noundef 16) #3, !dbg !63
  store ptr %2, ptr %1, align 8, !dbg !62
  %3 = load ptr, ptr %1, align 8, !dbg !64
  %4 = getelementptr inbounds %struct.pa, ptr %3, i32 0, i32 1, !dbg !65
  store ptr @fb, ptr %4, align 8, !dbg !66
  %5 = load ptr, ptr %1, align 8, !dbg !67
  store ptr %5, ptr @gb, align 8, !dbg !68
  ret void, !dbg !69
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @setc() #0 !dbg !70 {
  %1 = alloca ptr, align 8
  %2 = alloca ptr, align 8
  call void @llvm.dbg.declare(metadata ptr %1, metadata !71, metadata !DIExpression()), !dbg !72
  call void @llvm.dbg.declare(metadata ptr %2, metadata !73, metadata !DIExpression()), !dbg !74
  %3 = call noalias ptr @malloc(i64 noundef 16) #3, !dbg !75
  store ptr %3, ptr %2, align 8, !dbg !76
  store ptr %3, ptr %1, align 8, !dbg !77
  %4 = load ptr, ptr %2, align 8, !dbg !78
  %5 = getelementptr inbounds %struct.pa, ptr %4, i32 0, i32 1, !dbg !79
  store ptr @fc, ptr %5, align 8, !dbg !80
  %6 = load ptr, ptr %2, align 8, !dbg !81
  store ptr %6, ptr @gc, align 8, !dbg !82
  %7 = load ptr, ptr %1, align 8, !dbg !83
  store ptr %7, ptr @gb, align 8, !dbg !84
  ret void, !dbg !85
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @callb() #0 !dbg !86 {
  %1 = load ptr, ptr @gb, align 8, !dbg !87
  %2 = getelementptr inbounds %struct.pa, ptr %1, i32 0, i32 1, !dbg !88
  %3 = load ptr, ptr %2, align 8, !dbg !88
  call void %3(), !dbg !87
  ret void, !dbg !89
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @callc() #0 !dbg !90 {
  %1 = load ptr, ptr @gc, align 8, !dbg !91
  %2 = getelementptr inbounds %struct.pa, ptr %1, i32 0, i32 1, !dbg !92
  %3 = load ptr, ptr %2, align 8, !dbg !92
  call void %3(), !dbg !91
  ret void, !dbg !93
}

attributes #0 = { noinline nounwind optnone uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #2 = { nounwind allocsize(0) "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { nounwind allocsize(0) }

!llvm.dbg.cu = !{!2, !16}
!llvm.ident = !{!31, !31}
!llvm.module.flags = !{!32, !33, !34, !35, !36, !37, !38}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(name: "ga", scope: !2, file: !3, line: 3, type: !5, isLocal: false, isDefinition: true)
!2 = distinct !DICompileUnit(language: DW_LANG_C11, file: !3, producer: "Ubuntu clang version 18.1.8 (++20240731025043+3b5b5c1ec4a3-1~exp1~20240731145144.92)", isOptimized: false, flags: "/usr/lib/llvm-18/bin/clang -g -O0 -emit-llvm -c a.c -o a.bc", runtimeVersion: 0, emissionKind: FullDebug, globals: !4, splitDebugInlining: false, nameTableKind: None)
!3 = !DIFile(filename: "a.c", directory: ".", checksumkind: CSK_MD5, checksum: "6eb4133b058f9fb8357050905c379ad0")
!4 = !{!0}
!5 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !6, size: 64)
!6 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "pa", file: !3, line: 2, size: 128, elements: !7)
!7 = !{!8, !10}
!8 = !DIDerivedType(tag: DW_TAG_member, name: "x", scope: !6, file: !3, line: 2, baseType: !9, size: 64)
!9 = !DIBasicType(name: "long", size: 64, encoding: DW_ATE_signed)
!10 = !DIDerivedType(tag: DW_TAG_member, name: "f", scope: !6, file: !3, line: 2, baseType: !11, size: 64, offset: 64)
!11 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !12, size: 64)
!12 = !DISubroutineType(types: !13)
!13 = !{null}
!14 = !DIGlobalVariableExpression(var: !15, expr: !DIExpression())
!15 = distinct !DIGlobalVariable(name: "gb", scope: !16, file: !17, line: 4, type: !26, isLocal: false, isDefinition: true)
!16 = distinct !DICompileUnit(language: DW_LANG_C11, file: !17, producer: "Ubuntu clang version 18.1.8 (++20240731025043+3b5b5c1ec4a3-1~exp1~20240731145144.92)", isOptimized: false, flags: "/usr/lib/llvm-18/bin/clang -g -O0 -emit-llvm -c b.c -o b.bc", runtimeVersion: 0, emissionKind: FullDebug, globals: !18, splitDebugInlining: false, nameTableKind: None)
!17 = !DIFile(filename: "b.c", directory: ".", checksumkind: CSK_MD5, checksum: "9ee67741e6c1924ae670b048d48c838b")
!18 = !{!14, !19}
!19 = !DIGlobalVariableExpression(var: !20, expr: !DIExpression())
!20 = distinct !DIGlobalVariable(name: "gc", scope: !16, file: !17, line: 5, type: !21, isLocal: false, isDefinition: true)
!21 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !22, size: 64)
!22 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "pc", file: !17, line: 3, size: 128, elements: !23)
!23 = !{!24, !25}
!24 = !DIDerivedType(tag: DW_TAG_member, name: "z", scope: !22, file: !17, line: 3, baseType: !9, size: 64)
!25 = !DIDerivedType(tag: DW_TAG_member, name: "h", scope: !22, file: !17, line: 3, baseType: !11, size: 64, offset: 64)
!26 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !27, size: 64)
!27 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "pb", file: !17, line: 2, size: 128, elements: !28)
!28 = !{!29, !30}
!29 = !DIDerivedType(tag: DW_TAG_member, name: "y", scope: !27, file: !17, line: 2, baseType: !9, size: 64)
!30 = !DIDerivedType(tag: DW_TAG_member, name: "g", scope: !27, file: !17, line: 2, baseType: !11, size: 64, offset: 64)
!31 = !{!"Ubuntu clang version 18.1.8 (++20240731025043+3b5b5c1ec4a3-1~exp1~20240731145144.92)"}
!32 = !{i32 7, !"Dwarf Version", i32 5}
!33 = !{i32 2, !"Debug Info Version", i32 3}
!34 = !{i32 1, !"wchar_size", i32 4}
!35 = !{i32 8, !"PIC Level", i32 2}
!36 = !{i32 7, !"PIE Level", i32 2}
!37 = !{i32 7, !"uwtable", i32 2}
!38 = !{i32 7, !"frame-pointer", i32 2}
!39 = distinct !DISubprogram(name: "fa", scope: !3, file: !3, line: 4, type: !12, scopeLine: 4, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !2)
!40 = !DILocation(line: 4, column: 16, scope: !39)
!41 = distinct !DISubprogram(name: "seta", scope: !3, file: !3, line: 5, type: !12, scopeLine: 5, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !2, retainedNodes: !42)
!42 = !{}
!43 = !DILocalVariable(name: "p", scope: !41, file: !3, line: 5, type: !5)
!44 = !DILocation(line: 5, column: 30, scope: !41)
!45 = !DILocation(line: 5, column: 34, scope: !41)
!46 = !DILocation(line: 5, column: 53, scope: !41)
!47 = !DILocation(line: 5, column: 56, scope: !41)
!48 = !DILocation(line: 5, column: 58, scope: !41)
!49 = !DILocation(line: 5, column: 69, scope: !41)
!50 = !DILocation(line: 5, column: 67, scope: !41)
!51 = !DILocation(line: 5, column: 72, scope: !41)
!52 = distinct !DISubprogram(name: "calla", scope: !3, file: !3, line: 6, type: !12, scopeLine: 6, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !2)
!53 = !DILocation(line: 6, column: 20, scope: !52)
!54 = !DILocation(line: 6, column: 24, scope: !52)
!55 = !DILocation(line: 6, column: 29, scope: !52)
!56 = distinct !DISubprogram(name: "fb", scope: !17, file: !17, line: 6, type: !12, scopeLine: 6, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !16)
!57 = !DILocation(line: 6, column: 16, scope: !56)
!58 = distinct !DISubprogram(name: "fc", scope: !17, file: !17, line: 7, type: !12, scopeLine: 7, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !16)
!59 = !DILocation(line: 7, column: 16, scope: !58)
!60 = distinct !DISubprogram(name: "setb", scope: !17, file: !17, line: 8, type: !12, scopeLine: 8, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !16, retainedNodes: !42)
!61 = !DILocalVariable(name: "p", scope: !60, file: !17, line: 8, type: !26)
!62 = !DILocation(line: 8, column: 30, scope: !60)
!63 = !DILocation(line: 8, column: 34, scope: !60)
!64 = !DILocation(line: 8, column: 53, scope: !60)
!65 = !DILocation(line: 8, column: 56, scope: !60)
!66 = !DILocation(line: 8, column: 58, scope: !60)
!67 = !DILocation(line: 8, column: 69, scope: !60)
!68 = !DILocation(line: 8, column: 67, scope: !60)
!69 = !DILocation(line: 8, column: 72, scope: !60)
!70 = distinct !DISubprogram(name: "setc", scope: !17, file: !17, line: 9, type: !12, scopeLine: 9, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !16, retainedNodes: !42)
!71 = !DILocalVariable(name: "p", scope: !70, file: !17, line: 9, type: !26)
!72 = !DILocation(line: 9, column: 30, scope: !70)
!73 = !DILocalVariable(name: "q", scope: !70, file: !17, line: 9, type: !21)
!74 = !DILocation(line: 9, column: 44, scope: !70)
!75 = !DILocation(line: 9, column: 55, scope: !70)
!76 = !DILocation(line: 9, column: 53, scope: !70)
!77 = !DILocation(line: 9, column: 49, scope: !70)
!78 = !DILocation(line: 9, column: 74, scope: !70)
!79 = !DILocation(line: 9, column: 77, scope: !70)
!80 = !DILocation(line: 9, column: 79, scope: !70)
!81 = !DILocation(line: 9, column: 90, scope: !70)
!82 = !DILocation(line: 9, column: 88, scope: !70)
!83 = !DILocation(line: 9, column: 98, scope: !70)
!84 = !DILocation(line: 9, column: 96, scope: !70)
!85 = !DILocation(line: 9, column: 101, scope: !70)
!86 = distinct !DISubprogram(name: "callb", scope: !17, file: !17, line: 10, type: !12, scopeLine: 10, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !16)
!87 = !DILocation(line: 10, column: 20, scope: !86)
!88 = !DILocation(line: 10, column: 24, scope: !86)
!89 = !DILocation(line: 10, column: 29, scope: !86)
!90 = distinct !DISubprogram(name: "callc", scope: !17, file: !17, line: 11, type: !12, scopeLine: 11, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !16)
!91 = !DILocation(line: 11, column: 20, scope: !90)
!92 = !DILocation(line: 11, column: 24, scope: !90)
!93 = !DILocation(line: 11, column: 29, scope: !90)
