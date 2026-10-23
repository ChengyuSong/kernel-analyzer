// t_cells_packedarray.c — packed partial arrays (rule (a), Fable 2026-10-22):
// clang emits a partially initialized array as a packed literal struct
// (<{ ptr x6, [10 x ptr] zeroinitializer }> for tbl[16]); labeled by that
// literal, the initializer's writes land in per-field cells and a runtime
// index over it is an index over one object, which read the null element
// only (tcpdump print-fr.c:860). Labeled by its debug type's array
// [16 x ptr] once the premise is checked, the call reaches both targets.
// The union array keeps its literal: its element writes an i64 where
// union u's IR type has a pointer (one row, the field and the reason).
// LOG: packed array @tbl: labeled \[16 x ptr\] from DI \(literal <\{ 6 x ptr, \[10 x ptr\] \}>, 7 fields, zero tail 10\)
// LOG: packed array @uarr: not labeled .*: a non-pointer over a pointer field of T at \+0
typedef void (*fn)(int);
void f1(int x) { (void)x; }
void f5(int x) { (void)x; }
fn tbl[16] = {[1] = f1, [5] = f5};
union u { void *p; long l; };
union u uarr[8] = {[0].l = 5, [1].l = 7};
void call(int i) { tbl[i](i); } // CHECK: f1 f5
long use(int i) { return uarr[i].l; }
