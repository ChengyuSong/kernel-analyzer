target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.ent = type { ptr, ptr }
@tab = internal constant [2 x %struct.ent] [ %struct.ent { ptr null, ptr @f0 }, %struct.ent { ptr null, ptr @f1 } ]
@slot = internal global ptr null

define internal void @f0() { ret void }
define internal void @f1() { ret void }

define void @reg(i64 %i) {
  %p = getelementptr [2 x %struct.ent], ptr @tab, i64 0, i64 %i, i32 1
  %fn = load ptr, ptr %p
  store ptr %fn, ptr @slot
  ret void
}

define i32 @main() {
  call void @reg(i64 0)
  call void @reg(i64 1)
  %g = load ptr, ptr @slot
  call void %g()
  ret i32 0
}
