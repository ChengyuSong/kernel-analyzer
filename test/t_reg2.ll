target datalayout = "e-m:e-p270:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.ent = type { ptr, ptr }
%struct.fd = type { i32, ptr }
@tab = internal constant [2 x %struct.ent] [ %struct.ent { ptr null, ptr @f0 }, %struct.ent { ptr null, ptr @f1 } ]
@bucket = internal global [4 x ptr] zeroinitializer

declare ptr @malloc(i64)
define internal void @f0() { ret void }
define internal void @f1() { ret void }

define internal void @create(ptr %fn, i64 %h) {
  %fd = call ptr @malloc(i64 16)
  %x = getelementptr %struct.fd, ptr %fd, i64 0, i32 1
  store ptr %fn, ptr %x
  %b = getelementptr [4 x ptr], ptr @bucket, i64 0, i64 %h
  store ptr %fd, ptr %b
  ret void
}

define void @reg(i64 %i) {
  %p = getelementptr [2 x %struct.ent], ptr @tab, i64 0, i64 %i, i32 1
  %fn = load ptr, ptr %p
  call void @create(ptr %fn, i64 %i)
  ret void
}

define i32 @main() {
  call void @reg(i64 0)
  call void @reg(i64 1)
  %b = getelementptr [4 x ptr], ptr @bucket, i64 0, i64 2
  %fd = load ptr, ptr %b
  %x = getelementptr %struct.fd, ptr %fd, i64 0, i32 1
  %g = load ptr, ptr %x
  call void %g()
  ret i32 0
}
