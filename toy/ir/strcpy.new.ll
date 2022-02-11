; ModuleID = 'toy/src/strcpy.c'
source_filename = "toy/src/strcpy.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local void @dep_strcpy(i8* %0, i8* %1, i64 %2) #0 {
  %4 = alloca i8*, align 8
  %5 = alloca i8*, align 8
  %6 = alloca i64, align 8
  %7 = alloca i32, align 4
  store i8* %0, i8** %4, align 8
  store i8* %1, i8** %5, align 8
  store i64 %2, i64* %6, align 8
  store i32 0, i32* %7, align 4
  br label %8

8:                                                ; preds = %23, %3
  %9 = load i32, i32* %7, align 4
  %10 = zext i32 %9 to i64
  %11 = load i64, i64* %6, align 8
  %12 = icmp ult i64 %10, %11
  br i1 %12, label %13, label %26

13:                                               ; preds = %8
  %14 = load i8*, i8** %5, align 8
  %15 = load i32, i32* %7, align 4
  %16 = zext i32 %15 to i64
  %17 = getelementptr inbounds i8, i8* %14, i64 %16
  %18 = load i8, i8* %17, align 1
  %19 = load i8*, i8** %4, align 8
  %20 = load i32, i32* %7, align 4
  %21 = zext i32 %20 to i64
  %22 = getelementptr inbounds i8, i8* %19, i64 %21
  store i8 %18, i8* %22, align 1
  br label %23

23:                                               ; preds = %13
  %24 = load i32, i32* %7, align 4
  %25 = add i32 %24, 1
  store i32 %25, i32* %7, align 4
  br label %8, !llvm.loop !6

26:                                               ; preds = %8
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local i32 @get_strsize_1(i8* %0) #0 {
  %2 = alloca i8*, align 8
  %3 = alloca i32, align 4
  store i8* %0, i8** %2, align 8
  store i32 0, i32* %3, align 4
  br label %4

4:                                                ; preds = %1, %13
  %5 = load i8*, i8** %2, align 8
  %6 = load i32, i32* %3, align 4
  %7 = zext i32 %6 to i64
  %8 = getelementptr inbounds i8, i8* %5, i64 %7
  %9 = load i8, i8* %8, align 1
  %10 = sext i8 %9 to i32
  %11 = icmp eq i32 %10, 0
  br i1 %11, label %12, label %13

12:                                               ; preds = %4
  br label %16

13:                                               ; preds = %4
  %14 = load i32, i32* %3, align 4
  %15 = add i32 %14, 1
  store i32 %15, i32* %3, align 4
  br label %4

16:                                               ; preds = %12
  %17 = load i32, i32* %3, align 4
  %18 = add i32 %17, 1
  ret i32 %18
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local i32 @get_strsize_2(i8* %0) #0 {
  %2 = alloca i8*, align 8
  %3 = alloca i32, align 4
  store i8* %0, i8** %2, align 8
  store i32 0, i32* %3, align 4
  br label %4

4:                                                ; preds = %1, %22
  %5 = load i8*, i8** %2, align 8
  %6 = load i32, i32* %3, align 4
  %7 = zext i32 %6 to i64
  %8 = getelementptr inbounds i8, i8* %5, i64 %7
  %9 = load i8, i8* %8, align 1
  %10 = sext i8 %9 to i32
  %11 = icmp eq i32 %10, 0
  br i1 %11, label %12, label %13

12:                                               ; preds = %4
  br label %23

13:                                               ; preds = %4
  %14 = load i32, i32* %3, align 4
  %15 = add i32 %14, 1
  store i32 %15, i32* %3, align 4
  %16 = load i32, i32* %3, align 4
  %17 = urem i32 %16, 2
  %18 = icmp eq i32 %17, 0
  br i1 %18, label %19, label %22

19:                                               ; preds = %13
  %20 = load i32, i32* %3, align 4
  %21 = add i32 %20, 1
  store i32 %21, i32* %3, align 4
  br label %22

22:                                               ; preds = %19, %13
  br label %4

23:                                               ; preds = %12
  %24 = load i32, i32* %3, align 4
  %25 = add i32 %24, 1
  ret i32 %25
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local i8* @get_heap_str(i8* %0) #0 {
  %2 = alloca i8*, align 8
  %3 = alloca i32, align 4
  %4 = alloca i8*, align 8
  store i8* %0, i8** %2, align 8
  %5 = load i8*, i8** %2, align 8
  %6 = call i32 @get_strsize_1(i8* %5)
  store i32 %6, i32* %3, align 4
  %7 = load i32, i32* %3, align 4
  %8 = zext i32 %7 to i64
  %9 = mul i64 1, %8
  %10 = call noalias align 16 i8* @malloc(i64 %9) #2
  store i8* %10, i8** %4, align 8
  %11 = load i8*, i8** %4, align 8
  %12 = load i8*, i8** %2, align 8
  %13 = load i32, i32* %3, align 4
  %14 = zext i32 %13 to i64
  call void @dep_strcpy(i8* %11, i8* %12, i64 %14)
  %15 = load i8*, i8** %4, align 8
  ret i8* %15
}

; Function Attrs: nounwind
declare noalias align 16 i8* @malloc(i64) #1

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local void @free_heap_str(i8* %0) #0 {
  %2 = alloca i8*, align 8
  store i8* %0, i8** %2, align 8
  %3 = load i8*, i8** %2, align 8
  call void @free(i8* %3) #2
  ret void
}

; Function Attrs: nounwind
declare void @free(i8*) #1

attributes #0 = { noinline nounwind optnone sspstrong uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { nounwind }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 1}
!4 = !{i32 7, !"frame-pointer", i32 2}
!5 = !{!"clang version 13.0.1"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}
