; ModuleID = 'tests/derivesmt.c'
source_filename = "tests/derivesmt.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@__const.main.default_str = private unnamed_addr constant [10 x i8] c"ABCDEFGHI\00", align 1
@.str = private unnamed_addr constant [8 x i8] c"a = %s\0A\00", align 1

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

8:                                                ; preds = %32, %3
  %9 = load i32, i32* %7, align 4
  %10 = zext i32 %9 to i64
  %11 = load i64, i64* %6, align 8
  %12 = icmp ult i64 %10, %11
  br i1 %12, label %13, label %35

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
  %23 = load i8*, i8** %5, align 8
  %24 = load i32, i32* %7, align 4
  %25 = zext i32 %24 to i64
  %26 = getelementptr inbounds i8, i8* %23, i64 %25
  %27 = load i8, i8* %26, align 1
  %28 = sext i8 %27 to i32
  %29 = icmp eq i32 %28, 0
  br i1 %29, label %30, label %31

30:                                               ; preds = %13
  br label %35

31:                                               ; preds = %13
  br label %32

32:                                               ; preds = %31
  %33 = load i32, i32* %7, align 4
  %34 = add i32 %33, 1
  store i32 %34, i32* %7, align 4
  br label %8, !llvm.loop !6

35:                                               ; preds = %30, %8
  ret void
}

; Function Attrs: noinline nounwind optnone sspstrong uwtable
define dso_local i32 @get_strsize(i8* %0) #0 {
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
define dso_local i32 @main(i32 %0, i8** %1, i8** %2) #0 {
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i8**, align 8
  %7 = alloca i8**, align 8
  %8 = alloca [60 x i8], align 16
  %9 = alloca i32, align 4
  %10 = alloca [10 x i8], align 1
  store i32 0, i32* %4, align 4
  store i32 %0, i32* %5, align 4
  store i8** %1, i8*** %6, align 8
  store i8** %2, i8*** %7, align 8
  %11 = load i32, i32* %5, align 4
  %12 = icmp sgt i32 %11, 1
  br i1 %12, label %13, label %24

13:                                               ; preds = %3
  %14 = load i8**, i8*** %6, align 8
  %15 = getelementptr inbounds i8*, i8** %14, i64 1
  %16 = load i8*, i8** %15, align 8
  %17 = call i32 @get_strsize(i8* %16)
  store i32 %17, i32* %9, align 4
  %18 = getelementptr inbounds [60 x i8], [60 x i8]* %8, i64 0, i64 0
  %19 = load i8**, i8*** %6, align 8
  %20 = getelementptr inbounds i8*, i8** %19, i64 1
  %21 = load i8*, i8** %20, align 8
  %22 = load i32, i32* %9, align 4
  %23 = zext i32 %22 to i64
  call void @dep_strcpy(i8* %18, i8* %21, i64 %23)
  br label %28

24:                                               ; preds = %3
  %25 = bitcast [10 x i8]* %10 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 1 %25, i8* align 1 getelementptr inbounds ([10 x i8], [10 x i8]* @__const.main.default_str, i32 0, i32 0), i64 10, i1 false)
  %26 = getelementptr inbounds [60 x i8], [60 x i8]* %8, i64 0, i64 0
  %27 = getelementptr inbounds [10 x i8], [10 x i8]* %10, i64 0, i64 0
  call void @dep_strcpy(i8* %26, i8* %27, i64 10)
  br label %28

28:                                               ; preds = %24, %13
  %29 = getelementptr inbounds [60 x i8], [60 x i8]* %8, i64 0, i64 0
  %30 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str, i64 0, i64 0), i8* %29)
  ret i32 0
}

; Function Attrs: argmemonly nofree nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #1

declare i32 @printf(i8*, ...) #2

attributes #0 = { noinline nounwind optnone sspstrong uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { argmemonly nofree nounwind willreturn }
attributes #2 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 1}
!4 = !{i32 7, !"frame-pointer", i32 2}
!5 = !{!"clang version 13.0.0"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}
