; ModuleID = './llvm2smt/examples/structs/structs.c'
source_filename = "./llvm2smt/examples/structs/structs.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-freebsd13.0"

%struct.s0 = type { i8 }
%struct.__sFILE = type { i8*, i32, i32, i16, i16, %struct.__sbuf, i32, i8*, i32 (i8*)*, i32 (i8*, i8*, i32)*, i64 (i8*, i64, i32)*, i32 (i8*, i8*, i32)*, %struct.__sbuf, i8*, i32, [3 x i8], [1 x i8], %struct.__sbuf, i32, i64, %struct.pthread_mutex*, %struct.pthread*, i32, i32, %union.__mbstate_t, i32 }
%struct.__sbuf = type { i8*, i32 }
%struct.pthread_mutex = type opaque
%struct.pthread = type opaque
%union.__mbstate_t = type { i64, [120 x i8] }
%struct.s1 = type { i8, i8, i16, i64 }
%struct.s2 = type { i8, i16 }
%struct.s3 = type { i8, double, i16 }
%struct.s4 = type { i8, double }
%struct.s5 = type { i8, i64 }
%struct.s6 = type { i8, float }
%union.s7 = type { i32 }

@__const.main.foo = private unnamed_addr constant %struct.s0 { i8 107 }, align 1
@__stderrp = external dso_local global %struct.__sFILE*, align 8
@.str = private unnamed_addr constant [34 x i8] c"sizeof(%s) = %d offset of c = %d\0A\00", align 1
@.str.1 = private unnamed_addr constant [3 x i8] c"s0\00", align 1
@.str.2 = private unnamed_addr constant [2 x i8] c"\0A\00", align 1
@.str.3 = private unnamed_addr constant [36 x i8] c"sizeof(%s) = %d offset of c   = %d\0A\00", align 1
@.str.4 = private unnamed_addr constant [3 x i8] c"s1\00", align 1
@.str.5 = private unnamed_addr constant [36 x i8] c"sizeof(%s) = %d offset of d   = %d\0A\00", align 1
@.str.6 = private unnamed_addr constant [36 x i8] c"sizeof(%s) = %d offset of s   = %d\0A\00", align 1
@.str.7 = private unnamed_addr constant [36 x i8] c"sizeof(%s) = %d offset of n   = %d\0A\00", align 1
@.str.8 = private unnamed_addr constant [3 x i8] c"s2\00", align 1
@.str.9 = private unnamed_addr constant [3 x i8] c"s3\00", align 1
@.str.10 = private unnamed_addr constant [3 x i8] c"s4\00", align 1
@.str.11 = private unnamed_addr constant [3 x i8] c"s5\00", align 1
@.str.12 = private unnamed_addr constant [36 x i8] c"sizeof(%s) = %d offset of i64 = %d\0A\00", align 1
@.str.13 = private unnamed_addr constant [3 x i8] c"s6\00", align 1
@.str.14 = private unnamed_addr constant [36 x i8] c"sizeof(%s) = %d offset of f   = %d\0A\00", align 1
@.str.15 = private unnamed_addr constant [36 x i8] c"sizeof(%s) = %d offset of j   = %d\0A\00", align 1
@.str.16 = private unnamed_addr constant [4 x i8] c"%c\0A\00", align 1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local %struct.s0* @make_s0(i8 signext %0) #0 {
  %2 = alloca i8, align 1
  %3 = alloca %struct.s0*, align 8
  store i8 %0, i8* %2, align 1
  %4 = call noalias i8* @malloc(i64 1) #4
  %5 = bitcast i8* %4 to %struct.s0*
  store %struct.s0* %5, %struct.s0** %3, align 8
  %6 = load i8, i8* %2, align 1
  %7 = load %struct.s0*, %struct.s0** %3, align 8
  %8 = getelementptr inbounds %struct.s0, %struct.s0* %7, i32 0, i32 0
  store i8 %6, i8* %8, align 1
  %9 = load %struct.s0*, %struct.s0** %3, align 8
  ret %struct.s0* %9
}

; Function Attrs: allocsize(0)
declare dso_local noalias i8* @malloc(i64) #1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local %struct.s1* @make_s1(i8 signext %0, i8 signext %1, i16 signext %2, i64 %3) #0 {
  %5 = alloca i8, align 1
  %6 = alloca i8, align 1
  %7 = alloca i16, align 2
  %8 = alloca i64, align 8
  %9 = alloca %struct.s1*, align 8
  store i8 %0, i8* %5, align 1
  store i8 %1, i8* %6, align 1
  store i16 %2, i16* %7, align 2
  store i64 %3, i64* %8, align 8
  %10 = call noalias i8* @malloc(i64 16) #4
  %11 = bitcast i8* %10 to %struct.s1*
  store %struct.s1* %11, %struct.s1** %9, align 8
  %12 = load i8, i8* %5, align 1
  %13 = load %struct.s1*, %struct.s1** %9, align 8
  %14 = getelementptr inbounds %struct.s1, %struct.s1* %13, i32 0, i32 0
  store i8 %12, i8* %14, align 8
  %15 = load i8, i8* %6, align 1
  %16 = load %struct.s1*, %struct.s1** %9, align 8
  %17 = getelementptr inbounds %struct.s1, %struct.s1* %16, i32 0, i32 1
  store i8 %15, i8* %17, align 1
  %18 = load i16, i16* %7, align 2
  %19 = load %struct.s1*, %struct.s1** %9, align 8
  %20 = getelementptr inbounds %struct.s1, %struct.s1* %19, i32 0, i32 2
  store i16 %18, i16* %20, align 2
  %21 = load i64, i64* %8, align 8
  %22 = load %struct.s1*, %struct.s1** %9, align 8
  %23 = getelementptr inbounds %struct.s1, %struct.s1* %22, i32 0, i32 3
  store i64 %21, i64* %23, align 8
  %24 = load %struct.s1*, %struct.s1** %9, align 8
  ret %struct.s1* %24
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local %struct.s2* @make_s2(i8 signext %0, i16 signext %1) #0 {
  %3 = alloca i8, align 1
  %4 = alloca i16, align 2
  %5 = alloca %struct.s2*, align 8
  store i8 %0, i8* %3, align 1
  store i16 %1, i16* %4, align 2
  %6 = call noalias i8* @malloc(i64 4) #4
  %7 = bitcast i8* %6 to %struct.s2*
  store %struct.s2* %7, %struct.s2** %5, align 8
  %8 = load i8, i8* %3, align 1
  %9 = load %struct.s2*, %struct.s2** %5, align 8
  %10 = getelementptr inbounds %struct.s2, %struct.s2* %9, i32 0, i32 0
  store i8 %8, i8* %10, align 2
  %11 = load i16, i16* %4, align 2
  %12 = load %struct.s2*, %struct.s2** %5, align 8
  %13 = getelementptr inbounds %struct.s2, %struct.s2* %12, i32 0, i32 1
  store i16 %11, i16* %13, align 2
  %14 = load %struct.s2*, %struct.s2** %5, align 8
  ret %struct.s2* %14
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local %struct.s3* @make_s3(i8 signext %0, double %1, i16 signext %2) #0 {
  %4 = alloca i8, align 1
  %5 = alloca double, align 8
  %6 = alloca i16, align 2
  %7 = alloca %struct.s3*, align 8
  store i8 %0, i8* %4, align 1
  store double %1, double* %5, align 8
  store i16 %2, i16* %6, align 2
  %8 = call noalias i8* @malloc(i64 24) #4
  %9 = bitcast i8* %8 to %struct.s3*
  store %struct.s3* %9, %struct.s3** %7, align 8
  %10 = load i8, i8* %4, align 1
  %11 = load %struct.s3*, %struct.s3** %7, align 8
  %12 = getelementptr inbounds %struct.s3, %struct.s3* %11, i32 0, i32 0
  store i8 %10, i8* %12, align 8
  %13 = load double, double* %5, align 8
  %14 = load %struct.s3*, %struct.s3** %7, align 8
  %15 = getelementptr inbounds %struct.s3, %struct.s3* %14, i32 0, i32 1
  store double %13, double* %15, align 8
  %16 = load i16, i16* %6, align 2
  %17 = load %struct.s3*, %struct.s3** %7, align 8
  %18 = getelementptr inbounds %struct.s3, %struct.s3* %17, i32 0, i32 2
  store i16 %16, i16* %18, align 8
  %19 = load %struct.s3*, %struct.s3** %7, align 8
  ret %struct.s3* %19
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local %struct.s4* @make_s4(i8 signext %0, double %1) #0 {
  %3 = alloca i8, align 1
  %4 = alloca double, align 8
  %5 = alloca %struct.s4*, align 8
  store i8 %0, i8* %3, align 1
  store double %1, double* %4, align 8
  %6 = call noalias i8* @malloc(i64 16) #4
  %7 = bitcast i8* %6 to %struct.s4*
  store %struct.s4* %7, %struct.s4** %5, align 8
  %8 = load i8, i8* %3, align 1
  %9 = load %struct.s4*, %struct.s4** %5, align 8
  %10 = getelementptr inbounds %struct.s4, %struct.s4* %9, i32 0, i32 0
  store i8 %8, i8* %10, align 8
  %11 = load double, double* %4, align 8
  %12 = load %struct.s4*, %struct.s4** %5, align 8
  %13 = getelementptr inbounds %struct.s4, %struct.s4* %12, i32 0, i32 1
  store double %11, double* %13, align 8
  %14 = load %struct.s4*, %struct.s4** %5, align 8
  ret %struct.s4* %14
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local %struct.s5* @make_s5(i8 signext %0, i64 %1) #0 {
  %3 = alloca i8, align 1
  %4 = alloca i64, align 8
  %5 = alloca %struct.s5*, align 8
  store i8 %0, i8* %3, align 1
  store i64 %1, i64* %4, align 8
  %6 = call noalias i8* @malloc(i64 16) #4
  %7 = bitcast i8* %6 to %struct.s5*
  store %struct.s5* %7, %struct.s5** %5, align 8
  %8 = load i8, i8* %3, align 1
  %9 = load %struct.s5*, %struct.s5** %5, align 8
  %10 = getelementptr inbounds %struct.s5, %struct.s5* %9, i32 0, i32 0
  store i8 %8, i8* %10, align 8
  %11 = load i64, i64* %4, align 8
  %12 = load %struct.s5*, %struct.s5** %5, align 8
  %13 = getelementptr inbounds %struct.s5, %struct.s5* %12, i32 0, i32 1
  store i64 %11, i64* %13, align 8
  %14 = load %struct.s5*, %struct.s5** %5, align 8
  ret %struct.s5* %14
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local %struct.s6* @make_s6(i8 signext %0, float %1) #0 {
  %3 = alloca i8, align 1
  %4 = alloca float, align 4
  %5 = alloca %struct.s6*, align 8
  store i8 %0, i8* %3, align 1
  store float %1, float* %4, align 4
  %6 = call noalias i8* @malloc(i64 8) #4
  %7 = bitcast i8* %6 to %struct.s6*
  store %struct.s6* %7, %struct.s6** %5, align 8
  %8 = load i8, i8* %3, align 1
  %9 = load %struct.s6*, %struct.s6** %5, align 8
  %10 = getelementptr inbounds %struct.s6, %struct.s6* %9, i32 0, i32 0
  store i8 %8, i8* %10, align 4
  %11 = load float, float* %4, align 4
  %12 = load %struct.s6*, %struct.s6** %5, align 8
  %13 = getelementptr inbounds %struct.s6, %struct.s6* %12, i32 0, i32 1
  store float %11, float* %13, align 4
  %14 = load %struct.s6*, %struct.s6** %5, align 8
  ret %struct.s6* %14
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local %union.s7* @make_s7(i8 signext %0, i16 signext %1, i32 %2) #0 {
  %4 = alloca i8, align 1
  %5 = alloca i16, align 2
  %6 = alloca i32, align 4
  %7 = alloca %union.s7*, align 8
  store i8 %0, i8* %4, align 1
  store i16 %1, i16* %5, align 2
  store i32 %2, i32* %6, align 4
  %8 = call noalias i8* @malloc(i64 4) #4
  %9 = bitcast i8* %8 to %union.s7*
  store %union.s7* %9, %union.s7** %7, align 8
  %10 = load i8, i8* %4, align 1
  %11 = load %union.s7*, %union.s7** %7, align 8
  %12 = bitcast %union.s7* %11 to i8*
  store i8 %10, i8* %12, align 4
  %13 = load i16, i16* %5, align 2
  %14 = load %union.s7*, %union.s7** %7, align 8
  %15 = bitcast %union.s7* %14 to i16*
  store i16 %13, i16* %15, align 4
  %16 = load i32, i32* %6, align 4
  %17 = load %union.s7*, %union.s7** %7, align 8
  %18 = bitcast %union.s7* %17 to i32*
  store i32 %16, i32* %18, align 4
  %19 = load %union.s7*, %union.s7** %7, align 8
  ret %union.s7* %19
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main(i32 %0, i8** %1) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i8**, align 8
  %6 = alloca %struct.s0, align 1
  store i32 0, i32* %3, align 4
  store i32 %0, i32* %4, align 4
  store i8** %1, i8*** %5, align 8
  %7 = bitcast %struct.s0* %6 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 1 %7, i8* align 1 getelementptr inbounds (%struct.s0, %struct.s0* @__const.main.foo, i32 0, i32 0), i64 1, i1 false)
  %8 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %9 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %8, i8* getelementptr inbounds ([34 x i8], [34 x i8]* @.str, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.1, i64 0, i64 0), i32 1, i32 0)
  %10 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %11 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %10, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i64 0, i64 0))
  %12 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %13 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %12, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.3, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.4, i64 0, i64 0), i32 16, i32 0)
  %14 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %15 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %14, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.5, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.4, i64 0, i64 0), i32 16, i32 1)
  %16 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %17 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %16, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.6, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.4, i64 0, i64 0), i32 16, i32 2)
  %18 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %19 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %18, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.7, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.4, i64 0, i64 0), i32 16, i32 8)
  %20 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %21 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %20, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i64 0, i64 0))
  %22 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %23 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %22, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.3, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.8, i64 0, i64 0), i32 4, i32 0)
  %24 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %25 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %24, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.6, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.8, i64 0, i64 0), i32 4, i32 2)
  %26 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %27 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %26, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i64 0, i64 0))
  %28 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %29 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %28, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.3, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.9, i64 0, i64 0), i32 24, i32 0)
  %30 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %31 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %30, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.5, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.9, i64 0, i64 0), i32 24, i32 8)
  %32 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %33 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %32, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.6, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.9, i64 0, i64 0), i32 24, i32 16)
  %34 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %35 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %34, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i64 0, i64 0))
  %36 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %37 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %36, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.3, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.10, i64 0, i64 0), i32 16, i32 0)
  %38 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %39 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %38, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.5, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.10, i64 0, i64 0), i32 16, i32 8)
  %40 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %41 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %40, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i64 0, i64 0))
  %42 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %43 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %42, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.3, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.11, i64 0, i64 0), i32 16, i32 0)
  %44 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %45 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %44, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.12, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.11, i64 0, i64 0), i32 16, i32 8)
  %46 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %47 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %46, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i64 0, i64 0))
  %48 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %49 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %48, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.3, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.13, i64 0, i64 0), i32 8, i32 0)
  %50 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %51 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %50, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.14, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.13, i64 0, i64 0), i32 8, i32 4)
  %52 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %53 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %52, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i64 0, i64 0))
  %54 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %55 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %54, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.3, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.13, i64 0, i64 0), i32 4, i32 0)
  %56 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %57 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %56, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.6, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.13, i64 0, i64 0), i32 4, i32 0)
  %58 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %59 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %58, i8* getelementptr inbounds ([36 x i8], [36 x i8]* @.str.15, i64 0, i64 0), i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.13, i64 0, i64 0), i32 4, i32 0)
  %60 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %61 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %60, i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.2, i64 0, i64 0))
  %62 = load %struct.__sFILE*, %struct.__sFILE** @__stderrp, align 8
  %63 = getelementptr inbounds %struct.s0, %struct.s0* %6, i32 0, i32 0
  %64 = load i8, i8* %63, align 1
  %65 = sext i8 %64 to i32
  %66 = call i32 (%struct.__sFILE*, i8*, ...) @fprintf(%struct.__sFILE* %62, i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.16, i64 0, i64 0), i32 %65)
  ret i32 0
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #2

declare dso_local i32 @fprintf(%struct.__sFILE*, i8*, ...) #3

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { allocsize(0) "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { argmemonly nounwind willreturn }
attributes #3 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { allocsize(0) }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"FreeBSD clang version 11.0.1 (git@github.com:llvm/llvm-project.git llvmorg-11.0.1-0-g43ff75f2c3fe)"}
