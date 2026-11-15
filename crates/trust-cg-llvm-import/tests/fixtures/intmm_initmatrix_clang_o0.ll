; clang -O0 LLVM IR of the C program below, the INTMM_INITMATRIX_C source in
; tests/intmm_o2_e2e.rs. That test imports it when no clang is on PATH (the
; Linux AArch64 floor host has only GCC) and checks this header against the
; embedded source. Everything after the source block is unmodified output of
;   Ubuntu clang 18.1.3 (1ubuntu1): clang --target=aarch64-unknown-linux-gnu
;   -O0 -S -emit-llvm -o intmm_initmatrix_clang_o0.ll intmm_initmatrix_o2.c
;
; |
; | #include <stdio.h>
; |
; | #define rowsize 40
; |
; | long seed;
; | int ima[rowsize + 1][rowsize + 1];
; |
; | void Initrand(void) {
; |     seed = 74755L;
; | }
; |
; | int Rand(void) {
; |     seed = (seed * 1309L + 13849L) & 65535L;
; |     return (int)seed;
; | }
; |
; | void Initmatrix(int m[rowsize + 1][rowsize + 1]) {
; |     int temp, i, j;
; |     for (i = 1; i <= rowsize; i++) {
; |         for (j = 1; j <= rowsize; j++) {
; |             temp = Rand();
; |             m[i][j] = temp - (temp / 120) * 120 - 60;
; |         }
; |     }
; | }
; |
; | int main(void) {
; |     int first = 1;
; |     int last = rowsize;
; |     Initrand();
; |     Initmatrix(ima);
; |     printf("%d %d\n", ima[first][first], ima[last][last]);
; |     return 0;
; | }

; ModuleID = 'intmm_initmatrix_o2.c'
source_filename = "intmm_initmatrix_o2.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

@seed = dso_local global i64 0, align 8
@ima = dso_local global [41 x [41 x i32]] zeroinitializer, align 4
@.str = private unnamed_addr constant [7 x i8] c"%d %d\0A\00", align 1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @Initrand() #0 {
  store i64 74755, ptr @seed, align 8
  ret void
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @Rand() #0 {
  %1 = load i64, ptr @seed, align 8
  %2 = mul nsw i64 %1, 1309
  %3 = add nsw i64 %2, 13849
  %4 = and i64 %3, 65535
  store i64 %4, ptr @seed, align 8
  %5 = load i64, ptr @seed, align 8
  %6 = trunc i64 %5 to i32
  ret i32 %6
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @Initmatrix(ptr noundef %0) #0 {
  %2 = alloca ptr, align 8
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  store ptr %0, ptr %2, align 8
  store i32 1, ptr %4, align 4
  br label %6

6:                                                ; preds = %32, %1
  %7 = load i32, ptr %4, align 4
  %8 = icmp sle i32 %7, 40
  br i1 %8, label %9, label %35

9:                                                ; preds = %6
  store i32 1, ptr %5, align 4
  br label %10

10:                                               ; preds = %28, %9
  %11 = load i32, ptr %5, align 4
  %12 = icmp sle i32 %11, 40
  br i1 %12, label %13, label %31

13:                                               ; preds = %10
  %14 = call i32 @Rand()
  store i32 %14, ptr %3, align 4
  %15 = load i32, ptr %3, align 4
  %16 = load i32, ptr %3, align 4
  %17 = sdiv i32 %16, 120
  %18 = mul nsw i32 %17, 120
  %19 = sub nsw i32 %15, %18
  %20 = sub nsw i32 %19, 60
  %21 = load ptr, ptr %2, align 8
  %22 = load i32, ptr %4, align 4
  %23 = sext i32 %22 to i64
  %24 = getelementptr inbounds [41 x i32], ptr %21, i64 %23
  %25 = load i32, ptr %5, align 4
  %26 = sext i32 %25 to i64
  %27 = getelementptr inbounds [41 x i32], ptr %24, i64 0, i64 %26
  store i32 %20, ptr %27, align 4
  br label %28

28:                                               ; preds = %13
  %29 = load i32, ptr %5, align 4
  %30 = add nsw i32 %29, 1
  store i32 %30, ptr %5, align 4
  br label %10, !llvm.loop !6

31:                                               ; preds = %10
  br label %32

32:                                               ; preds = %31
  %33 = load i32, ptr %4, align 4
  %34 = add nsw i32 %33, 1
  store i32 %34, ptr %4, align 4
  br label %6, !llvm.loop !8

35:                                               ; preds = %6
  ret void
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  store i32 1, ptr %2, align 4
  store i32 40, ptr %3, align 4
  call void @Initrand()
  call void @Initmatrix(ptr noundef @ima)
  %4 = load i32, ptr %2, align 4
  %5 = sext i32 %4 to i64
  %6 = getelementptr inbounds [41 x [41 x i32]], ptr @ima, i64 0, i64 %5
  %7 = load i32, ptr %2, align 4
  %8 = sext i32 %7 to i64
  %9 = getelementptr inbounds [41 x i32], ptr %6, i64 0, i64 %8
  %10 = load i32, ptr %9, align 4
  %11 = load i32, ptr %3, align 4
  %12 = sext i32 %11 to i64
  %13 = getelementptr inbounds [41 x [41 x i32]], ptr @ima, i64 0, i64 %12
  %14 = load i32, ptr %3, align 4
  %15 = sext i32 %14 to i64
  %16 = getelementptr inbounds [41 x i32], ptr %13, i64 0, i64 %15
  %17 = load i32, ptr %16, align 4
  %18 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %10, i32 noundef %17)
  ret i32 0
}

declare i32 @printf(ptr noundef, ...) #1

attributes #0 = { noinline nounwind optnone uwtable "frame-pointer"="non-leaf" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="generic" "target-features"="+fp-armv8,+neon,+outline-atomics,+v8a,-fmv" }
attributes #1 = { "frame-pointer"="non-leaf" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="generic" "target-features"="+fp-armv8,+neon,+outline-atomics,+v8a,-fmv" }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 1}
!5 = !{!"Ubuntu clang version 18.1.3 (1ubuntu1)"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}
!8 = distinct !{!8, !7}
