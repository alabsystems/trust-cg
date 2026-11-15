; clang -O0 LLVM IR of the C program below, the INTMM_MAIN_LOOP_C source in
; tests/intmm_o2_e2e.rs. That test imports it when no clang is on PATH (the
; Linux AArch64 floor host has only GCC) and checks this header against the
; embedded source. Everything after the source block is unmodified output of
;   Ubuntu clang 18.1.3 (1ubuntu1): clang --target=aarch64-unknown-linux-gnu
;   -O0 -S -emit-llvm -o intmm_main_loop_clang_o0.ll intmm_main_loop_o2.c
;
; |
; | #include <stdio.h>
; |
; | #define rowsize 40
; |
; | long seed;
; | int ima[rowsize + 1][rowsize + 1];
; | int imb[rowsize + 1][rowsize + 1];
; | int imr[rowsize + 1][rowsize + 1];
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
; | void Innerproduct(int *result, int a[rowsize + 1][rowsize + 1],
; |                   int b[rowsize + 1][rowsize + 1], int row, int column) {
; |     int i;
; |     *result = 0;
; |     for (i = 1; i <= rowsize; i++) {
; |         *result += a[row][i] * b[i][column];
; |     }
; | }
; |
; | void Intmm(int run) {
; |     int i, j;
; |     Initrand();
; |     Initmatrix(ima);
; |     Initmatrix(imb);
; |     for (i = 1; i <= rowsize; i++) {
; |         for (j = 1; j <= rowsize; j++) {
; |             Innerproduct(&imr[i][j], ima, imb, i, j);
; |         }
; |     }
; |     printf("%d\n", imr[run + 1][run + 1]);
; | }
; |
; | int main(void) {
; |     int i;
; |     for (i = 0; i < 10; i++) {
; |         Intmm(i);
; |     }
; |     return 0;
; | }

; ModuleID = 'intmm_main_loop_o2.c'
source_filename = "intmm_main_loop_o2.c"
target datalayout = "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128"
target triple = "aarch64-unknown-linux-gnu"

@seed = dso_local global i64 0, align 8
@ima = dso_local global [41 x [41 x i32]] zeroinitializer, align 4
@imb = dso_local global [41 x [41 x i32]] zeroinitializer, align 4
@imr = dso_local global [41 x [41 x i32]] zeroinitializer, align 4
@.str = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1

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
define dso_local void @Innerproduct(ptr noundef %0, ptr noundef %1, ptr noundef %2, i32 noundef %3, i32 noundef %4) #0 {
  %6 = alloca ptr, align 8
  %7 = alloca ptr, align 8
  %8 = alloca ptr, align 8
  %9 = alloca i32, align 4
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  store ptr %0, ptr %6, align 8
  store ptr %1, ptr %7, align 8
  store ptr %2, ptr %8, align 8
  store i32 %3, ptr %9, align 4
  store i32 %4, ptr %10, align 4
  %12 = load ptr, ptr %6, align 8
  store i32 0, ptr %12, align 4
  store i32 1, ptr %11, align 4
  br label %13

13:                                               ; preds = %37, %5
  %14 = load i32, ptr %11, align 4
  %15 = icmp sle i32 %14, 40
  br i1 %15, label %16, label %40

16:                                               ; preds = %13
  %17 = load ptr, ptr %7, align 8
  %18 = load i32, ptr %9, align 4
  %19 = sext i32 %18 to i64
  %20 = getelementptr inbounds [41 x i32], ptr %17, i64 %19
  %21 = load i32, ptr %11, align 4
  %22 = sext i32 %21 to i64
  %23 = getelementptr inbounds [41 x i32], ptr %20, i64 0, i64 %22
  %24 = load i32, ptr %23, align 4
  %25 = load ptr, ptr %8, align 8
  %26 = load i32, ptr %11, align 4
  %27 = sext i32 %26 to i64
  %28 = getelementptr inbounds [41 x i32], ptr %25, i64 %27
  %29 = load i32, ptr %10, align 4
  %30 = sext i32 %29 to i64
  %31 = getelementptr inbounds [41 x i32], ptr %28, i64 0, i64 %30
  %32 = load i32, ptr %31, align 4
  %33 = mul nsw i32 %24, %32
  %34 = load ptr, ptr %6, align 8
  %35 = load i32, ptr %34, align 4
  %36 = add nsw i32 %35, %33
  store i32 %36, ptr %34, align 4
  br label %37

37:                                               ; preds = %16
  %38 = load i32, ptr %11, align 4
  %39 = add nsw i32 %38, 1
  store i32 %39, ptr %11, align 4
  br label %13, !llvm.loop !9

40:                                               ; preds = %13
  ret void
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local void @Intmm(i32 noundef %0) #0 {
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
  call void @Initrand()
  call void @Initmatrix(ptr noundef @ima)
  call void @Initmatrix(ptr noundef @imb)
  store i32 1, ptr %3, align 4
  br label %5

5:                                                ; preds = %25, %1
  %6 = load i32, ptr %3, align 4
  %7 = icmp sle i32 %6, 40
  br i1 %7, label %8, label %28

8:                                                ; preds = %5
  store i32 1, ptr %4, align 4
  br label %9

9:                                                ; preds = %21, %8
  %10 = load i32, ptr %4, align 4
  %11 = icmp sle i32 %10, 40
  br i1 %11, label %12, label %24

12:                                               ; preds = %9
  %13 = load i32, ptr %3, align 4
  %14 = sext i32 %13 to i64
  %15 = getelementptr inbounds [41 x [41 x i32]], ptr @imr, i64 0, i64 %14
  %16 = load i32, ptr %4, align 4
  %17 = sext i32 %16 to i64
  %18 = getelementptr inbounds [41 x i32], ptr %15, i64 0, i64 %17
  %19 = load i32, ptr %3, align 4
  %20 = load i32, ptr %4, align 4
  call void @Innerproduct(ptr noundef %18, ptr noundef @ima, ptr noundef @imb, i32 noundef %19, i32 noundef %20)
  br label %21

21:                                               ; preds = %12
  %22 = load i32, ptr %4, align 4
  %23 = add nsw i32 %22, 1
  store i32 %23, ptr %4, align 4
  br label %9, !llvm.loop !10

24:                                               ; preds = %9
  br label %25

25:                                               ; preds = %24
  %26 = load i32, ptr %3, align 4
  %27 = add nsw i32 %26, 1
  store i32 %27, ptr %3, align 4
  br label %5, !llvm.loop !11

28:                                               ; preds = %5
  %29 = load i32, ptr %2, align 4
  %30 = add nsw i32 %29, 1
  %31 = sext i32 %30 to i64
  %32 = getelementptr inbounds [41 x [41 x i32]], ptr @imr, i64 0, i64 %31
  %33 = load i32, ptr %2, align 4
  %34 = add nsw i32 %33, 1
  %35 = sext i32 %34 to i64
  %36 = getelementptr inbounds [41 x i32], ptr %32, i64 0, i64 %35
  %37 = load i32, ptr %36, align 4
  %38 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %37)
  ret void
}

declare i32 @printf(ptr noundef, ...) #1

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  store i32 0, ptr %2, align 4
  br label %3

3:                                                ; preds = %8, %0
  %4 = load i32, ptr %2, align 4
  %5 = icmp slt i32 %4, 10
  br i1 %5, label %6, label %11

6:                                                ; preds = %3
  %7 = load i32, ptr %2, align 4
  call void @Intmm(i32 noundef %7)
  br label %8

8:                                                ; preds = %6
  %9 = load i32, ptr %2, align 4
  %10 = add nsw i32 %9, 1
  store i32 %10, ptr %2, align 4
  br label %3, !llvm.loop !12

11:                                               ; preds = %3
  ret i32 0
}

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
!9 = distinct !{!9, !7}
!10 = distinct !{!10, !7}
!11 = distinct !{!11, !7}
!12 = distinct !{!12, !7}
