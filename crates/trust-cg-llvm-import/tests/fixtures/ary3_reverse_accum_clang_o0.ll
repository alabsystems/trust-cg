; Minimized clang -O0-shaped ary3 reverse accumulation fixture for #935.
; The hot loop is equivalent to:
;   for (int i = n - 1; i >= 0; --i) y[i] += x[i];

source_filename = "ary3_reverse_accum_clang_o0.c"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "arm64-apple-macosx26.0.0"

define i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  %3 = call i32 @run_case(i32 noundef 0)
  store i32 %3, ptr %2, align 4
  %4 = load i32, ptr %2, align 4
  %5 = icmp ne i32 %4, 0
  br i1 %5, label %6, label %8

6:
  %7 = load i32, ptr %2, align 4
  store i32 %7, ptr %1, align 4
  br label %63

8:
  %9 = call i32 @run_case(i32 noundef 1)
  store i32 %9, ptr %2, align 4
  %10 = load i32, ptr %2, align 4
  %11 = icmp ne i32 %10, 0
  br i1 %11, label %12, label %14

12:
  %13 = load i32, ptr %2, align 4
  store i32 %13, ptr %1, align 4
  br label %63

14:
  %15 = call i32 @run_case(i32 noundef 2)
  store i32 %15, ptr %2, align 4
  %16 = load i32, ptr %2, align 4
  %17 = icmp ne i32 %16, 0
  br i1 %17, label %18, label %20

18:
  %19 = load i32, ptr %2, align 4
  store i32 %19, ptr %1, align 4
  br label %63

20:
  %21 = call i32 @run_case(i32 noundef 3)
  store i32 %21, ptr %2, align 4
  %22 = load i32, ptr %2, align 4
  %23 = icmp ne i32 %22, 0
  br i1 %23, label %24, label %26

24:
  %25 = load i32, ptr %2, align 4
  store i32 %25, ptr %1, align 4
  br label %63

26:
  %27 = call i32 @run_case(i32 noundef 4)
  store i32 %27, ptr %2, align 4
  %28 = load i32, ptr %2, align 4
  %29 = icmp ne i32 %28, 0
  br i1 %29, label %30, label %32

30:
  %31 = load i32, ptr %2, align 4
  store i32 %31, ptr %1, align 4
  br label %63

32:
  %33 = call i32 @run_case(i32 noundef 5)
  store i32 %33, ptr %2, align 4
  %34 = load i32, ptr %2, align 4
  %35 = icmp ne i32 %34, 0
  br i1 %35, label %36, label %38

36:
  %37 = load i32, ptr %2, align 4
  store i32 %37, ptr %1, align 4
  br label %63

38:
  %39 = call i32 @run_case(i32 noundef 7)
  store i32 %39, ptr %2, align 4
  %40 = load i32, ptr %2, align 4
  %41 = icmp ne i32 %40, 0
  br i1 %41, label %42, label %44

42:
  %43 = load i32, ptr %2, align 4
  store i32 %43, ptr %1, align 4
  br label %63

44:
  %45 = call i32 @run_case(i32 noundef 8)
  store i32 %45, ptr %2, align 4
  %46 = load i32, ptr %2, align 4
  %47 = icmp ne i32 %46, 0
  br i1 %47, label %48, label %50

48:
  %49 = load i32, ptr %2, align 4
  store i32 %49, ptr %1, align 4
  br label %63

50:
  %51 = call i32 @run_case(i32 noundef 9)
  store i32 %51, ptr %2, align 4
  %52 = load i32, ptr %2, align 4
  %53 = icmp ne i32 %52, 0
  br i1 %53, label %54, label %56

54:
  %55 = load i32, ptr %2, align 4
  store i32 %55, ptr %1, align 4
  br label %63

56:
  %57 = call i32 @run_case(i32 noundef 17)
  store i32 %57, ptr %2, align 4
  %58 = load i32, ptr %2, align 4
  %59 = icmp ne i32 %58, 0
  br i1 %59, label %60, label %62

60:
  %61 = load i32, ptr %2, align 4
  store i32 %61, ptr %1, align 4
  br label %63

62:
  store i32 0, ptr %1, align 4
  br label %63

63:
  %64 = load i32, ptr %1, align 4
  ret i32 %64
}

define internal i32 @run_case(i32 noundef %0) #0 {
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca ptr, align 8
  %5 = alloca ptr, align 8
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  store i32 %0, ptr %3, align 4
  %8 = load i32, ptr %3, align 4
  %9 = sext i32 %8 to i64
  %10 = call ptr @calloc(i64 noundef %9, i64 noundef 4) #3
  store ptr %10, ptr %4, align 8
  %11 = load i32, ptr %3, align 4
  %12 = sext i32 %11 to i64
  %13 = call ptr @calloc(i64 noundef %12, i64 noundef 4) #3
  store ptr %13, ptr %5, align 8
  %14 = load ptr, ptr %4, align 8
  %15 = load ptr, ptr %5, align 8
  %16 = load i32, ptr %3, align 4
  call void @seed(ptr noundef %14, ptr noundef %15, i32 noundef %16)
  %17 = load i32, ptr %3, align 4
  %18 = sub nsw i32 %17, 1
  store i32 %18, ptr %6, align 4
  br label %19

19:
  %20 = load i32, ptr %6, align 4
  %21 = icmp sge i32 %20, 0
  br i1 %21, label %22, label %37

22:
  %23 = load ptr, ptr %4, align 8
  %24 = load i32, ptr %6, align 4
  %25 = sext i32 %24 to i64
  %26 = getelementptr inbounds i32, ptr %23, i64 %25
  %27 = load i32, ptr %26, align 4
  %28 = load ptr, ptr %5, align 8
  %29 = load i32, ptr %6, align 4
  %30 = sext i32 %29 to i64
  %31 = getelementptr inbounds i32, ptr %28, i64 %30
  %32 = load i32, ptr %31, align 4
  %33 = add nsw i32 %32, %27
  store i32 %33, ptr %31, align 4
  br label %34

34:
  %35 = load i32, ptr %6, align 4
  %36 = add nsw i32 %35, -1
  store i32 %36, ptr %6, align 4
  br label %19, !llvm.loop !6

37:
  store i32 0, ptr %7, align 4
  br label %38

38:
  %39 = load i32, ptr %7, align 4
  %40 = load i32, ptr %3, align 4
  %41 = icmp slt i32 %39, %40
  br i1 %41, label %42, label %61

42:
  %43 = load ptr, ptr %5, align 8
  %44 = load i32, ptr %7, align 4
  %45 = sext i32 %44 to i64
  %46 = getelementptr inbounds i32, ptr %43, i64 %45
  %47 = load i32, ptr %46, align 4
  %48 = load i32, ptr %7, align 4
  %49 = mul nsw i32 %48, 3
  %50 = load i32, ptr %7, align 4
  %51 = add nsw i32 %50, 1
  %52 = add nsw i32 %49, %51
  %53 = icmp ne i32 %47, %52
  br i1 %53, label %54, label %57

54:
  %55 = load i32, ptr %7, align 4
  %56 = add nsw i32 %55, 1
  store i32 %56, ptr %2, align 4
  br label %64

57:
  br label %58

58:
  %59 = load i32, ptr %7, align 4
  %60 = add nsw i32 %59, 1
  store i32 %60, ptr %7, align 4
  br label %38, !llvm.loop !8

61:
  %62 = load ptr, ptr %4, align 8
  call void @free(ptr noundef %62)
  %63 = load ptr, ptr %5, align 8
  call void @free(ptr noundef %63)
  store i32 0, ptr %2, align 4
  br label %64

64:
  %65 = load i32, ptr %2, align 4
  ret i32 %65
}

declare ptr @calloc(i64 noundef, i64 noundef) #1

define internal void @seed(ptr noundef %0, ptr noundef %1, i32 noundef %2) #0 {
  %4 = alloca ptr, align 8
  %5 = alloca ptr, align 8
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  store ptr %0, ptr %4, align 8
  store ptr %1, ptr %5, align 8
  store i32 %2, ptr %6, align 4
  store i32 0, ptr %7, align 4
  br label %8

8:
  %9 = load i32, ptr %7, align 4
  %10 = load i32, ptr %6, align 4
  %11 = icmp slt i32 %9, %10
  br i1 %11, label %12, label %28

12:
  %13 = load i32, ptr %7, align 4
  %14 = add nsw i32 %13, 1
  %15 = load ptr, ptr %4, align 8
  %16 = load i32, ptr %7, align 4
  %17 = sext i32 %16 to i64
  %18 = getelementptr inbounds i32, ptr %15, i64 %17
  store i32 %14, ptr %18, align 4
  %19 = load i32, ptr %7, align 4
  %20 = mul nsw i32 %19, 3
  %21 = load ptr, ptr %5, align 8
  %22 = load i32, ptr %7, align 4
  %23 = sext i32 %22 to i64
  %24 = getelementptr inbounds i32, ptr %21, i64 %23
  store i32 %20, ptr %24, align 4
  br label %25

25:
  %26 = load i32, ptr %7, align 4
  %27 = add nsw i32 %26, 1
  store i32 %27, ptr %7, align 4
  br label %8, !llvm.loop !9

28:
  ret void
}

declare void @free(ptr noundef) #2

attributes #0 = { noinline nounwind optnone }
attributes #1 = { allocsize(0,1) }
attributes #2 = { nounwind }
attributes #3 = { allocsize(0,1) }

!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}
!8 = distinct !{!8, !7}
!9 = distinct !{!9, !7}
