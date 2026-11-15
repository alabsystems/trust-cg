; Minimized clang -O0-shaped i32 induction-store fixture whose loop starts
; at a nonzero, negative or i32::MAX-adjacent index (TRUSTCG-18):
;   for (int i = start; i < end; i++) a[i] = i + 1;
; run_case points `a` `start` elements before buf[offset], so the loop writes
; buf[offset .. offset + (end - start)] and nothing else. The GEPs from `a`
; are not inbounds, so the i32::MAX-adjacent cases stay defined.
; main returns 0 on success and the failing case's 1-based index otherwise.

source_filename = "ary3_init_offset_clang_o0.c"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx26.0.0"

@buf = internal global [25 x i32] zeroinitializer, align 4

define void @fill_from(ptr noundef %a, i32 noundef %start, i32 noundef %end) {
entry:
  %a.addr = alloca ptr, align 8
  %end.addr = alloca i32, align 4
  %i = alloca i32, align 4
  store ptr %a, ptr %a.addr, align 8
  store i32 %end, ptr %end.addr, align 4
  store i32 %start, ptr %i, align 4
  br label %for.cond

for.cond:
  %i.load = load i32, ptr %i, align 4
  %end.load = load i32, ptr %end.addr, align 4
  %cmp = icmp slt i32 %i.load, %end.load
  br i1 %cmp, label %for.body, label %for.end

for.body:
  %i.value = load i32, ptr %i, align 4
  %value = add nsw i32 %i.value, 1
  %a.load = load ptr, ptr %a.addr, align 8
  %i.index = load i32, ptr %i, align 4
  %idxprom = sext i32 %i.index to i64
  %arrayidx = getelementptr i32, ptr %a.load, i64 %idxprom
  store i32 %value, ptr %arrayidx, align 4
  br label %for.inc

for.inc:
  %i.next.load = load i32, ptr %i, align 4
  %inc = add nsw i32 %i.next.load, 1
  store i32 %inc, ptr %i, align 4
  br label %for.cond

for.end:
  ret void
}

define void @reset_buf() {
entry:
  %i = alloca i32, align 4
  store i32 0, ptr %i, align 4
  br label %loop.cond

loop.cond:
  %i.load = load i32, ptr %i, align 4
  %cmp = icmp slt i32 %i.load, 25
  br i1 %cmp, label %loop.body, label %loop.end

loop.body:
  %idx = load i32, ptr %i, align 4
  %idxprom = sext i32 %idx to i64
  %slot = getelementptr inbounds [25 x i32], ptr @buf, i64 0, i64 %idxprom
  store i32 -559038737, ptr %slot, align 4
  br label %loop.inc

loop.inc:
  %i.next.load = load i32, ptr %i, align 4
  %inc = add nsw i32 %i.next.load, 1
  store i32 %inc, ptr %i, align 4
  br label %loop.cond

loop.end:
  ret void
}

; 0 when buf[offset .. offset + max(end - start, 0)] holds start + 1 .. end
; and every other element still holds the sentinel; 1 otherwise.
define i32 @run_case(i32 noundef %start, i32 noundef %end, i32 noundef %offset) {
entry:
  %k = alloca i32, align 4
  call void @reset_buf()
  %offset.wide = sext i32 %offset to i64
  %start.wide = sext i32 %start to i64
  %delta = sub i64 %offset.wide, %start.wide
  %a = getelementptr i32, ptr @buf, i64 %delta
  call void @fill_from(ptr noundef %a, i32 noundef %start, i32 noundef %end)
  %end.wide = sext i32 %end to i64
  %span = sub i64 %end.wide, %start.wide
  %positive = icmp sgt i64 %span, 0
  %trip = select i1 %positive, i64 %span, i64 0
  %limit = add i64 %offset.wide, %trip
  store i32 0, ptr %k, align 4
  br label %check.cond

check.cond:
  %k.load = load i32, ptr %k, align 4
  %more = icmp slt i32 %k.load, 25
  br i1 %more, label %check.body, label %ok

check.body:
  %k.value = load i32, ptr %k, align 4
  %k.wide = sext i32 %k.value to i64
  %slot = getelementptr inbounds [25 x i32], ptr @buf, i64 0, i64 %k.wide
  %actual = load i32, ptr %slot, align 4
  %after.start = icmp sge i64 %k.wide, %offset.wide
  %before.end = icmp slt i64 %k.wide, %limit
  %in.range = and i1 %after.start, %before.end
  %rel = sub i32 %k.value, %offset
  %elem = add i32 %start, %rel
  %stored = add i32 %elem, 1
  %expected = select i1 %in.range, i32 %stored, i32 -559038737
  %match = icmp eq i32 %actual, %expected
  br i1 %match, label %check.inc, label %mismatch

check.inc:
  %k.next.load = load i32, ptr %k, align 4
  %k.next = add nsw i32 %k.next.load, 1
  store i32 %k.next, ptr %k, align 4
  br label %check.cond

ok:
  ret i32 0

mismatch:
  ret i32 1
}

define i32 @main() {
entry:
  br label %case1

case1:
  ; for (i = 4; i < 8; i++) with a[4] at buf[4]
  %r1 = call i32 @run_case(i32 noundef 4, i32 noundef 8, i32 noundef 4)
  %bad1 = icmp ne i32 %r1, 0
  br i1 %bad1, label %fail1, label %case2

fail1:
  ret i32 1

case2:
  ; for (i = 5; i < 23; i++) with a[5] at buf[2]
  %r2 = call i32 @run_case(i32 noundef 5, i32 noundef 23, i32 noundef 2)
  %bad2 = icmp ne i32 %r2, 0
  br i1 %bad2, label %fail2, label %case3

fail2:
  ret i32 2

case3:
  ; for (i = -3; i < 9; i++) with a[-3] at buf[5]
  %r3 = call i32 @run_case(i32 noundef -3, i32 noundef 9, i32 noundef 5)
  %bad3 = icmp ne i32 %r3, 0
  br i1 %bad3, label %fail3, label %case4

fail3:
  ret i32 3

case4:
  ; for (i = 1; i < 1; i++) with a[1] at buf[0]
  %r4 = call i32 @run_case(i32 noundef 1, i32 noundef 1, i32 noundef 0)
  %bad4 = icmp ne i32 %r4, 0
  br i1 %bad4, label %fail4, label %case5

fail4:
  ret i32 4

case5:
  ; for (i = 7; i < 3; i++) with a[7] at buf[0]
  %r5 = call i32 @run_case(i32 noundef 7, i32 noundef 3, i32 noundef 0)
  %bad5 = icmp ne i32 %r5, 0
  br i1 %bad5, label %fail5, label %case6

fail5:
  ret i32 5

case6:
  ; for (i = 0; i < 17; i++) with a[0] at buf[0]
  %r6 = call i32 @run_case(i32 noundef 0, i32 noundef 17, i32 noundef 0)
  %bad6 = icmp ne i32 %r6, 0
  br i1 %bad6, label %fail6, label %case7

fail6:
  ret i32 6

case7:
  ; for (i = 2; i < 25; i++) with a[2] at buf[0]
  %r7 = call i32 @run_case(i32 noundef 2, i32 noundef 25, i32 noundef 0)
  %bad7 = icmp ne i32 %r7, 0
  br i1 %bad7, label %fail7, label %case8

fail7:
  ret i32 7

case8:
  ; for (i = 2147483646; i < 2147483647; i++) with a[2147483646] at buf[3]
  %r8 = call i32 @run_case(i32 noundef 2147483646, i32 noundef 2147483647, i32 noundef 3)
  %bad8 = icmp ne i32 %r8, 0
  br i1 %bad8, label %fail8, label %case9

fail8:
  ret i32 8

case9:
  ; for (i = 2147483643; i < 2147483647; i++) with a[2147483643] at buf[10]
  %r9 = call i32 @run_case(i32 noundef 2147483643, i32 noundef 2147483647, i32 noundef 10)
  %bad9 = icmp ne i32 %r9, 0
  br i1 %bad9, label %fail9, label %case10

fail9:
  ret i32 9

case10:
  ; for (i = 2147483644; i < 2147483647; i++) with a[2147483644] at buf[20]
  %r10 = call i32 @run_case(i32 noundef 2147483644, i32 noundef 2147483647, i32 noundef 20)
  %bad10 = icmp ne i32 %r10, 0
  br i1 %bad10, label %fail10, label %case11

fail10:
  ret i32 10

case11:
  ; for (i = 2147483638; i < 2147483646; i++) with a[2147483638] at buf[12]
  %r11 = call i32 @run_case(i32 noundef 2147483638, i32 noundef 2147483646, i32 noundef 12)
  %bad11 = icmp ne i32 %r11, 0
  br i1 %bad11, label %fail11, label %case12

fail11:
  ret i32 11

case12:
  ; for (i = -2147483648; i < -2147483639; i++) with a[-2147483648] at buf[1]
  %r12 = call i32 @run_case(i32 noundef -2147483648, i32 noundef -2147483639, i32 noundef 1)
  %bad12 = icmp ne i32 %r12, 0
  br i1 %bad12, label %fail12, label %done

fail12:
  ret i32 12

done:
  ret i32 0
}
