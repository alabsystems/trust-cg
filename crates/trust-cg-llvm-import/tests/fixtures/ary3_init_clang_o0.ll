; Minimized clang -O0-shaped ary3 initialization fixture for #922.
; The hot loop is equivalent to:
;   for (int i = 0; i < n; i++) a[i] = i + 1;

source_filename = "ary3_init_clang_o0.c"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx26.0.0"

@buf = internal global [25 x i32] zeroinitializer, align 4

define void @ary3_init(ptr noundef %a, i32 noundef %n) {
entry:
  %a.addr = alloca ptr, align 8
  %n.addr = alloca i32, align 4
  %i = alloca i32, align 4
  store ptr %a, ptr %a.addr, align 8
  store i32 %n, ptr %n.addr, align 4
  store i32 0, ptr %i, align 4
  br label %for.cond

for.cond:
  %i.load = load i32, ptr %i, align 4
  %n.load = load i32, ptr %n.addr, align 4
  %cmp = icmp slt i32 %i.load, %n.load
  br i1 %cmp, label %for.body, label %for.end

for.body:
  %i.value = load i32, ptr %i, align 4
  %value = add nsw i32 %i.value, 1
  %a.load = load ptr, ptr %a.addr, align 8
  %i.index = load i32, ptr %i, align 4
  %idxprom = sext i32 %i.index to i64
  %arrayidx = getelementptr inbounds i32, ptr %a.load, i64 %idxprom
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

define i32 @run_case(i32 noundef %n) {
entry:
  %n.addr = alloca i32, align 4
  %i = alloca i32, align 4
  store i32 %n, ptr %n.addr, align 4
  call void @reset_buf()
  %base = getelementptr inbounds [25 x i32], ptr @buf, i64 0, i64 0
  %n.call = load i32, ptr %n.addr, align 4
  call void @ary3_init(ptr noundef %base, i32 noundef %n.call)
  store i32 0, ptr %i, align 4
  br label %value.cond

value.cond:
  %value.i = load i32, ptr %i, align 4
  %value.n = load i32, ptr %n.addr, align 4
  %value.cmp = icmp slt i32 %value.i, %value.n
  br i1 %value.cmp, label %value.body, label %sentinel.init

value.body:
  %value.idx = load i32, ptr %i, align 4
  %value.idxprom = sext i32 %value.idx to i64
  %value.ptr = getelementptr inbounds [25 x i32], ptr @buf, i64 0, i64 %value.idxprom
  %actual = load i32, ptr %value.ptr, align 4
  %expected.base = load i32, ptr %i, align 4
  %expected = add nsw i32 %expected.base, 1
  %value.ok = icmp eq i32 %actual, %expected
  br i1 %value.ok, label %value.inc, label %value.fail

value.inc:
  %value.next.load = load i32, ptr %i, align 4
  %value.inc = add nsw i32 %value.next.load, 1
  store i32 %value.inc, ptr %i, align 4
  br label %value.cond

sentinel.init:
  %n.sentinel = load i32, ptr %n.addr, align 4
  store i32 %n.sentinel, ptr %i, align 4
  br label %sentinel.cond

sentinel.cond:
  %sentinel.i = load i32, ptr %i, align 4
  %sentinel.n = load i32, ptr %n.addr, align 4
  %sentinel.end = add nsw i32 %sentinel.n, 4
  %sentinel.cmp = icmp slt i32 %sentinel.i, %sentinel.end
  br i1 %sentinel.cmp, label %sentinel.body, label %ok

sentinel.body:
  %sentinel.idx = load i32, ptr %i, align 4
  %sentinel.idxprom = sext i32 %sentinel.idx to i64
  %sentinel.ptr = getelementptr inbounds [25 x i32], ptr @buf, i64 0, i64 %sentinel.idxprom
  %sentinel.actual = load i32, ptr %sentinel.ptr, align 4
  %sentinel.ok = icmp eq i32 %sentinel.actual, -559038737
  br i1 %sentinel.ok, label %sentinel.inc, label %sentinel.fail

sentinel.inc:
  %sentinel.next.load = load i32, ptr %i, align 4
  %sentinel.inc = add nsw i32 %sentinel.next.load, 1
  store i32 %sentinel.inc, ptr %i, align 4
  br label %sentinel.cond

ok:
  ret i32 0

value.fail:
  ret i32 1

sentinel.fail:
  ret i32 2
}

define i32 @main() {
entry:
  %case0 = call i32 @run_case(i32 noundef 0)
  %case0.bad = icmp ne i32 %case0, 0
  br i1 %case0.bad, label %fail0, label %case1

fail0:
  ret i32 %case0

case1:
  %case1.result = call i32 @run_case(i32 noundef 1)
  %case1.bad = icmp ne i32 %case1.result, 0
  br i1 %case1.bad, label %fail1, label %case2

fail1:
  ret i32 %case1.result

case2:
  %case2.result = call i32 @run_case(i32 noundef 2)
  %case2.bad = icmp ne i32 %case2.result, 0
  br i1 %case2.bad, label %fail2, label %case3

fail2:
  ret i32 %case2.result

case3:
  %case3.result = call i32 @run_case(i32 noundef 3)
  %case3.bad = icmp ne i32 %case3.result, 0
  br i1 %case3.bad, label %fail3, label %case4

fail3:
  ret i32 %case3.result

case4:
  %case4.result = call i32 @run_case(i32 noundef 4)
  %case4.bad = icmp ne i32 %case4.result, 0
  br i1 %case4.bad, label %fail4, label %case5

fail4:
  ret i32 %case4.result

case5:
  %case5.result = call i32 @run_case(i32 noundef 5)
  %case5.bad = icmp ne i32 %case5.result, 0
  br i1 %case5.bad, label %fail5, label %case7

fail5:
  ret i32 %case5.result

case7:
  %case7.result = call i32 @run_case(i32 noundef 7)
  %case7.bad = icmp ne i32 %case7.result, 0
  br i1 %case7.bad, label %fail7, label %case8

fail7:
  ret i32 %case7.result

case8:
  %case8.result = call i32 @run_case(i32 noundef 8)
  %case8.bad = icmp ne i32 %case8.result, 0
  br i1 %case8.bad, label %fail8, label %case9

fail8:
  ret i32 %case8.result

case9:
  %case9.result = call i32 @run_case(i32 noundef 9)
  %case9.bad = icmp ne i32 %case9.result, 0
  br i1 %case9.bad, label %fail9, label %case17

fail9:
  ret i32 %case9.result

case17:
  %case17.result = call i32 @run_case(i32 noundef 17)
  %case17.bad = icmp ne i32 %case17.result, 0
  br i1 %case17.bad, label %fail17, label %ok

fail17:
  ret i32 %case17.result

ok:
  ret i32 0
}
