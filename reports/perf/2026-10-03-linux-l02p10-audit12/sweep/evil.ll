target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "aarch64-unknown-linux-gnu"

@c_word = global i64 1000, align 8

define i64 @c_cb(i64 %x) {
  %r = mul i64 %x, 2
  ret i64 %r
}

; A start-up routine of the program's own in place of glibc's: it calls main
; without glibc's set-up (no IRELATIVE application, no TLS set-up).
define i32 @__libc_start_main(ptr %main, i32 %argc, ptr %argv, ptr %init, ptr %fini, ptr %rtld_fini, ptr %stack_end) {
  %r = call i32 %main(i32 %argc, ptr %argv, ptr null)
  call void asm sideeffect "mov x8, #94\0Asvc #0", "{x0}"(i32 %r)
  unreachable
}
