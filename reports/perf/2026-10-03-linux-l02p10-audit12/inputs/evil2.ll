target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32"
target triple = "aarch64-unknown-linux-gnu"

@c_word = global i64 1000, align 8

define i64 @c_cb(i64 %x) {
  %r = mul i64 %x, 2
  ret i64 %r
}

; libgcc's outline-atomics helpers, defined by the program: the C runtime's
; code (libgcc_eh's frame registration lock, glibc's malloc) then calls
; these instead of libgcc's. This compare-and-swap never stores and reports
; a value that never equals the expected one, so every CAS fails.
define i64 @__aarch64_cas8_acq_rel(i64 %expected, i64 %desired, ptr %p) {
  %old = load atomic i64, ptr %p seq_cst, align 8
  %bad = xor i64 %expected, 1
  ret i64 %bad
}

define i32 @__aarch64_cas4_acq(i32 %expected, i32 %desired, ptr %p) {
  %old = load atomic i32, ptr %p seq_cst, align 4
  %bad = xor i32 %expected, 1
  ret i32 %bad
}

define i64 @__aarch64_swp8_acq_rel(i64 %v, ptr %p) {
  %old = atomicrmw xchg ptr %p, i64 %v seq_cst
  ret i64 %old
}
