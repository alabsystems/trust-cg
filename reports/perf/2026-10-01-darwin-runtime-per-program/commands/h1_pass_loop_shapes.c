// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// h1_vec_push_sum's pass loop in four shapes, to ask whether the loop's shape
// moves its cycles:
//   clang -O2 -o h1_shapes h1_pass_loop_shapes.c
//   abmodes.py ./h1_shapes 15 A B C D
//
// argv[1]: A = LLVM -O3's loop, B = trust-cg's, C = 128 B per iteration,
// D = LLVM's with a 1 KiB-ahead prefetch.
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#define N 300000
static uint64_t sum_a(const uint64_t *p, uint64_t n) {
  uint64_t acc; const uint64_t *q = p + 4; uint64_t k = n & ~7ull;
  __asm__ volatile(
    "movi v0.2d, #0\n movi v1.2d, #0\n movi v2.2d, #0\n movi v3.2d, #0\n"
    "1: ldp q4, q5, [%[q], #-0x20]\n ldp q6, q7, [%[q]], #0x40\n"
    "add v1.2d, v4.2d, v1.2d\n add v0.2d, v5.2d, v0.2d\n add v2.2d, v6.2d, v2.2d\n add v3.2d, v7.2d, v3.2d\n"
    "subs %[k], %[k], #8\n b.ne 1b\n"
    "add v0.2d, v0.2d, v1.2d\n add v0.2d, v2.2d, v0.2d\n add v0.2d, v3.2d, v0.2d\n addp d0, v0.2d\n fmov %[acc], d0\n"
    : [acc] "=r"(acc), [q] "+r"(q), [k] "+r"(k) :: "v0","v1","v2","v3","v4","v5","v6","v7","memory","cc");
  return acc;
}
static uint64_t sum_b(const uint64_t *p, uint64_t n) {
  uint64_t acc; const uint64_t *x0 = p; uint64_t i = 0; uint64_t lim = n - 7;
  __asm__ volatile(
    "movi v7.16b, #0\n movi v5.16b, #0\n movi v6.16b, #0\n movi v4.16b, #0\n"
    "1: ldp q0, q1, [%[x0]], #0x20\n ldp q2, q3, [%[x0]], #0x20\n"
    "add v7.2d, v7.2d, v0.2d\n add v5.2d, v5.2d, v1.2d\n add v6.2d, v6.2d, v2.2d\n add v4.2d, v4.2d, v3.2d\n"
    "add %[i], %[i], #8\n cmp %[i], %[lim]\n b.lo 1b\n"
    "add v2.2d, v7.2d, v5.2d\n add v0.2d, v6.2d, v4.2d\n add v1.2d, v2.2d, v0.2d\n mov %[acc], v1.d[0]\n mov x9, v1.d[1]\n add %[acc], %[acc], x9\n"
    : [acc] "=r"(acc), [x0] "+r"(x0), [i] "+r"(i) : [lim] "r"(lim) : "x9","v0","v1","v2","v3","v4","v5","v6","v7","memory","cc");
  return acc;
}
static uint64_t sum_c(const uint64_t *p, uint64_t n) {
  uint64_t acc; const uint64_t *q = p; uint64_t k = n & ~15ull;
  __asm__ volatile(
    "movi v0.2d, #0\n movi v1.2d, #0\n movi v2.2d, #0\n movi v3.2d, #0\n"
    "1: ldp q4, q5, [%[q]]\n ldp q6, q7, [%[q], #0x20]\n ldp q16, q17, [%[q], #0x40]\n ldp q18, q19, [%[q], #0x60]\n add %[q], %[q], #0x80\n"
    "add v0.2d, v0.2d, v4.2d\n add v1.2d, v1.2d, v5.2d\n add v2.2d, v2.2d, v6.2d\n add v3.2d, v3.2d, v7.2d\n"
    "add v0.2d, v0.2d, v16.2d\n add v1.2d, v1.2d, v17.2d\n add v2.2d, v2.2d, v18.2d\n add v3.2d, v3.2d, v19.2d\n"
    "subs %[k], %[k], #16\n b.ne 1b\n"
    "add v0.2d, v0.2d, v1.2d\n add v0.2d, v2.2d, v0.2d\n add v0.2d, v3.2d, v0.2d\n addp d0, v0.2d\n fmov %[acc], d0\n"
    : [acc] "=r"(acc), [q] "+r"(q), [k] "+r"(k) :: "v0","v1","v2","v3","v4","v5","v6","v7","v16","v17","v18","v19","memory","cc");
  return acc;
}
static uint64_t sum_d(const uint64_t *p, uint64_t n) {
  uint64_t acc; const uint64_t *q = p + 4; uint64_t k = n & ~7ull;
  __asm__ volatile(
    "movi v0.2d, #0\n movi v1.2d, #0\n movi v2.2d, #0\n movi v3.2d, #0\n"
    "1: prfm pldl1strm, [%[q], #0x400]\n ldp q4, q5, [%[q], #-0x20]\n ldp q6, q7, [%[q]], #0x40\n"
    "add v1.2d, v4.2d, v1.2d\n add v0.2d, v5.2d, v0.2d\n add v2.2d, v6.2d, v2.2d\n add v3.2d, v7.2d, v3.2d\n"
    "subs %[k], %[k], #8\n b.ne 1b\n"
    "add v0.2d, v0.2d, v1.2d\n add v0.2d, v2.2d, v0.2d\n add v0.2d, v3.2d, v0.2d\n addp d0, v0.2d\n fmov %[acc], d0\n"
    : [acc] "=r"(acc), [q] "+r"(q), [k] "+r"(k) :: "v0","v1","v2","v3","v4","v5","v6","v7","memory","cc");
  return acc;
}
int main(int argc, char **argv) {
  uint64_t *v = malloc(N * 8); uint64_t x = 0x9E3779B97F4A7C15ull;
  for (int i = 0; i < N; i++) { x ^= x << 13; x ^= x >> 7; x ^= x << 17; v[i] = x; }
  uint64_t (*f)(const uint64_t *, uint64_t) =
    argv[1][0] == 'A' ? sum_a : argv[1][0] == 'B' ? sum_b : argv[1][0] == 'C' ? sum_c : sum_d;
  uint64_t acc = 0;
  for (int p = 0; p < 300; p++) acc += f(v, N);   // N is a multiple of 16
  return (int)(acc % 126);
}
