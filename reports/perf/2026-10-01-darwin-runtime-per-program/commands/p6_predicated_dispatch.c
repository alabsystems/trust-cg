// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// p6_branch_match's loop with its 7-way dispatch branched or predicated:
//   clang -O2 -o p6_pred p6_predicated_dispatch.c
//   abmodes.py ./p6_pred 7 branch select   (the program's random selector)
//   abmodes.py ./p6_pred 7 pbranch pselect (a predictable selector, i % 7)
//
// p6_branch_match's loop: argv[1] "branch" = the 7-way dispatch as written
// (clang -O2 picks its own dispatch), "select" = every arm computed and the
// result picked by index with no branch (a predicated switch); "pbranch" /
// "pselect" the same with a predictable selector (i % 7).
#include <stdint.h>
#include <string.h>
static inline uint64_t rotl(uint64_t x, unsigned r) { return (x << (r & 63)) | (x >> ((-r) & 63)); }
__attribute__((noinline)) static uint64_t run_branch(uint64_t s, uint64_t acc, uint64_t n) {
  for (uint64_t i = 0; i < n; i++) {
    s ^= s << 13; s ^= s >> 7; s ^= s << 17;
    switch (s % 7) {
      case 0: acc += s; break;
      case 1: acc ^= s; break;
      case 2: acc *= (s | 1); break;
      case 3: acc = rotl(acc, (unsigned)(s & 63)); break;
      case 4: acc -= s >> 5; break;
      case 5: acc += s >> (s & 31); break;
      default: acc += s ^ (acc >> 11); break;
    }
  }
  return acc;
}
__attribute__((noinline)) static uint64_t run_select(uint64_t s, uint64_t acc, uint64_t n) {
  for (uint64_t i = 0; i < n; i++) {
    s ^= s << 13; s ^= s >> 7; s ^= s << 17;
    uint64_t k = s % 7;
    uint64_t r0 = acc + s, r1 = acc ^ s, r2 = acc * (s | 1), r3 = rotl(acc, (unsigned)(s & 63));
    uint64_t r4 = acc - (s >> 5), r5 = acc + (s >> (s & 31)), r6 = acc + (s ^ (acc >> 11));
    uint64_t a = k == 0 ? r0 : r1, b = k == 2 ? r2 : r3, c = k == 4 ? r4 : r5;
    uint64_t lo = k <= 1 ? a : b, hi = k <= 5 ? c : r6;
    __asm__("" : "+r"(lo), "+r"(hi));  // keep the selects as csel
    acc = k <= 3 ? lo : hi;
  }
  return acc;
}
__attribute__((noinline)) static uint64_t run_pbranch(uint64_t s, uint64_t acc, uint64_t n) {
  for (uint64_t i = 0; i < n; i++) {
    s ^= s << 13; s ^= s >> 7; s ^= s << 17;
    switch (i % 7) {
      case 0: acc += s; break;
      case 1: acc ^= s; break;
      case 2: acc *= (s | 1); break;
      case 3: acc = rotl(acc, (unsigned)(s & 63)); break;
      case 4: acc -= s >> 5; break;
      case 5: acc += s >> (s & 31); break;
      default: acc += s ^ (acc >> 11); break;
    }
  }
  return acc;
}
__attribute__((noinline)) static uint64_t run_pselect(uint64_t s, uint64_t acc, uint64_t n) {
  for (uint64_t i = 0; i < n; i++) {
    s ^= s << 13; s ^= s >> 7; s ^= s << 17;
    uint64_t k = i % 7;
    uint64_t r0 = acc + s, r1 = acc ^ s, r2 = acc * (s | 1), r3 = rotl(acc, (unsigned)(s & 63));
    uint64_t r4 = acc - (s >> 5), r5 = acc + (s >> (s & 31)), r6 = acc + (s ^ (acc >> 11));
    uint64_t a = k == 0 ? r0 : r1, b = k == 2 ? r2 : r3, c = k == 4 ? r4 : r5;
    uint64_t lo = k <= 1 ? a : b, hi = k <= 5 ? c : r6;
    __asm__("" : "+r"(lo), "+r"(hi));  // keep the selects as csel
    acc = k <= 3 ? lo : hi;
  }
  return acc;
}
int main(int argc, char **argv) {
  volatile uint64_t s0 = 88172645463325252ull, n = 200000000ull;
  uint64_t acc = strcmp(argv[1], "branch") == 0 ? run_branch(s0, 0, n) : strcmp(argv[1], "select") == 0 ? run_select(s0, 0, n) : strcmp(argv[1], "pbranch") == 0 ? run_pbranch(s0, 0, n) : run_pselect(s0, 0, n);
  return (int)(acc % 126);
}
