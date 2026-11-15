// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Latency of `madd` through its multiplicand and through its addend, of the
// shift-add form of x*17 + y, and of `mul` (cycles / 8e8 per operation).
// Build: clang -O2 -o madd_latency madd_latency.c

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  int mode = atoi(argv[1]);
  uint64_t x = 5, k = 17, y = 3, n = 400000000ull;
  switch (mode) {
  case 0: for (uint64_t i = 0; i < n; i++) __asm__ volatile("madd %0, %0, %1, %2\n madd %0, %0, %1, %2" : "+r"(x) : "r"(k), "r"(y)); break; // via multiplicand
  case 1: for (uint64_t i = 0; i < n; i++) __asm__ volatile("madd %0, %1, %2, %0\n madd %0, %1, %2, %0" : "+r"(x) : "r"(k), "r"(y)); break; // via addend
  case 2: for (uint64_t i = 0; i < n; i++) __asm__ volatile("add %0, %0, %0, lsl #4\n add %0, %0, %2\n add %0, %0, %0, lsl #4\n add %0, %0, %2" : "+r"(x) : "r"(k), "r"(y)); break; // shift-add + add
  case 3: for (uint64_t i = 0; i < n; i++) __asm__ volatile("mul %0, %0, %1\n mul %0, %0, %1" : "+r"(x) : "r"(k)); break;
  }
  printf("%llu\n", (unsigned long long)x);
  return 0;
}
