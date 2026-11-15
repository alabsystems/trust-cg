// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// C model of h3_box_leak (1.5M boxed u64, 20 deref-sum passes), to measure
// what unrolling the gather sum is worth on the host core:
//   clang -O3 -DUNROLL=1 -o h3_u1 h3_gather_unroll_model.c   (unroll disabled)
//   clang -O3 -DUNROLL=0 -o h3_def h3_gather_unroll_model.c  (clang's default)

#include <stdint.h>
#include <stdlib.h>
#ifndef UNROLL
#define UNROLL 1
#endif
int main(void) {
  volatile size_t vn = 1500000; size_t n = vn;
  volatile uint64_t vx = 0x243F6A8885A308D3ull; uint64_t x = vx;
  uint64_t **v = malloc(8 * n);
  for (size_t i = 0; i < n; i++) { x ^= x << 13; x ^= x >> 7; x ^= x << 17; uint64_t *b = malloc(8); *b = x; v[i] = b; }
  volatile uint32_t vp = 20; uint32_t passes = vp; uint64_t acc = 0;
  for (uint32_t p = 0; p < passes; p++) {
#if UNROLL == 1
#pragma clang loop unroll(disable)
#endif
    for (size_t k = 0; k < n; k++) acc += *v[k];
  }
  exit((int)(acc % 126));
}
