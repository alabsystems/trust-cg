// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Recurrence latency of one xorshift64 state update on the host core.
// mode 0: three `eor x, x, x, lsl/lsr #k` (the shifted operand is the chain);
// mode 1: the same split into `lsl/lsr` + plain `eor`;
// mode 2: steps 1+2 fused as xorshift-pair-fusion emits them
//         (`eor t, x, x, lsl #13; ubfiz w, x, #6, #51; eor u, w, x, lsr #7;
//         eor y, t, u`), then step 3.
// Build: clang -O2 -o xorshift_chain_latency xorshift_chain_latency.c
// Run:   /usr/bin/time -l ./xorshift_chain_latency <mode>   (cycles / 4e8)

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  int mode = atoi(argv[1]);
  uint64_t x = 0x243F6A8885A308D3ull, n = 400000000ull;
  if (mode == 0) { // eor shifted
    for (uint64_t i = 0; i < n; i++) {
      __asm__ volatile("eor %0, %0, %0, lsl #13\n eor %0, %0, %0, lsr #7\n eor %0, %0, %0, lsl #17" : "+r"(x));
    }
  } else if (mode == 1) { // split lsl + eor
    uint64_t t;
    for (uint64_t i = 0; i < n; i++) {
      __asm__ volatile("lsl %1, %0, #13\n eor %0, %0, %1\n lsr %1, %0, #7\n eor %0, %0, %1\n lsl %1, %0, #17\n eor %0, %0, %1" : "+r"(x), "=&r"(t));
    }
  } else if (mode == 2) { // merged steps 1+2: x2 = (x ^ x<<13) ^ ((x>>7) ^ ((x<<13)>>7)), then step 3
    uint64_t a, b;
    for (uint64_t i = 0; i < n; i++) {
      __asm__ volatile(
        "eor %1, %0, %0, lsl #13\n"   // a = x ^ x<<13
        "ubfiz %2, %0, #6, #51\n"     // b = (x<<13)>>7 = (x & (2^51-1)) << 6
        "eor %2, %2, %0, lsr #7\n"    // b ^= x>>7
        "eor %0, %1, %2\n"            // x2
        "eor %0, %0, %0, lsl #17\n"   // x3
        : "+r"(x), "=&r"(a), "=&r"(b));
    }
  }
  printf("%llu\n", (unsigned long long)x);
  return 0;
}
