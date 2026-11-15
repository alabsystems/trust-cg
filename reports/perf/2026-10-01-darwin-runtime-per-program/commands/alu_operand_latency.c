// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Latency of single AArch64 ALU forms on the host core, each a chain of 4
// dependent instructions per iteration (cycles / 16e8 per instruction):
// mode 0 ubfiz; 1 eor through the UNshifted operand; 2 eor through the
// shifted operand; 3 plain eor; 4 lsl.
// Build: clang -O2 -o alu_operand_latency alu_operand_latency.c

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  int mode = atoi(argv[1]);
  uint64_t x = 0x243F6A8885A308D3ull, y = 0x1234, n = 400000000ull;
  switch (mode) {
  case 0: for (uint64_t i = 0; i < n; i++) __asm__ volatile("ubfiz %0, %0, #6, #51\n ubfiz %0, %0, #6, #51\n ubfiz %0, %0, #6, #51\n ubfiz %0, %0, #6, #51" : "+r"(x)); break; // ubfiz latency x4
  case 1: for (uint64_t i = 0; i < n; i++) __asm__ volatile("eor %0, %0, %1, lsl #13\n eor %0, %0, %1, lsl #13\n eor %0, %0, %1, lsl #13\n eor %0, %0, %1, lsl #13" : "+r"(x) : "r"(y)); break; // chain through UNshifted operand x4
  case 2: for (uint64_t i = 0; i < n; i++) __asm__ volatile("eor %0, %1, %0, lsl #13\n eor %0, %1, %0, lsl #13\n eor %0, %1, %0, lsl #13\n eor %0, %1, %0, lsl #13" : "+r"(x) : "r"(y)); break; // chain through shifted operand x4
  case 3: for (uint64_t i = 0; i < n; i++) __asm__ volatile("eor %0, %0, %1\n eor %0, %0, %1\n eor %0, %0, %1\n eor %0, %0, %1" : "+r"(x) : "r"(y)); break; // plain eor x4
  case 4: for (uint64_t i = 0; i < n; i++) __asm__ volatile("lsl %0, %0, #3\n lsl %0, %0, #3\n lsl %0, %0, #3\n lsl %0, %0, #3" : "+r"(x)); break; // lsl x4
  }
  printf("%llu\n", (unsigned long long)x);
  return 0;
}
