/* Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 */
#include <asm/hwcap.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/auxv.h>

int main(int argc, char **argv) {
    if (argc != 2) return 10;
    if (!strcmp(argv[1], "features")) {
        unsigned long caps = getauxval(AT_HWCAP);
        printf("CPU_FEATURES hwcap=%lx hwcap2=%lx lse=%u fp16_scalar=%u fp16_simd=%u dotprod=%u\n",
               caps, getauxval(AT_HWCAP2), !!(caps & HWCAP_ATOMICS),
               !!(caps & HWCAP_FPHP), !!(caps & HWCAP_ASIMDHP), !!(caps & HWCAP_ASIMDDP));
        return 0;
    }
    if (!strcmp(argv[1], "llsc")) {
        uint32_t cell = 41, old, next, status;
        __asm__ volatile("0: ldaxr %w[old], [%[address]]\n"
                         "add %w[next], %w[old], #1\n"
                         "stlxr %w[status], %w[next], [%[address]]\n"
                         "cbnz %w[status], 0b\n"
                         : [old] "=&r" (old), [next] "=&r" (next), [status] "=&r" (status)
                         : [address] "r" (&cell) : "memory", "cc");
        return old == 41 && cell == 42 ? 0 : 11;
    }
    if (!strcmp(argv[1], "lse")) {
        uint32_t cell = 41, old, delta = 1;
        __asm__ volatile(".arch_extension lse\nldaddal %w[delta], %w[old], [%[address]]\n"
                         : [old] "=&r" (old) : [delta] "r" (delta), [address] "r" (&cell) : "memory");
        return old == 41 && cell == 42 ? 0 : 12;
    }
    if (!strcmp(argv[1], "fp16_scalar")) {
        uint32_t result;
        __asm__ volatile(".arch_extension fp16\nmov w9, #0x3c00\nfmov h0, w9\nfadd h0, h0, h0\nfmov %w[result], h0\n"
                         : [result] "=r" (result) : : "w9", "v0");
        return result == 0x4000 ? 0 : 13;
    }
    if (!strcmp(argv[1], "fp16_simd")) {
        uint32_t result;
        __asm__ volatile(".arch_extension fp16\nmovi v0.8h, #0x3c, lsl #8\nfadd v0.8h, v0.8h, v0.8h\numov %w[result], v0.h[0]\n"
                         : [result] "=r" (result) : : "v0");
        return result == 0x4000 ? 0 : 14;
    }
    if (!strcmp(argv[1], "dotprod")) {
        uint32_t result;
        __asm__ volatile(".arch_extension dotprod\nmovi v0.16b, #0\nmovi v1.16b, #1\nmovi v2.16b, #2\nudot v0.4s, v1.16b, v2.16b\numov %w[result], v0.s[0]\n"
                         : [result] "=r" (result) : : "v0", "v1", "v2");
        return result == 8 ? 0 : 15;
    }
    return 16;
}
