// Is p4_matmul's 8% the LOOP NEST -- a 3-iteration inner `j` loop that LLVM does not
// have, because it fully unrolls `j` and strides a whole 24-element row?
//
// Both variants do IDENTICAL SSE work: 12 multiply-accumulate units per `k`, over 24 `k`,
// repeated `reps` times. They differ ONLY in structure:
//
//   A (trust-cg): a `k` loop containing a `j` loop of 3 iterations x 4 units,
//                 with indexed addressing off the `j` counter.
//   B (LLVM):     a `k` loop whose body is 12 units fully unrolled at fixed
//                 displacements, no inner loop at all.
//
// Each unit is the 2-movdqa (LLVM-style) form, since movdqa is already measured free, so
// the only difference left is the inner loop's counter, compare, branch and indexing.
#include <stdio.h>
#include <stdlib.h>

static long long acc[32] __attribute__((aligned(16)));
static long long bsrc[2] __attribute__((aligned(16)));
static long long inv[4] __attribute__((aligned(16)));

#define UNIT(disp)                                  \
    "movdqu (%[b]), %%xmm1\n"                       \
    "movdqa %%xmm1, %%xmm3\n"                       \
    "pmuludq %%xmm4, %%xmm3\n"                      \
    "movdqa %%xmm1, %%xmm2\n"                       \
    "pmuludq %%xmm5, %%xmm2\n"                      \
    "psrlq $32, %%xmm1\n"                           \
    "pmuludq %%xmm4, %%xmm1\n"                      \
    "paddq %%xmm2, %%xmm1\n"                        \
    "psllq $32, %%xmm1\n"                           \
    "paddq %%xmm1, %%xmm3\n"                        \
    "movdqu " disp "(%[a]), %%xmm0\n"               \
    "paddq %%xmm3, %%xmm0\n"                        \
    "movdqu %%xmm0, " disp "(%[a])\n"

/* indexed form for the inner-loop variant: base + j*8 + disp */
#define UNIT_IDX(disp)                              \
    "movdqu (%[b]), %%xmm1\n"                       \
    "movdqa %%xmm1, %%xmm3\n"                       \
    "pmuludq %%xmm4, %%xmm3\n"                      \
    "movdqa %%xmm1, %%xmm2\n"                       \
    "pmuludq %%xmm5, %%xmm2\n"                      \
    "psrlq $32, %%xmm1\n"                           \
    "pmuludq %%xmm4, %%xmm1\n"                      \
    "paddq %%xmm2, %%xmm1\n"                        \
    "psllq $32, %%xmm1\n"                           \
    "paddq %%xmm1, %%xmm3\n"                        \
    "movdqu " disp "(%[a],%%rdi,8), %%xmm0\n"       \
    "paddq %%xmm3, %%xmm0\n"                        \
    "movdqu %%xmm0, " disp "(%[a],%%rdi,8)\n"

int main(int argc, char **argv) {
    long reps = atol(argv[1]);
    int variant = atoi(argv[2]);
    bsrc[0] = 0x1122334455667788LL; bsrc[1] = 0x99aabbccddeeff00LL;
    inv[0] = 0x0f0f0f0f0f0f0f0fLL;  inv[1] = 0x1111111111111111LL;
    inv[2] = 0x2222222222222222LL;  inv[3] = 0x3333333333333333LL;
    for (int i = 0; i < 32; i++) acc[i] = 0;

    if (variant == 0) {
        /* A: k loop containing a 3-iteration j loop of 4 units */
        __asm__ volatile (
            "movdqa (%[iv]), %%xmm4\n"
            "movdqa 16(%[iv]), %%xmm5\n"
            "2:\n"
            "mov $24, %%rsi\n"                  /* k = 24 */
            "3:\n"
            "xor %%rdi, %%rdi\n"                /* j = 0 */
            "4:\n"
            UNIT_IDX("0") UNIT_IDX("16") UNIT_IDX("32") UNIT_IDX("48")
            "add $8, %%rdi\n"
            "cmp $24, %%rdi\n"
            "jb 4b\n"
            "dec %%rsi\n"
            "jnz 3b\n"
            "dec %[reps]\n"
            "jnz 2b\n"
            : [reps] "+r" (reps)
            : [a] "r" (acc), [b] "r" (bsrc), [iv] "r" (inv)
            : "rsi","rdi","xmm0","xmm1","xmm2","xmm3","xmm4","xmm5","memory","cc");
    } else {
        /* B: k loop whose body is 12 units fully unrolled, no inner loop */
        __asm__ volatile (
            "movdqa (%[iv]), %%xmm4\n"
            "movdqa 16(%[iv]), %%xmm5\n"
            "2:\n"
            "mov $24, %%rsi\n"
            "3:\n"
            UNIT("0")   UNIT("16")  UNIT("32")  UNIT("48")
            UNIT("64")  UNIT("80")  UNIT("96")  UNIT("112")
            UNIT("128") UNIT("144") UNIT("160") UNIT("176")
            "dec %%rsi\n"
            "jnz 3b\n"
            "dec %[reps]\n"
            "jnz 2b\n"
            : [reps] "+r" (reps)
            : [a] "r" (acc), [b] "r" (bsrc), [iv] "r" (inv)
            : "rsi","xmm0","xmm1","xmm2","xmm3","xmm4","xmm5","memory","cc");
    }
    long long x = 0; for (int i = 0; i < 32; i++) x ^= acc[i];
    printf("%lld\n", x);
    return 0;
}
