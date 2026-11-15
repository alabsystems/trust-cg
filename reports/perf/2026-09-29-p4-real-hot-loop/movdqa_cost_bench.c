// Does a redundant MOVDQA reg-reg cost time on this host?
//
// Both variants run the SAME SSE2 64x64 multiply-accumulate unit that p4_matmul's
// vector loop runs (3 pmuludq + psrlq + psllq + 3 paddq + a load/store pair), with
// `b` reloaded every iteration exactly as the real loop does. They differ ONLY in
// how many MOVDQA register copies preserve a live operand:
//
//   A (what trust-cg emits): 4 copies -- it copies the loop-INVARIANT aik lo/hi on
//     every use, and copies b again to build b>>32.
//   B (what LLVM emits):     2 copies -- it ties each product to the dying `b` and
//     shifts b IN PLACE at its last use.
//
// So B - A isolates exactly 2 MOVDQA per unit, which is p4's per-unit difference
// (~1.75). If A and B time the same, MOVDQA is renamer-eliminated on this core and
// extending the two-address commuted tie to XMM cannot pay.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static long long acc[2] __attribute__((aligned(16)));
static long long bsrc[2] __attribute__((aligned(16)));
static long long inv[4] __attribute__((aligned(16)));

int main(int argc, char **argv) {
    long n = atol(argv[1]);
    int variant = atoi(argv[2]);
    bsrc[0] = 0x1122334455667788LL; bsrc[1] = 0x99aabbccddeeff00LL;
    inv[0] = 0x0f0f0f0f0f0f0f0fLL;  inv[1] = 0x1111111111111111LL;
    inv[2] = 0x2222222222222222LL;  inv[3] = 0x3333333333333333LL;
    acc[0] = 0; acc[1] = 0;

    if (variant == 0) {
        __asm__ volatile (
            "movdqa (%[iv]), %%xmm4\n"
            "movdqa 16(%[iv]), %%xmm5\n"
            "1:\n"
            "movdqu (%[b]), %%xmm1\n"
            "movdqa %%xmm4, %%xmm3\n"        /* copy invariant */
            "pmuludq %%xmm1, %%xmm3\n"
            "movdqa %%xmm1, %%xmm0\n"        /* copy b to shift it */
            "psrlq $32, %%xmm0\n"
            "movdqa %%xmm4, %%xmm2\n"        /* copy invariant again */
            "pmuludq %%xmm0, %%xmm2\n"
            "movdqa %%xmm5, %%xmm0\n"        /* and again */
            "pmuludq %%xmm1, %%xmm0\n"
            "paddq %%xmm0, %%xmm2\n"
            "psllq $32, %%xmm2\n"
            "paddq %%xmm2, %%xmm3\n"
            "movdqu (%[a]), %%xmm0\n"
            "paddq %%xmm3, %%xmm0\n"
            "movdqu %%xmm0, (%[a])\n"
            "dec %[n]\n"
            "jnz 1b\n"
            : [n] "+r" (n)
            : [a] "r" (acc), [b] "r" (bsrc), [iv] "r" (inv)
            : "xmm0","xmm1","xmm2","xmm3","xmm4","xmm5","memory","cc");
    } else {
        __asm__ volatile (
            "movdqa (%[iv]), %%xmm4\n"
            "movdqa 16(%[iv]), %%xmm5\n"
            "1:\n"
            "movdqu (%[b]), %%xmm1\n"
            "movdqa %%xmm1, %%xmm3\n"        /* tie to the DYING b */
            "pmuludq %%xmm4, %%xmm3\n"
            "movdqa %%xmm1, %%xmm2\n"        /* tie to the dying b */
            "pmuludq %%xmm5, %%xmm2\n"
            "psrlq $32, %%xmm1\n"            /* shift b IN PLACE at its last use */
            "pmuludq %%xmm4, %%xmm1\n"
            "paddq %%xmm2, %%xmm1\n"
            "psllq $32, %%xmm1\n"
            "paddq %%xmm1, %%xmm3\n"
            "movdqu (%[a]), %%xmm0\n"
            "paddq %%xmm3, %%xmm0\n"
            "movdqu %%xmm0, (%[a])\n"
            "dec %[n]\n"
            "jnz 1b\n"
            : [n] "+r" (n)
            : [a] "r" (acc), [b] "r" (bsrc), [iv] "r" (inv)
            : "xmm0","xmm1","xmm2","xmm3","xmm4","xmm5","memory","cc");
    }
    printf("%lld\n", acc[0] ^ acc[1]);
    return 0;
}
