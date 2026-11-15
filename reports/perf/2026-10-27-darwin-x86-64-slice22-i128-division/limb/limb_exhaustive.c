// Slice-22 design: the 128-bit product spellings, checked EXHAUSTIVELY at the
// analogous small widths (n-bit halves, 2n-bit product, n = 1..8), with every
// operand pair. Each spelling is the one mk_mulu128.py / smtq22.py write at
// n = 64; the identities are width-generic (only "mod 2^n" and "mod 2^2n"
// appear), so a check at every small n is the s19 practice for identity groups.
//
//   S0   (A*B) mod 2^2n                                   the source's bvmul
//   L128 (aL*bL + ((aH*bL + aL*bH) mod 2^2n) << n) mod 2^2n   cross products 2n-bit, bvshl
//   L64  (aL*bL + ((aH*bL + aL*bH) mod 2^n) * 2^n) mod 2^2n   cross products n-bit, concat
//   HI   high half of S0 == (mulhi(aL,bL) + aH*bL + aL*bH) mod 2^n   (addhi0 applied)
//   LO   low half of S0  == (aL*bL) mod 2^n                          (mullo)
//   ADDHI0 extract[2n-1:n](P + concat(X, 0_n)) == (P_hi + X) mod 2^n, every P (2n bits), X (n bits)
//
// build: cc -O2 -o limb_exhaustive limb_exhaustive.c ; run: ./limb_exhaustive
#include <stdint.h>
#include <stdio.h>

int main(void) {
    int bad = 0;
    for (int n = 1; n <= 8; n++) {
        const uint64_t W = 2 * n;
        const uint64_t mn = (1ULL << n) - 1, m2n = (1ULL << W) - 1;
        uint64_t count = 0, fails = 0;
        for (uint64_t A = 0; A <= m2n; A++) {
            const uint64_t aL = A & mn, aH = A >> n;
            for (uint64_t B = 0; B <= m2n; B++) {
                const uint64_t bL = B & mn, bH = B >> n;
                const uint64_t s0 = (A * B) & m2n;
                const uint64_t p = (aL * bL) & m2n; // zext * zext at 2n bits
                const uint64_t l128 = (p + ((((aH * bL) + (aL * bH)) & m2n) << n)) & m2n;
                const uint64_t l64 = (p + ((((aH * bL) + (aL * bH)) & mn) << n)) & m2n;
                const uint64_t hi = ((p >> n) + aH * bL + aL * bH) & mn;
                const uint64_t lo = (aL * bL) & mn;
                count++;
                if (s0 != l128 || s0 != l64 || (s0 >> n) != hi || (s0 & mn) != lo) {
                    if (fails++ < 3)
                        printf("n=%d A=%llu B=%llu s0=%llu l128=%llu l64=%llu\n", n,
                               (unsigned long long)A, (unsigned long long)B, (unsigned long long)s0,
                               (unsigned long long)l128, (unsigned long long)l64);
                }
            }
        }
        uint64_t c2 = 0, f2 = 0;
        for (uint64_t P = 0; P <= m2n; P++)
            for (uint64_t X = 0; X <= mn; X++) {
                const uint64_t lhs = (((P + (X << n)) & m2n) >> n);
                const uint64_t rhs = ((P >> n) + X) & mn;
                c2++;
                if (lhs != rhs) f2++;
            }
        printf("n=%d (product %llu bits): products %llu pairs, %llu mismatches; addhi0 %llu pairs, %llu mismatches\n",
               n, (unsigned long long)W, (unsigned long long)count, (unsigned long long)fails,
               (unsigned long long)c2, (unsigned long long)f2);
        bad += (fails != 0) + (f2 != 0);
    }
    printf(bad ? "FAIL\n" : "ALL EXACT\n");
    return bad != 0;
}
