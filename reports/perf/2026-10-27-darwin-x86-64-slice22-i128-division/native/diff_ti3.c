// Slice-22 design: a native differential of the four 128-bit division routines
// the x86-64 selector calls (__udivti3, __umodti3, __divti3, __modti3) against
// an INDEPENDENT reference of trust-ir's semantics (interpret.rs at the pin:
// UDiv/URem floor and modulo, UB for a zero divisor; SDiv/SRem truncate
// toward zero, the remainder takes the dividend's sign, UB for a zero divisor
// and for MIN / -1).
//
// The reference uses no 128-bit division (and so no __udivti3: trust-ir's own
// interpreter computes `lhs.raw / rhs.raw` on u128, which LLVM lowers to the
// very routine under test, so it is no independent reference): bit-serial
// restoring division over two uint64 halves, then signs by magnitude.
//
// The routine under test is whichever the LINK binds: built with `cc` alone,
// libSystem's (macOS compiler-rt); linked with the Trust sysroot's
// compiler_builtins rlib first, Rust's (its weak definitions win over the
// dylib's, as in every Rust binary). `run_diff.sh` builds both and checks the
// binding with `nm`/`otool`.
//
// Inputs: every pair from an edge set (0, 1, 2, 3, 7, 10, 10^16, 10^19, 2^k-1,
// 2^k, 2^k+1 for k in {31,32,63,64,65,96,126,127}, MAX, MIN, -1, -2, MIN+1,
// and their negations), then N random pairs drawn per (dividend bit length,
// divisor bit length) class, including divisors below 2^64 (the asymmetric
// algorithm's one-`div` path), equal lengths, and q*d + r constructions with r
// at 0, 1, d-1. Only trust-ir's defined domain is compared; the undefined
// inputs (zero divisor; MIN / -1) are counted and skipped.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned __int128 u128;
typedef __int128 i128;

#ifdef CB_LINK
// compiler_builtins' objects name Rust's EH personality in their unwind
// tables; the harness never unwinds, so a stub that aborts satisfies the link.
void rust_eh_personality(void) { abort(); }
#endif

u128 __udivti3(u128, u128);
u128 __umodti3(u128, u128);
i128 __divti3(i128, i128);
i128 __modti3(i128, i128);

// The volatile function pointers keep the compiler from folding a call.
#ifdef MUTANT
// Control: a wrong routine (the quotient's low bit flipped when the divisor has
// a high half) must be reported, or the harness checks nothing.
static u128 bad_udiv(u128 a, u128 b) { return __udivti3(a, b) ^ (u128)((b >> 64) != 0); }
static u128 (*volatile UDIV)(u128, u128) = bad_udiv;
#else
static u128 (*volatile UDIV)(u128, u128) = __udivti3;
#endif
static u128 (*volatile UMOD)(u128, u128) = __umodti3;
static i128 (*volatile SDIV)(i128, i128) = __divti3;
static i128 (*volatile SMOD)(i128, i128) = __modti3;

// Bit-serial restoring division: q = n / d, r = n % d, d != 0. Shifts,
// compares and subtracts of u128 only (inline on x86-64, no runtime call).
static void ref_udivrem(u128 n, u128 d, u128 *q, u128 *r) {
    u128 qq = 0, rr = 0;
    for (int i = 127; i >= 0; i--) {
        rr = (rr << 1) | ((n >> i) & 1);
        if (rr >= d) {
            rr -= d;
            qq |= (u128)1 << i;
        }
    }
    *q = qq;
    *r = rr;
}

static const i128 IMIN = (i128)((u128)1 << 127);

static int ref_sdivrem(i128 a, i128 b, i128 *q, i128 *r) {
    if (b == 0 || (a == IMIN && b == -1)) return 0; // undefined in trust-ir
    u128 ua = a < 0 ? (u128)0 - (u128)a : (u128)a;
    u128 ub = b < 0 ? (u128)0 - (u128)b : (u128)b;
    u128 uq, ur;
    ref_udivrem(ua, ub, &uq, &ur);
    *q = ((a < 0) != (b < 0)) ? (i128)((u128)0 - uq) : (i128)uq;
    *r = (a < 0) ? (i128)((u128)0 - ur) : (i128)ur;
    return 1;
}

static uint64_t s[2] = {0x9E3779B97F4A7C15ULL, 0xD1B54A32D192ED03ULL};
static uint64_t rnd(void) { // xoroshiro128+
    uint64_t s0 = s[0], s1 = s[1], r = s0 + s1;
    s1 ^= s0;
    s[0] = ((s0 << 24) | (s0 >> 40)) ^ s1 ^ (s1 << 16);
    s[1] = (s1 << 37) | (s1 >> 27);
    return r;
}
static u128 rnd_bits(int bits) { // a value of exactly `bits` significant bits (0 = zero)
    if (bits == 0) return 0;
    u128 v = ((u128)rnd() << 64) | rnd();
    if (bits < 128) v &= ((u128)1 << bits) - 1;
    v |= (u128)1 << (bits - 1);
    return v;
}

static unsigned long long checked, undefined_skipped, bad;
static void hex(u128 v, char *out) {
    sprintf(out, "%016llx%016llx", (unsigned long long)(v >> 64), (unsigned long long)v);
}
static void report(const char *op, u128 a, u128 b, u128 got, u128 want) {
    if (bad++ < 20) {
        char x[40], y[40], g[40], w[40];
        hex(a, x); hex(b, y); hex(got, g); hex(want, w);
        printf("MISMATCH %s a=%s b=%s got=%s want=%s\n", op, x, y, g, w);
    }
}

static void one(u128 a, u128 b) {
    if (b == 0) {
        undefined_skipped += 4;
    } else {
        u128 q, r;
        ref_udivrem(a, b, &q, &r);
        u128 gq = UDIV(a, b), gr = UMOD(a, b);
        if (gq != q) report("udivti3", a, b, gq, q);
        if (gr != r) report("umodti3", a, b, gr, r);
        checked += 2;
    }
    i128 sq, sr;
    if (ref_sdivrem((i128)a, (i128)b, &sq, &sr)) {
        i128 gq = SDIV((i128)a, (i128)b), gr = SMOD((i128)a, (i128)b);
        if (gq != sq) report("divti3", a, b, (u128)gq, (u128)sq);
        if (gr != sr) report("modti3", a, b, (u128)gr, (u128)sr);
        checked += 2;
    } else if (b != 0) {
        undefined_skipped += 2;
    }
}

int main(int argc, char **argv) {
    long n = argc > 1 ? atol(argv[1]) : 2000;
    u128 edge[256];
    int ne = 0;
    const int ks[] = {31, 32, 63, 64, 65, 96, 126, 127};
    const u128 small[] = {0, 1, 2, 3, 7, 10, (u128)10000000000000000ULL, (u128)10000000000000000000ULL};
    for (unsigned i = 0; i < sizeof small / sizeof *small; i++) edge[ne++] = small[i];
    for (unsigned i = 0; i < sizeof ks / sizeof *ks; i++) {
        u128 p = (u128)1 << ks[i];
        edge[ne++] = p - 1; edge[ne++] = p; edge[ne++] = p + 1;
    }
    edge[ne++] = ~(u128)0;           // MAX (unsigned), -1 (signed)
    edge[ne++] = ~(u128)0 - 1;       // -2
    edge[ne++] = (u128)IMIN;         // MIN
    edge[ne++] = (u128)IMIN + 1;     // MIN + 1
    edge[ne++] = (u128)IMIN - 1;     // i128::MAX
    int base = ne;
    for (int i = 0; i < base; i++) edge[ne++] = (u128)0 - edge[i]; // negations
    for (int i = 0; i < ne; i++)
        for (int j = 0; j < ne; j++) one(edge[i], edge[j]);
    unsigned long long edge_checked = checked;
    // random classes: every (dividend bits, divisor bits) pair on a grid of lengths
    const int lens[] = {0, 1, 2, 8, 31, 32, 33, 63, 64, 65, 96, 127, 128};
    const int nl = sizeof lens / sizeof *lens;
    for (int i = 0; i < nl; i++)
        for (int j = 0; j < nl; j++)
            for (long k = 0; k < n; k++) one(rnd_bits(lens[i]), rnd_bits(lens[j]));
    // q*d + r with r at the boundaries (r = 0, 1, d-1) for random q, d without overflow
    for (long k = 0; k < 13 * n; k++) {
        int dl = 1 + (int)(rnd() % 127);
        u128 d = rnd_bits(dl);
        int ql = (int)(rnd() % (129 - dl));
        u128 q = rnd_bits(ql);
        u128 base_v = q * d; // no overflow: bits(q) + bits(d) <= 128
        u128 rs[3] = {0, 1, d - 1};
        for (int t = 0; t < 3; t++) {
            u128 v = base_v + rs[t];
            if (v < base_v) continue;
            one(v, d);
        }
    }
    printf("edge pairs %d x %d: %llu checks; total checks %llu; undefined (skipped) %llu; mismatches %llu\n",
           ne, ne, edge_checked, checked, undefined_skipped, bad);
    return bad != 0;
}
