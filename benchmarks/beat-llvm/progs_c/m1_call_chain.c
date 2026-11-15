/* C port of progs/m1_call_chain.rs — identical kernel, for the gcc/clang baseline.
   `bb()` mirrors std::hint::black_box (empty asm barrier). Rust u64 wrapping
   arithmetic is C unsigned arithmetic: same bits, both DEFINED. `rotl64` masks
   the amount and special-cases 0, because Rust rotate_left(0) is the identity
   while a C shift by 64 is UB. */
#include <stdint.h>
#include <stdlib.h>
#include <stddef.h>
static inline uint64_t bb(uint64_t v) { __asm__ volatile("" : "+r"(v)); return v; }
static inline uint64_t rotl64(uint64_t x, unsigned n) { n &= 63u; return n ? ((x << n) | (x >> (64u - n))) : x; }
static uint64_t f4(uint64_t x) { return x ^ (x << 9); }
static uint64_t f3(uint64_t x, uint64_t k) { return rotl64(f4(x + k), 5); }
static uint64_t f2(uint64_t x, uint64_t k) { return f3(x ^ (x >> 7), k) * 3ull; }
static uint64_t f1(uint64_t x, uint64_t k) { return f2(x * (k | 1ull), k) + 1ull; }
int main(void) {
    uint64_t k = bb(0x2545F4914F6CDD1Dull), n = bb(30000000ull), acc = bb(1ull);
    for (uint64_t i = 0; i < n; i++) acc = f1(acc ^ i, k);
    exit((int)(acc % 126));
}
