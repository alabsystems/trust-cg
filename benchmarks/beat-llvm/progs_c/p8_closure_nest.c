/* C port of progs/p8_closure_nest.rs — identical kernel, for the gcc/clang baseline.
   `bb()` mirrors std::hint::black_box (empty asm barrier). Rust u64 wrapping
   arithmetic is C unsigned arithmetic: same bits, both DEFINED. `rotl64` masks
   the amount and special-cases 0, because Rust rotate_left(0) is the identity
   while a C shift by 64 is UB. */
#include <stdint.h>
#include <stdlib.h>
#include <stddef.h>
static inline uint64_t bb(uint64_t v) { __asm__ volatile("" : "+r"(v)); return v; }
static inline uint64_t rotl64(uint64_t x, unsigned n) { n &= 63u; return n ? ((x << n) | (x >> (64u - n))) : x; }
static inline uint64_t stepc(uint64_t x, uint64_t y, uint64_t k) {
    return (x * (k | 1ull)) + (y ^ (x >> 9));
}
int main(void) {
    uint64_t k = bb(17ull), n = bb(20000ull), m = bb(10000ull), acc = bb(5ull);
    for (uint64_t i = 0; i < n; i++)
        for (uint64_t j = 0; j < m; j++) acc = stepc(acc, i * j, k);
    exit((int)(acc % 126));
}
