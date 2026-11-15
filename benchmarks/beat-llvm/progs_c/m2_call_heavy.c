/* C port of progs/m2_call_heavy.rs — identical kernel, for the gcc/clang baseline.
   `bb()` mirrors std::hint::black_box (empty asm barrier). Rust u64 wrapping
   arithmetic is C unsigned arithmetic: same bits, both DEFINED. `rotl64` masks
   the amount and special-cases 0, because Rust rotate_left(0) is the identity
   while a C shift by 64 is UB. */
#include <stdint.h>
#include <stdlib.h>
#include <stddef.h>
static inline uint64_t bb(uint64_t v) { __asm__ volatile("" : "+r"(v)); return v; }
static inline uint64_t rotl64(uint64_t x, unsigned n) { n &= 63u; return n ? ((x << n) | (x >> (64u - n))) : x; }
__attribute__((noinline)) static uint64_t step(uint64_t s) {
    s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s;
}
__attribute__((noinline)) static uint64_t mix(uint64_t a, uint64_t b) {
    return (a * (b | 1ull)) ^ (a >> 11);
}
int main(void) {
    uint64_t n = bb(40000000ull), s = bb(0x243F6A8885A308D3ull), acc = bb(7ull);
    for (uint64_t i = 0; i < n; i++) { s = step(s); acc = mix(acc, s); }
    exit((int)(acc % 126));
}
