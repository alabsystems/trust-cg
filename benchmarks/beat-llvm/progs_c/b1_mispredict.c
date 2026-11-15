/* C port of progs/b1_mispredict.rs — identical kernel, for the gcc/clang baseline.
   `bb()` mirrors std::hint::black_box (empty asm barrier). Rust u64 wrapping
   arithmetic is C unsigned arithmetic: same bits, both DEFINED. `rotl64` masks
   the amount and special-cases 0, because Rust rotate_left(0) is the identity
   while a C shift by 64 is UB. */
#include <stdint.h>
#include <stdlib.h>
#include <stddef.h>
static inline uint64_t bb(uint64_t v) { __asm__ volatile("" : "+r"(v)); return v; }
static inline uint64_t rotl64(uint64_t x, unsigned n) { n &= 63u; return n ? ((x << n) | (x >> (64u - n))) : x; }
int main(void) {
    uint64_t n = bb(60000000ull), s = bb(0x9E3779B97F4A7C15ull), t[16] = {0}, acc = 0;
    for (uint64_t i = 0; i < n; i++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        if ((s & 1ull) == 0) {
            acc = acc + (s >> 3);
            t[(size_t)((s >> 4) & 15ull)] ^= s;
        } else {
            acc ^= s * 0x2545F4914F6CDD1Dull;
            size_t j = (size_t)((s >> 8) & 15ull);
            t[j] = t[j] + acc;
        }
        if ((s & 6ull) == 2ull) acc = rotl64(acc, 7);
    }
    for (size_t k = 0; k < 16; k++) acc = acc + t[k];
    exit((int)(acc % 126));
}
