/* C port of progs/p6_branch_match.rs — identical kernel, for the gcc/clang baseline.
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
    uint64_t s = bb(88172645463325252ull), acc = bb(0ull), n = bb(200000000ull);
    for (uint64_t i = 0; i < n; i++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        switch (s % 7) {
            case 0: acc = acc + s; break;
            case 1: acc = acc ^ s; break;
            case 2: acc = acc * (s | 1ull); break;
            case 3: acc = rotl64(acc, (unsigned)(s & 63ull)); break;
            case 4: acc = acc - (s >> 5); break;
            case 5: acc = acc + (s >> (s & 31ull)); break;
            default: acc = acc + (s ^ (acc >> 11)); break;
        }
    }
    exit((int)(acc % 126));
}
