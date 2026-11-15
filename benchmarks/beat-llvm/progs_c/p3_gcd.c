/* C port of progs/p3_gcd.rs — identical kernel and constants. */
#include <stdint.h>
#include <stdlib.h>
static inline uint64_t bb(uint64_t v) { __asm__ volatile("" : "+r"(v)); return v; }
static uint64_t gcd(uint64_t a, uint64_t b) {
    while (b != 0) { uint64_t t = a % b; a = b; b = t; }
    return a;
}
int main(void) {
    uint64_t s = bb(0x9E3779B97F4A7C15ull), acc = 0, n = bb(4000000ull);
    for (uint64_t i = 0; i < n; i++) {
        s = s * 6364136223846793005ull + 1442695040888963407ull;
        uint64_t a = (s >> 16) | 1;
        s = s * 6364136223846793005ull + 1442695040888963407ull;
        uint64_t b = (s >> 16) | 1;
        acc += gcd(a, b);
    }
    exit((int)(acc % 126));
}
