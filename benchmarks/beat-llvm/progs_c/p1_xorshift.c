/* C port of progs/p1_xorshift.rs — identical kernel, for the gcc baseline.
   `bb()` mirrors Rust's std::hint::black_box: an empty asm barrier that
   forces the value into a register and blocks constant folding. */
#include <stdint.h>
#include <stdlib.h>
static inline uint64_t bb(uint64_t v) { __asm__ volatile("" : "+r"(v)); return v; }
int main(void) {
    uint64_t x = bb(0x243F6A8885A308D3ull);
    uint64_t acc = 0;
    uint64_t n = bb(400000000ull);
    for (uint64_t i = 0; i < n; i++) {
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        acc += x;
    }
    exit((int)(acc % 126));
}
