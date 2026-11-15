/* C port of progs/v3_popcount.rs — identical kernel. `__builtin_popcount` is
   the faithful equivalent of Rust's `u32::count_ones`. See v1_saxpy.c. */
#include <stdint.h>
#include <stdlib.h>
#include <stddef.h>
static inline uint32_t bb32(uint32_t v) { __asm__ volatile("" : "+r"(v)); return v; }
static inline uint64_t bb64(uint64_t v) { __asm__ volatile("" : "+r"(v)); return v; }
#define N 4096
int main(void) {
    uint64_t x = bb64(0x243F6A8885A308D3ull);
    uint8_t a[N];
    for (size_t i = 0; i < N; i++) {
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        a[i] = (uint8_t)(x & 0xFFu);
    }
    uint32_t reps = bb32(60000u);
    uint64_t acc = 0;
    for (uint32_t r = 0; r < reps; r++) {
        for (size_t i = 0; i < N; i++) acc += (uint64_t)__builtin_popcount((uint32_t)a[i]);
        a[(size_t)(r % N)] = (uint8_t)(acc & 0xFFu);
    }
    exit((int)(acc % 126));
}
