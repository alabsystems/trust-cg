/* C port of progs/v2_memfill.rs — identical kernel. See v1_saxpy.c for `bb`. */
#include <stdint.h>
#include <stdlib.h>
#include <stddef.h>
static inline uint32_t bb32(uint32_t v) { __asm__ volatile("" : "+r"(v)); return v; }
static inline uint64_t bb64(uint64_t v) { __asm__ volatile("" : "+r"(v)); return v; }
#define N 8192
int main(void) {
    uint32_t reps = bb32(100000u);
    uint8_t a[N];
    for (size_t i = 0; i < N; i++) a[i] = 0;
    uint64_t acc = 0;
    for (uint32_t r = 0; r < reps; r++) {
        uint8_t v = (uint8_t)((uint8_t)r | 1u);
        for (size_t i = 0; i < N; i++) a[i] = v;
        size_t idx = (size_t)bb64((uint64_t)((size_t)r * 31u)) % N;
        acc += (uint64_t)a[idx];
    }
    exit((int)(acc % 126));
}
