/* C port of progs/p7_sieve.rs — identical kernel, constants, and array size. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
static inline uint64_t bb64(uint64_t v) { __asm__ volatile("" : "+r"(v)); return v; }
#define M 1024
int main(void) {
    uint32_t reps = (uint32_t)bb64(60000ull);
    uint64_t total = 0;
    for (uint32_t r = 0; r < reps; r++) {
        unsigned char comp[M];
        memset(comp, 0, M);
        size_t start = 2 + ((size_t)r % 3);
        for (size_t p = 2; p * p < M; p++) {
            if (comp[p] == 0) { for (size_t q = p * p; q < M; q += p) comp[q] = 1; }
        }
        uint64_t count = 0;
        for (size_t i = start; i < M; i++) if (comp[i] == 0) count++;
        total += count;
    }
    exit((int)(total % 126));
}
