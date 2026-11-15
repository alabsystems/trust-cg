/* C port of progs/p2_collatz.rs — identical kernel and constants. */
#include <stdint.h>
#include <stdlib.h>
static inline uint64_t bb(uint64_t v) { __asm__ volatile("" : "+r"(v)); return v; }
int main(void) {
    uint64_t lim = bb(2000000ull);
    uint64_t total = 0;
    for (uint64_t n = 1; n < lim; n++) {
        uint64_t c = n, steps = 0;
        while (c != 1) {
            if ((c & 1) == 0) c >>= 1; else c = c * 3 + 1;
            steps++;
        }
        total += steps;
    }
    exit((int)(total % 126));
}
