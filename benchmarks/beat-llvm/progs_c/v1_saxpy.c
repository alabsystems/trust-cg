/* C port of progs/v1_saxpy.rs — identical kernel, for the gcc/clang baseline.
   `bb()` mirrors Rust's std::hint::black_box: an empty asm barrier that forces
   the value into a register and blocks constant folding. Rust's wrapping_* on
   i32 is modelled with uint32_t arithmetic: same bit pattern, and signed
   overflow would be UB in C where it is DEFINED in Rust. */
#include <stdint.h>
#include <stdlib.h>
#include <stddef.h>
static inline uint32_t bb32(uint32_t v) { __asm__ volatile("" : "+r"(v)); return v; }
#define N 4096
int main(void) {
    uint32_t k = bb32(3u);
    uint32_t a[N], b[N];
    for (size_t i = 0; i < N; i++) {
        a[i] = (uint32_t)i * 7u + 1u;
        b[i] = (uint32_t)i * 13u - 5u;
    }
    uint32_t reps = bb32(200000u);
    uint64_t acc = 0;
    for (uint32_t r = 0; r < reps; r++) {
        for (size_t i = 0; i < N; i++) a[i] = a[i] * k + b[i];
        acc += (uint64_t)a[((size_t)r * 61u) % N];
    }
    exit((int)(acc % 126));
}
