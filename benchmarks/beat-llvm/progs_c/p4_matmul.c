/* C port of progs/p4_matmul.rs — identical kernel, for the gcc/clang baseline.
   `bb()` mirrors std::hint::black_box. Rust's wrapping_* on i64 is modelled with
   uint64_t arithmetic — same bits, and signed overflow is UB in C where Rust
   DEFINES the wrap. `c` is re-zeroed per rep exactly as the Rust `let mut c` is. */
#include <stdint.h>
#include <stdlib.h>
#include <stddef.h>
static inline uint64_t bb(uint64_t v) { __asm__ volatile("" : "+r"(v)); return v; }
#define N 24
int main(void) {
    uint64_t seed = bb(3ull);
    uint64_t a[N * N], b[N * N];
    for (size_t i = 0; i < N * N; i++) {
        a[i] = ((uint64_t)i * seed + 7ull) % 100ull;
        b[i] = ((uint64_t)i * (seed + 11ull) + 3ull) % 100ull;
    }
    uint32_t reps = (uint32_t)bb(20000ull);
    uint64_t acc = 0;
    for (uint32_t r = 0; r < reps; r++) {
        uint64_t c[N * N];
        for (size_t i = 0; i < N * N; i++) c[i] = 0;
        for (size_t i = 0; i < N; i++)
            for (size_t k = 0; k < N; k++) {
                uint64_t aik = a[i * N + k];
                for (size_t j = 0; j < N; j++)
                    c[i * N + j] = c[i * N + j] + aik * b[k * N + j];
            }
        acc = acc + c[((size_t)r * 37u) % (N * N)];
        a[((size_t)r * 13u) % (N * N)] = acc & 0xFFull;
    }
    exit((int)(acc % 126));
}
