/* C port of progs/p5_struct_acc.rs — identical kernel and constants. */
#include <stdint.h>
#include <stdlib.h>
static inline uint64_t bb(uint64_t v) { __asm__ volatile("" : "+r"(v)); return v; }
static inline uint64_t rotl64(uint64_t v, unsigned k) { return (v << k) | (v >> (64 - k)); }
struct St { uint64_t a, b, c; };
int main(void) {
    struct St st = { bb(1ull), bb(2ull), bb(3ull) };
    uint64_t n = bb(300000000ull);
    for (uint64_t i = 0; i < n; i++) {
        st.a = st.a * 31 + (st.c ^ i);
        st.b = st.b + (st.a >> 3);
        st.c = st.c ^ rotl64(st.b * 7, 9);
    }
    exit((int)((st.a ^ st.b ^ st.c) % 126));
}
