#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern uint64_t projected_cursor(const unsigned char *, uintptr_t);
extern uint64_t shared_cursor(const unsigned char *, uintptr_t);
extern uint64_t nested_cursor(const unsigned char *, uintptr_t, uint64_t);
extern uint64_t reordered_pair(uint8_t, uint64_t);

static unsigned checks;
static uint64_t rol(uint64_t x, unsigned n) { return (x << n) | (x >> (64 - n)); }
static void check(uint64_t actual, uint64_t expected, const char *label, unsigned i) {
    ++checks;
    if (actual != expected) {
        fprintf(stderr, "%s iteration=%u actual=%llx expected=%llx\n", label, i,
                (unsigned long long)actual, (unsigned long long)expected);
        exit(1);
    }
}
int main(void) {
    unsigned char bytes[64];
    for (unsigned i = 0; i < 4096; ++i) {
        uint64_t seed = (uint64_t)i * UINT64_C(0x9e3779b97f4a7c15);
        for (unsigned j = 0; j < sizeof(bytes); ++j)
            bytes[j] = (unsigned char)((seed >> (8 * (j % 8))) ^ (j * 71));
        for (unsigned len = 2; len <= 33; ++len) {
            const unsigned char *data = bytes + (i % 31);
            uint64_t advanced = data[0] | ((uint64_t)data[1] << 8) | ((uint64_t)(len - 1) << 16);
            uint64_t shared = data[0] | ((uint64_t)data[0] << 8) | ((uint64_t)len << 16);
            check(projected_cursor(data, len), advanced, "mutable projected cursor", i);
            check(shared_cursor(data, len), shared, "shared projected cursor", i);
            check(nested_cursor(data, len, seed), advanced ^ seed ^ rol(seed, 17), "nested cursor", i);
            uint8_t byte = (uint8_t)(i + len);
            uint64_t wide = seed ^ len;
            uint64_t expected = rol(wide, 13) ^ UINT64_C(0xa75860b15d9c3e2f)
                ^ ((uint64_t)(uint8_t)(byte + 37) * UINT64_C(0x0101010101010101)) ^ UINT64_C(0xdeadbeef00000000);
            check(reordered_pair(byte, wide), expected, "reordered pair", i);
        }
    }
    if (checks != 524288) return 1;
    printf("PASS projected_aggregate_borrows checks=%u\n", checks);
    return 0;
}
