#include <stdint.h>
#include <stdio.h>

uint64_t reordered_pair(uint8_t byte, uint64_t wide);

static uint64_t rotl(uint64_t x, unsigned r) { return r ? (x << r) | (x >> (64 - r)) : x; }

/* Independent oracle of reordered.rs: mutate_pair, then consume_pair. */
static uint64_t oracle(uint8_t byte, uint64_t wide) {
    uint8_t b = (uint8_t)(byte + 37);
    uint64_t w = rotl(wide, 13) ^ 0xa75860b15d9c3e2full;
    return w ^ ((uint64_t)b * 0x0101010101010101ull);
}

int main(void) {
    static const uint64_t wides[] = {0, 1, 0x8000000000000000ull, ~0ull, 0x0123456789abcdefull,
                                     0xfedcba9876543210ull, 0x5555555555555555ull,
                                     0xaaaaaaaaaaaaaaaaull};
    unsigned long checks = 0;
    for (unsigned b = 0; b < 256; b++) {
        for (unsigned i = 0; i < sizeof wides / sizeof wides[0]; i++) {
            for (unsigned s = 0; s < 64; s++) {
                uint64_t w = rotl(wides[i], s) ^ (uint64_t)s * 0x9e3779b97f4a7c15ull;
                uint64_t got = reordered_pair((uint8_t)b, w), want = oracle((uint8_t)b, w);
                if (got != want) {
                    printf("MISMATCH b=%u w=%016llx got=%016llx want=%016llx\n", b,
                           (unsigned long long)w, (unsigned long long)got,
                           (unsigned long long)want);
                    return 1;
                }
                checks++;
            }
        }
    }
    printf("PASS reordered_pair checks=%lu\n", checks);
    return 0;
}
