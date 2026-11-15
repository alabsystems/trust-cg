#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern uint8_t *nonnull_cursor(uint8_t *, uintptr_t);
extern uint64_t nonnull_sum(uint64_t *, uintptr_t);
extern uint8_t *raw_write(uint8_t *, uintptr_t);
extern uint64_t raw_reverse(const uint16_t *, uintptr_t);
extern uint8_t *wrapper_whole(uint8_t *, uintptr_t);
extern uint8_t *wrapper_field(uint8_t *, uintptr_t);
extern uintptr_t slice_tail(const uint8_t *, uintptr_t, uintptr_t);

#define CHECK(expr) do { \
    if (!(expr)) { \
        fprintf(stderr, "%s start=%u n=%u\n", #expr, start, n); \
        return 1; \
    } \
    checks++; \
} while (0)

int main(void) {
    unsigned checks = 0;
    for (unsigned start = 0; start < 17; start++) {
        for (unsigned n = 0; n < 65; n++) {
            uint8_t bytes[256], expected[256];
            uint16_t halves[256];
            uint64_t words[256];
            for (unsigned j = 0; j < 256; j++) {
                bytes[j] = (uint8_t)(j * 19 + 13);
                halves[j] = (uint16_t)(j * 251 + 37);
                words[j] = UINT64_C(0xfedcba9876543210) * j + 71;
            }
            CHECK(nonnull_cursor(bytes + start, n) == bytes + start + n);
            CHECK(wrapper_whole(bytes + start, n) == bytes + start + n);
            CHECK(wrapper_field(bytes + start, n) == bytes + start + n);
            uint64_t sum = 0;
            for (unsigned j = 0; j < n; j++) sum += words[start + j];
            CHECK(nonnull_sum(words + start, n) == sum);
            sum = 0;
            for (unsigned j = 0; j < n; j++) sum += halves[start + n - j - 1];
            CHECK(raw_reverse(halves + start + n, n) == sum);
            CHECK(slice_tail(bytes + start, 200, n) == (200 - n) * 257 + bytes[start + n]);
            memcpy(expected, bytes, sizeof(bytes));
            unsigned offset = start;
            for (unsigned j = 0; j < n; j++) {
                expected[offset] = (uint8_t)(j * 7);
                offset += 1 + (j & 1);
            }
            CHECK(raw_write(bytes + start, n) == bytes + offset);
            CHECK(memcmp(bytes, expected, sizeof(bytes)) == 0);
        }
    }
    if (checks != 8840) return 2;
    printf("PASS thin_pointer_loops checks=%u\n", checks);
    return 0;
}
