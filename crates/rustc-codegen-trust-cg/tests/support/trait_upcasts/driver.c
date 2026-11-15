#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

struct Plain { uint64_t value; };
struct Biased { uint64_t value; uint64_t bias; uint64_t spare[2]; };
extern uint64_t exercise_upcasts(struct Plain *, struct Biased *, uint64_t,
                                       uint32_t, uint32_t);

int main(void) {
    const uint64_t values[] = {0, 1, 17, UINT64_C(0x1020304050607080), UINT64_MAX};
    const uint64_t salts[] = {0, 1, 2, 3, 7, 8, UINT64_C(0x8000000000000004), UINT64_MAX};
    const uint64_t biases[] = {0, 23, UINT64_C(0xfedcba9876543210)};
    uint64_t checks = 0;
    for (unsigned a = 0; a < 5; ++a) {
        for (unsigned b = 0; b < 5; ++b) {
            for (unsigned c = 0; c < 3; ++c) {
                for (unsigned s = 0; s < 8; ++s) {
                    for (uint32_t pick = 0; pick < 2; ++pick) {
                        for (uint32_t mode = 0; mode < 16; ++mode) {
                            struct { uint64_t before; struct Plain item; uint64_t after; }
                                left = {UINT64_C(0x445566778899aabb), {values[a]}, UINT64_C(0xffeeddccbbaa9988)};
                            _Alignas(16) struct {
                                uint64_t before[2]; struct Biased item; uint64_t after[2];
                            } right = {{UINT64_C(0xaabbccdd11223344), UINT64_C(0x3141592653589793)},
                                       {values[b], biases[c], {UINT64_C(0x55aa1234567890ff), UINT64_C(0xccdd987654321011)}},
                                       {UINT64_C(0x8877665544332211), UINT64_C(0x2718281828459045)}};
                            uint64_t salt = salts[s];
                            uint64_t left_expected = values[a];
                            uint64_t right_expected = values[b];
                            if (mode == 6) {
                                if (pick == 0) left_expected += salt + 19;
                                else right_expected += salt + 23;
                            }
                            uint32_t output_pick = pick;
                            if (mode == 13 && (salt & 7) != 0)
                                output_pick = (salt & 1) != 0 ? 0 : 1;
                            uint64_t value = output_pick == 0 ? left_expected : right_expected;
                            uint64_t bias = output_pick == 0 ? 0 : biases[c];
                            uint64_t expected = value * 5 + (bias ^ salt) + 17;
                            if (mode == 0) expected = value * 7 - salt;
                            if (mode == 1) expected = (value * 3) ^ salt;
                            if (mode == 3) expected = value + salt + 11;
                            if (mode == 7) expected = (uint64_t)(uintptr_t)(pick == 0
                                ? (void *)&left.item : (void *)&right.item);
                            if (mode == 8 || mode == 10) expected = pick == 0 ? 8 : 32;
                            if (mode == 9) expected = pick == 0 ? 8 : 16;
                            if (mode == 15) expected = value * 13 + salt;
                            uint64_t actual = exercise_upcasts(&left.item, &right.item, salt, pick, mode);
                            if (actual != expected || left.item.value != left_expected ||
                                right.item.value != right_expected || right.item.bias != biases[c] ||
                                right.item.spare[0] != UINT64_C(0x55aa1234567890ff) ||
                                right.item.spare[1] != UINT64_C(0xccdd987654321011)) {
                                fprintf(stderr, "trait upcast mismatch a=%u b=%u c=%u s=%u pick=%u mode=%u got=%" PRIu64 " want=%" PRIu64 "\n",
                                        a, b, c, s, pick, mode, actual, expected);
                                return 1;
                            }
                            checks += 6;
                            if (left.before != UINT64_C(0x445566778899aabb) ||
                                left.after != UINT64_C(0xffeeddccbbaa9988) ||
                                right.before[0] != UINT64_C(0xaabbccdd11223344) ||
                                right.before[1] != UINT64_C(0x3141592653589793) ||
                                right.after[0] != UINT64_C(0x8877665544332211) ||
                                right.after[1] != UINT64_C(0x2718281828459045)) {
                                fputs("trait upcast sentinel changed\n", stderr);
                                return 1;
                            }
                            checks += 6;
                        }
                    }
                }
            }
        }
    }
    printf("PASS trait_upcasts checks=%" PRIu64 "\n", checks);
    return 0;
}
