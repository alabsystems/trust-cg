#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern uint64_t array_field_ref(uint8_t, uint8_t, uint8_t, uint8_t);
extern uint64_t aggregate_field_ref(uint8_t, uint8_t, uint8_t, uint8_t);
extern uint64_t dynamic_array_ref(uint8_t, uint8_t, uint8_t, uint8_t, uintptr_t);
extern uint64_t aggregate_entry_ref(uint8_t, uint8_t, uint8_t, uint8_t);
extern uint64_t loaded_reference(const uint16_t *);
extern uint64_t returned_reference(const uint16_t *, bool);
extern uint64_t mutated_reference(const uint16_t *);
extern uintptr_t whole_range_ref(uintptr_t, uintptr_t);

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
    for (unsigned i = 0; i < 16384; ++i) {
        uint64_t seed = (uint64_t)i * UINT64_C(0x9e3779b97f4a7c15);
        uint8_t bytes[4] = {(uint8_t)seed, (uint8_t)(seed >> 13),
                            (uint8_t)(seed >> 27), (uint8_t)(seed >> 39)};
        uint16_t words[2] = {(uint16_t)(seed >> 17), (uint16_t)(seed >> 43)};
        uint8_t a = bytes[0], b = bytes[1], c = bytes[2], d = bytes[3];
        uint64_t pair = a | ((uint64_t)d << 8);
        check(array_field_ref(a, b, c, d), pair, "array references in tuple", i);
        check(aggregate_field_ref(a, b, c, d), pair ^ 17, "local aggregate reference", i);
        check(dynamic_array_ref(a, b, c, d, seed), bytes[seed & 3], "dynamic array reference", i);
        check(aggregate_entry_ref(a, b, c, d), pair ^ 23, "entry aggregate reference", i);
        check(loaded_reference(words), ((uint64_t)words[0] ^ 29) | (UINT64_C(1) << 32),
              "loaded reference and identity", i);
        check(returned_reference(words, (i & 1) != 0), words[i & 1] | (UINT64_C(1) << 32),
              "returned reference and identity", i);
        check(mutated_reference(words), words[0] | ((uint64_t)words[1] << 16) | (UINT64_C(1) << 32),
              "reference replaced through raw alias", i);
        check(whole_range_ref(seed, ~seed), seed ^ rol(~seed, 11), "whole aggregate reborrow", i);
    }
    if (checks != 131072) return 1;
    printf("PASS raw_reference_storage checks=%u\n", checks);
    return 0;
}
