#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern uint64_t nested_mut(uint64_t, uint32_t);
extern uint64_t nested_shared(uint64_t, uint32_t);
extern uint64_t nested_value(uint64_t, uint32_t);
extern uint64_t nested_alias(uint64_t, uint32_t);
extern uint64_t nested_local(uint64_t, uint32_t);
extern uint64_t nested_multiple(uint64_t, uint64_t, uint32_t);
extern uint64_t nested_owned_once(uint64_t, uint32_t);
extern uint64_t nested_empty(uint32_t);

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
    for (unsigned i = 0; i < 8192; ++i) {
        uint64_t seed = (uint64_t)i * UINT64_C(0x9e3779b97f4a7c15);
        uint64_t salt = rol(~seed, 23);
        uint32_t x = i % 3 == 0 ? UINT32_MAX : (uint32_t)(seed >> 17);
        uint64_t first = seed * 31 + x;
        uint64_t second = first * 31 + (uint32_t)(x + 1);
        uint64_t sequence = first ^ rol(second, 17);
        check(nested_mut(seed, x), first, "mutable capture", i);
        check(nested_shared(seed, x), first, "shared capture", i);
        check(nested_value(seed, x), sequence, "owned scalar capture", i);
        check(nested_alias(seed, x), sequence ^ rol(second, 29), "alias after calls", i);
        check(nested_local(seed, x), first, "local closure capture", i);
        check(nested_multiple(seed, salt, x), first ^ salt, "multiple captures", i);
        check(nested_owned_once(seed, x), first, "FnOnce capture", i);
        check(nested_empty(x), (uint64_t)x * 31, "empty environment", i);
    }
    if (checks != 65536) return 1;
    printf("PASS captured_closure_storage checks=%u\n", checks);
    return 0;
}
