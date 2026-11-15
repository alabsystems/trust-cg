/* Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 */
/* Independent pointer, alignment, mutation and destructor observations. */
#include <stdint.h>
#include <stddef.h>
#include <string.h>
static uint64_t drops, total, observations;
static uint64_t load(const void *p) {
    uint64_t value;
    memcpy(&value, p, sizeof(value));
    return value;
}
uintptr_t observe(const void *a, const void *b, int same, uint64_t bits_a,
                  uint64_t bits_b, size_t align) {
    if ((a == b) != (same != 0) || (uintptr_t)a % align || (uintptr_t)b % align ||
        load(a) != bits_a || load(b) != bits_b) return 0;
    observations++;
    return (uintptr_t)a;
}
int replace(void *a, uintptr_t old_address, uint64_t replacement, size_t extent) {
    if ((uintptr_t)a != old_address || (extent != 8 && extent != 16)) return 0;
    memcpy(a, &replacement, sizeof(replacement));
    if (extent > 8) memset((char *)a + 8, 0xa5, extent - 8);
    return 1;
}
void dropped(uint64_t value) { drops++; total += value; }
uint64_t drop_count(void) { return drops; }
uint64_t drop_sum(void) { return total; }
uint64_t observation_count(void) { return observations; }
