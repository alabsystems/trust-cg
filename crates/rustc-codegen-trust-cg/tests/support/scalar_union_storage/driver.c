#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint64_t (*Function)(void);
extern uintptr_t storage_word(uintptr_t, uintptr_t);
extern __uint128_t storage_wide(__uint128_t, __uint128_t);
extern const unsigned char *storage_pointer(const unsigned char *, const unsigned char *);
extern bool storage_boolean(bool, bool);
extern uint32_t storage_character(uint32_t, uint32_t);
extern uint32_t storage_float32(uint32_t, uint32_t);
extern uint64_t storage_float64(uint64_t, uint64_t);
extern const uint64_t *storage_reference(const uint64_t *, const uint64_t *);
extern Function storage_function(Function, Function);
extern uint64_t storage_custom(uint64_t, uint64_t);
extern uint8_t storage_partial(uint8_t, uint8_t);
extern uint64_t storage_uninit(uint64_t, uint64_t);
extern uint64_t storage_reassign(uint64_t, uint64_t, uint64_t, uint64_t);
extern uint64_t storage_copy(uint64_t, uint64_t, uint64_t);
extern uintptr_t select_word(bool, uintptr_t, uintptr_t);
extern __uint128_t select_wide(bool, __uint128_t, __uint128_t);
extern const unsigned char *select_pointer(bool, const unsigned char *, const unsigned char *);

static unsigned char observed[2][16];
static void *slots[2];
static unsigned calls, checks;
static void snapshot(void *slot, size_t width) {
    unsigned index = calls % 2;
    memcpy(observed[index], slot, width);
    slots[index] = slot;
    ++calls;
}
#define REPLACER(name, Type) \
    void name(Type *slot, Type replacement) { snapshot(slot, sizeof(*slot)); *slot = replacement; }
REPLACER(replace_word, uintptr_t)
REPLACER(replace_wide, __uint128_t)
REPLACER(replace_pointer, const unsigned char *)
REPLACER(replace_bool, bool)
REPLACER(replace_char, uint32_t)
REPLACER(replace_u32, uint32_t)
REPLACER(replace_u64, uint64_t)
REPLACER(replace_reference, const uint64_t *)
REPLACER(replace_function, Function)
REPLACER(replace_byte, uint8_t)
void fill_u64(uint64_t *slot, uint64_t replacement) { *slot = replacement; ++calls; }
static uint64_t first_function(void) { return UINT64_C(0x711e33000deadbaa); }
static uint64_t second_function(void) { return UINT64_C(0xf0348981424775aa); }
static void check(int ok, unsigned iteration, const char *label) {
    ++checks;
    if (!ok) { fprintf(stderr,"mismatch i=%u %s\n",iteration,label); exit(1); }
}
#define STORAGE(name, Type, first, second) do { \
    Type initial = (first); Type replacement = (second); \
    calls = 0; \
    Type got = storage_##name(initial, replacement); \
    check(got == replacement, i, #name " return"); \
    check(calls == 1, i, #name " calls"); \
    check(memcmp(observed[0], &initial, sizeof(initial)) == 0, i, #name " initial"); \
} while (0)

int main(void) {
    unsigned char objects[256];
    uint64_t words[256];
    for (unsigned i = 0; i < 256; ++i) words[i] = UINT64_C(0x13995aedccd85233) * (i+1);
    const uint32_t characters[] = {0, 0x61, 0x7ff, 0xd7ff, 0xe000, 0xffff, 0x10ffff};
    const uint32_t floats32[] = {0, 0x80000000, 0x7f800000, 0xff800000, 0x7f800001, 0xffbfffff, 0x7fc12345, 1, 0x7f7fffff};
    const uint64_t floats64[] = {0, UINT64_C(0x8000000000000000), UINT64_C(0x7ff0000000000000), UINT64_C(0x7ff0000000000001), UINT64_C(0xfff7ffffffffffff), UINT64_C(0x7ff89182736455aa), 1};
    for (unsigned i = 0; i < 4096; ++i) {
        uintptr_t word = i % 4 == 0 ? 0 : i % 4 == 1 ? UINT64_MAX
            : i % 4 == 2 ? UINT64_C(1) << ((i / 4) % 64) : UINT64_C(0xa399ed113954752b) * i;
        __uint128_t wide = ((__uint128_t)(word ^ UINT64_C(0x8124dcca361481fb)) << 64)
            | UINT64_C(0x985cceed67878235) * (word + 1);
        const unsigned char *pointer = i % 5 == 0 ? NULL : objects + (i % 257);
        const unsigned char *replacement_pointer = i % 7 == 0 ? NULL : objects + ((i*31) % 257);
        uint32_t float32 = i % 2 ? floats32[(i/2)%9] : (uint32_t)word;
        uint32_t replacement32 = i % 2 ? floats32[(i/3)%9] : ~float32;
        uint64_t float64 = i % 2 ? floats64[(i/2)%7] : word;
        uint64_t replacement64 = i % 2 ? floats64[(i/3)%7] : ~float64;
        const uint64_t *reference = words + (i%256), *replacement_reference = words + ((i*31)%256);
        Function function = i%2 ? first_function : second_function;
        Function replacement_function = i%3 ? second_function : first_function;
        STORAGE(word, uintptr_t, word, ~word);
        STORAGE(wide, __uint128_t, wide, ~wide);
        STORAGE(pointer, const unsigned char *, pointer, replacement_pointer);
        STORAGE(boolean, bool, (i&1)!=0, (i&2)!=0);
        STORAGE(character, uint32_t, characters[i%7], characters[(i*3+1)%7]);
        STORAGE(float32, uint32_t, float32, replacement32);
        STORAGE(float64, uint64_t, float64, replacement64);
        STORAGE(reference, const uint64_t *, reference, replacement_reference);
        // Exercise the returned reference, not just its representation.
        calls = 0;
        check(*storage_reference(reference, replacement_reference) == *replacement_reference, i, "reference dereference");
        STORAGE(function, Function, function, replacement_function);
        calls = 0;
        check(storage_function(function, replacement_function)() == replacement_function(), i, "function call");
        STORAGE(custom, uint64_t, float64, replacement64);
        STORAGE(partial, uint8_t, (uint8_t)i, (uint8_t)(i*31));
        calls = 0;
        check(storage_uninit(word, ~word) == ~word, i, "uninit initialized return");
        check(calls == 1, i, "uninit write count");
        for (unsigned condition = 0; condition <= 1; ++condition) {
            check(select_word(condition != 0, word, ~word) == (condition ? word : ~word), i, "select word");
            check(select_wide(condition != 0, wide, ~wide) == (condition ? wide : ~wide), i, "select wide");
            check(select_pointer(condition != 0, pointer, replacement_pointer) == (condition ? pointer : replacement_pointer), i, "select pointer");
        }
        uint64_t second = ~word, third = word ^ UINT64_C(0x715658223df21aa8), fourth = ~third;
        calls = 0;
        check(storage_reassign(word, second, third, fourth) == fourth, i, "reassignment return");
        check(calls == 2, i, "reassignment calls");
        check(memcmp(observed[0], &word, 8) == 0, i, "reassignment first image");
        check(memcmp(observed[1], &third, 8) == 0, i, "reassignment second image");
        check(slots[0] == slots[1], i, "reassignment alias address");
        calls = 0;
        check(storage_copy(word, second, third) == third, i, "copy return");
        check(calls == 2, i, "copy calls");
        check(memcmp(observed[0], &word, 8) == 0, i, "copy first image");
        check(memcmp(observed[1], &second, 8) == 0, i, "copy second image");
    }
    printf("PASS scalar_union_storage checks=%u\n", checks);
}
