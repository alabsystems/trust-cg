#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

_Static_assert(sizeof(uintptr_t) == 8, "Linux AArch64 pointer image");
typedef struct { unsigned char data[8]; } Bytes;
extern void image_plain(void *, const unsigned char *);
extern void image_observed(void *, const unsigned char *);
extern void image_mutable(void *, unsigned char *);
extern void image_replaced(void *, const unsigned char *, const unsigned char *);
extern Bytes image_return(const unsigned char *);
extern void image_pair(void *, const unsigned char *, const unsigned char *);
extern void word_to_bytes(void *, uintptr_t);
extern uintptr_t bytes_to_word(const void *);
extern void wide_to_bytes(void *, __uint128_t);
extern __uint128_t bytes_to_wide(const void *);

static unsigned char observed[8];
static unsigned calls, replacements, checks;
void observe(const unsigned char *bytes) { memcpy(observed, bytes, 8); ++calls; }
void replace(const unsigned char **slot, const unsigned char *value) {
    *slot = value;
    ++replacements;
}
static void check(int ok, unsigned iteration, unsigned test, unsigned byte) {
    ++checks;
    if (!ok) {
        fprintf(stderr, "mismatch i=%u test=%u byte=%u\n", iteration, test, byte);
        exit(1);
    }
}
static void image_check(const unsigned char *out, const void *expected,
                        unsigned width, unsigned offset, unsigned char fill,
                        unsigned iteration, unsigned test) {
    for (unsigned j = 0; j < 64; ++j) {
        unsigned char wanted = j >= offset && j < offset + width
            ? ((const unsigned char *)expected)[j - offset] : fill;
        check(out[j] == wanted, iteration, test, j);
    }
}
int main(void) {
    unsigned char objects[256], out[64];
    for (unsigned i = 0; i < 4096; ++i) {
        unsigned char *pointer = i % 5 == 0 ? NULL : objects + (i % 257);
        const unsigned char *replacement = i % 7 == 0 ? NULL : objects + ((i * 31) % 257);
        unsigned offset = i % 17;
        unsigned char fill = (unsigned char)(i * 17 + 3);
        for (unsigned test = 0; test < 6; ++test) {
            uintptr_t expected[2] = {(uintptr_t)pointer, (uintptr_t)replacement};
            unsigned width = test == 5 ? 16 : 8;
            unsigned before_calls = calls, before_replacements = replacements;
            memset(out, fill, sizeof(out));
            switch (test) {
            case 0: image_plain(out + offset, pointer); break;
            case 1: image_observed(out + offset, pointer); break;
            case 2: image_mutable(out + offset, pointer); break;
            case 3:
                image_replaced(out + offset, pointer, replacement);
                expected[0] = (uintptr_t)replacement;
                break;
            case 4: {
                Bytes returned = image_return(pointer);
                memcpy(out + offset, returned.data, 8);
                break;
            }
            case 5: image_pair(out + offset, pointer, replacement); break;
            }
            image_check(out, expected, width, offset, fill, i, test);
            if (test >= 1 && test <= 3) {
                for (unsigned j = 0; j < 8; ++j)
                    check(observed[j] == ((unsigned char *)expected)[j], i, test, j);
                check(calls == before_calls + 1, i, test, 64);
            }
            if (test == 3)
                check(replacements == before_replacements + 1, i, test, 65);
        }
        // Include every one-bit position, all-ones, zero and mixed high lanes.
        uintptr_t word = i % 4 == 0 ? 0 : i % 4 == 1 ? UINT64_MAX
            : i % 4 == 2 ? (UINT64_C(1) << ((i / 4) % 64))
            : UINT64_C(0xa13945dc8211e777) * i;
        __uint128_t wide = ((__uint128_t)(word ^ UINT64_C(0x92f861ba09234dca)) << 64)
            | (word * UINT64_C(0x8711d85255937ba3));
        memset(out, fill, sizeof(out));
        word_to_bytes(out + offset, word);
        image_check(out, &word, 8, offset, fill, i, 6);
        memset(out, fill, sizeof(out));
        memcpy(out + offset, &word, 8);
        check(bytes_to_word(out + offset) == word, i, 7, 64);
        image_check(out, &word, 8, offset, fill, i, 7);
        memset(out, fill, sizeof(out));
        wide_to_bytes(out + offset, wide);
        image_check(out, &wide, 16, offset, fill, i, 8);
        memset(out, fill, sizeof(out));
        memcpy(out + offset, &wide, 16);
        check(bytes_to_wide(out + offset) == wide, i, 9, 64);
        image_check(out, &wide, 16, offset, fill, i, 9);
    }
    printf("PASS pointer_bytes checks=%u\n", checks);
}
