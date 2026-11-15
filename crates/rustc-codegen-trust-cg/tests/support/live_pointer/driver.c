#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct Record { uint64_t tag; uint8_t bytes[16]; };
struct Bytes { uint8_t bytes[16]; };
struct Guarded { uint64_t before; struct Record value; uint64_t after; };
void replace_word(const uint64_t **p, const uint64_t *q) { *p = q; }
void replace_record(const struct Record **p, const struct Record *q) { *p = q; }
const uint64_t *choose_word(const uint64_t *a, const uint64_t *b) { (void)b; return a; }
void observe_word(const uint64_t **p) { (void)p; }
extern const uint64_t *word_address(const uint64_t *, const uint64_t *);
extern const uint8_t *field_address(const struct Record *, const struct Record *);
extern struct Bytes nested_copy(const struct Record *, const struct Record *);
extern void nested_into(const struct Record *, const struct Record *, struct Record *);
extern const uint64_t *local_address(const uint64_t *, const uint64_t *);
extern const uint64_t *branch_address(const uint64_t *, const uint64_t *, uint8_t);

static unsigned checks;
static void check(int ok, const char *what, unsigned iteration) {
    ++checks;
    if (!ok) { fprintf(stderr, "%s at %u\n", what, iteration); exit(1); }
}

int main(void) {
    uint64_t state = UINT64_C(0x4bd369f861dea2c7);
    for (unsigned i = 0; i < 8192; ++i) {
        state = state * UINT64_C(6364136223846793005) + 1;
        struct Record a = { .tag = state }, b = { .tag = ~state };
        for (unsigned j = 0; j < 16; ++j) {
            a.bytes[j] = (uint8_t)((state >> (j % 8) * 8) + 19 * j);
            b.bytes[j] = (uint8_t)~a.bytes[j];
        }
        check(word_address(&a.tag, &b.tag) == &b.tag, "word address", i);
        check(field_address(&a, &b) == &b.bytes[7], "field address", i);
        struct Bytes copied = nested_copy(&a, &b);
        check(memcmp(copied.bytes, b.bytes, 16) == 0, "nested return", i);
        struct Guarded out;
        memset(&out, 0x5a, sizeof(out));
        nested_into(&a, &b, &out.value);
        check(out.value.tag == b.tag, "nested tag", i);
        check(memcmp(out.value.bytes, b.bytes, 16) == 0, "nested store", i);
        check(out.before == UINT64_C(0x5a5a5a5a5a5a5a5a), "leading guard", i);
        check(out.after == UINT64_C(0x5a5a5a5a5a5a5a5a), "trailing guard", i);
        check(local_address(&a.tag, &b.tag) == &b.tag, "local address", i);
        check(branch_address(&a.tag, &b.tag, 0) == &a.tag, "unchanged branch", i);
        check(branch_address(&a.tag, &b.tag, 1) == &b.tag, "replaced branch", i);
    }
    printf("PASS live_pointer checks=%u\n", checks);
}
