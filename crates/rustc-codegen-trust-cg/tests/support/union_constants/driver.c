#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
extern const uint64_t TARGET[4];
static unsigned checks;
static void check(int ok, const char *name, unsigned i) {
    ++checks;
    if (!ok) { fprintf(stderr, "%s byte=%u\n", name, i); exit(1); }
}
static void store_check(void (*f)(void *), const void *expected, unsigned width, const char *name) {
    union { max_align_t alignment; unsigned char bytes[64]; } out;
    for (unsigned iteration = 0; iteration < 16; ++iteration) {
        unsigned char fill = (unsigned char)(iteration * 17 + 3);
        memset(out.bytes, fill, sizeof(out.bytes));
        f(out.bytes + 16);
        for (unsigned i = 0; i < 64; ++i)
            check(out.bytes[i] == (i >= 16 && i < 16 + width ? ((const unsigned char *)expected)[i - 16] : fill), name, i);
    }
}
extern void store_u8(void *), store_u64(void *), store_u128(void *), store_i128(void *), store_offset(void *);
extern void store_f32(void *), store_f64(void *);
extern void store_f32_negative_nan(void *), store_f32_min_nan(void *), store_f32_max_signaling_nan(void *);
extern void store_f32_quiet_nan(void *), store_f32_negative_zero(void *), store_f32_negative_infinity(void *);
extern float return_f32_nan(void);
extern double return_f64_nan(void);
extern void store_bool(void *), store_char(void *);
extern void store_ptr(void *), store_null(void *), store_const_ptr(void *), store_const_ref(void *);
extern uint64_t return_word(void);
extern const uint64_t *return_ptr(void);
extern const uint64_t *return_const_ptr(void);
extern void store_partial(void *);
typedef struct { const uint64_t *pointer; uint64_t (*function)(uint64_t); uint64_t bits; } Image;
typedef struct { uint64_t head; Image image; uint64_t tail; } Outer;
extern uint64_t image_function(uint64_t);
extern void store_image(void *), store_image_offset(void *), store_outer(void *);
int main(void) {
    uint8_t a = 0xb7;
    uint64_t b = UINT64_C(0xfedcba9876543210);
    __uint128_t c = ((__uint128_t)UINT64_C(0xfedcba9876543210) << 64) | UINT64_C(0x0123456789abcdef);
    __uint128_t d = -(((__uint128_t)UINT64_C(0x123456789abcdef0) << 64) | UINT64_C(0x1020304050607080));
    store_check(store_u8, &a, 1, "u8"); store_check(store_u64, &b, 8, "u64");
    store_check(store_u128, &c, 16, "u128"); store_check(store_i128, &d, 16, "i128");
    uint64_t e = UINT64_C(0x9876543210abcdef); store_check(store_offset, &e, 8, "offset image");
    { uint32_t a = UINT32_C(0x7f812345); uint64_t b = UINT64_C(0x7ff0123456789abc);
    store_check(store_f32, &a, 4, "f32 signaling NaN"); store_check(store_f64, &b, 8, "f64 signaling NaN"); }
    { uint8_t a = 1; uint32_t b = 0x10abcd;
    store_check(store_bool, &a, 1, "bool"); store_check(store_char, &b, 4, "char"); }
    { const uint64_t *a = &TARGET[2], *b = NULL;
    store_check(store_ptr, &a, sizeof(a), "pointer relocation"); store_check(store_null, &b, sizeof(b), "null pointer");
    store_check(store_const_ptr, &a, sizeof(a), "const pointer relocation");
    a = &TARGET[1]; store_check(store_const_ref, &a, sizeof(a), "const reference relocation"); }
    check(return_word() == UINT64_C(0xfedcba9876543210), "return word", 0);
    check(return_ptr() == &TARGET[2], "return pointer", 0);
    check(return_const_ptr() == &TARGET[3], "return const pointer", 0);
    union { max_align_t alignment; unsigned char bytes[64]; } out;
    memset(out.bytes, 0x5a, sizeof(out.bytes)); store_partial(out.bytes + 16);
    check(out.bytes[16] == 0xa5, "partial active byte", 16);
    for (unsigned i = 0; i < 64; ++i)
        if (i < 16 || i >= 24) check(out.bytes[i] == 0x5a, "partial guard", i);
    Image im = { &TARGET[2], image_function, UINT64_C(0xfedcba9876543210) };
    Outer outer = { UINT64_C(0x123456789abcdef0), im, UINT64_C(0x0123456789abcdef) };
    store_check(store_image, &im, sizeof(im), "image");
    store_check(store_image_offset, &im, sizeof(im), "image offset");
    store_check(store_outer, &outer, sizeof(outer), "outer image");
    Image got; store_image_offset(&got);
    for (uint64_t x = 0; x < 1024; ++x) {
        uint64_t expected = ((x << 17) | (x >> 47)) ^ UINT64_C(0x9876543210abcdef);
        check(got.function(x) == expected, "relocated function call", (unsigned)x);
        check(*got.pointer == 33, "relocated data dereference", (unsigned)x);
    }
    { uint32_t bits[] = { 0xff812345, 0x7f800001, 0x7fbfffff, 0x7fc54321, 0x80000000, 0xff800000 };
      void (*stores[])(void *) = { store_f32_negative_nan, store_f32_min_nan, store_f32_max_signaling_nan,
        store_f32_quiet_nan, store_f32_negative_zero, store_f32_negative_infinity };
      for (unsigned i = 0; i < 6; ++i) store_check(stores[i], &bits[i], 4, "f32 exact bits");
      float f = return_f32_nan(); double d = return_f64_nan(); uint32_t fb; uint64_t db;
      memcpy(&fb, &f, sizeof(fb)); memcpy(&db, &d, sizeof(db));
      check(fb == UINT32_C(0xff812345), "f32 return exact bits", 0);
      check(db == UINT64_C(0xfff0123456789abc), "f64 return exact bits", 0);
    }
    printf("PASS union_constant checks=%u\n", checks);
}
