/*
 * The 128-bit rows of the float -> integer differential, linked by the C
 * compiler driver against the platform's own runtime (no Rust runtime): the
 * `__fix{s,d}fti` / `__fixuns{s,d}fti` a raw conversion calls then come from the
 * system's compiler-rt or libgcc, which return MAX (or MIN) for a NaN where
 * Rust's `as` gives 0. Built against one build of casts.rs (trust-cg's or
 * LLVM's); prints every mismatch and exits with their count.
 *
 * Author: Andrew Yates <andrewyates.name@gmail.com>
 * Copyright 2026 Andrew Yates
 * License: Apache-2.0
 */
#include <math.h>
#include <stdio.h>

typedef __int128 i128;
typedef unsigned __int128 u128;

extern i128 as_f32_i128(float);
extern i128 as_f64_i128(double);
extern u128 as_f32_u128(float);
extern u128 as_f64_u128(double);
extern i128 unchecked_f32_i128(float);
extern i128 unchecked_f64_i128(double);
extern u128 unchecked_f32_u128(float);
extern u128 unchecked_f64_u128(double);

#define I128_MAX ((i128)(~(u128)0 >> 1))
#define I128_MIN (-I128_MAX - 1)
#define U128_MAX (~(u128)0)

static int failures;

static void check(const char *what, double input, u128 got, u128 want) {
    if (got != want) {
        failures++;
        printf("MISMATCH %s(%a) got %016llx%016llx want %016llx%016llx\n", what, input,
               (unsigned long long)(got >> 64), (unsigned long long)got,
               (unsigned long long)(want >> 64), (unsigned long long)want);
    }
}

/* Saturating `as`: NaN -> 0, beyond the range -> MIN/MAX, else toward zero. */
static void saturating(double x, i128 signed_want, u128 unsigned_want) {
    volatile double d = x;
    volatile float f = (float)x;
    check("as_f64_i128", x, (u128)as_f64_i128(d), (u128)signed_want);
    check("as_f64_u128", x, as_f64_u128(d), unsigned_want);
    check("as_f32_i128", x, (u128)as_f32_i128(f), (u128)signed_want);
    check("as_f32_u128", x, as_f32_u128(f), unsigned_want);
}

int main(void) {
    saturating(NAN, 0, 0);
    saturating(-NAN, 0, 0);
    saturating(INFINITY, I128_MAX, U128_MAX);
    saturating(-INFINITY, I128_MIN, 0);
    saturating(0x1p127, I128_MAX, (u128)1 << 127);
    saturating(-0x1p127, I128_MIN, 0);
    saturating(-0x1p100, -((i128)1 << 100), 0);
    saturating(-1.5, -1, 0);
    saturating(0x1p100, (i128)1 << 100, (u128)1 << 100);
    /* Beyond f32's range only as a binary64. */
    {
        volatile double d = 0x1p128;
        check("as_f64_i128", 0x1p128, (u128)as_f64_i128(d), (u128)I128_MAX);
        check("as_f64_u128", 0x1p128, as_f64_u128(d), U128_MAX);
    }
    /* `to_int_unchecked` inside its domain agrees with `as`. */
    {
        volatile double d = -0x1p127;
        volatile float f = -0x1p127f;
        check("unchecked_f64_i128", -0x1p127, (u128)unchecked_f64_i128(d), (u128)I128_MIN);
        check("unchecked_f32_i128", -0x1p127, (u128)unchecked_f32_i128(f), (u128)I128_MIN);
        volatile double h = -0.75;
        volatile float g = -0.75f;
        check("unchecked_f64_u128", -0.75, unchecked_f64_u128(h), 0);
        check("unchecked_f32_u128", -0.75, unchecked_f32_u128(g), 0);
    }
    printf("SUMMARY system-runtime mismatches=%d\n", failures);
    return failures;
}
