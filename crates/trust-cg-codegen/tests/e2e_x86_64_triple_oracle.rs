// trust-cg-codegen/tests/e2e_x86_64_triple_oracle.rs - x86-64 triple oracle
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// x86-64 mirror of `e2e_triple_oracle.rs`. Every function is evaluated by
// THREE independent truth sources and all three must agree:
//
//   1. trust_ir interpreter   — evaluates IR directly, no codegen
//   2. Trust Codegen (x86-64) — trust_ir -> ISel -> RegAlloc -> x86-64 -> Mach-O
//   3. clang                  — `cc -arch x86_64`, the golden C compiler
//
// Architecture: x86-64 host only. On AArch64 hosts these tests early-return so
// they never break the Apple-silicon dev machine. The corpus matches the
// AArch64 triple-oracle harness (fibonacci, gcd, sum_1_to_n, factorial, max,
// abs) plus integer power — see `tests/common/x86_64_corpus.rs`.
//
// Part of #301 / WS0 of docs/x86_64_completion_plan.md — x86-64 oracle.

mod common;
use common::x86_64_corpus::{
    TripleOracleCase, build_abs_module, build_deep_select_chain_module, build_factorial_module,
    build_fibonacci_module, build_gcd_module, build_i128_mulhi_i64_module, build_ipow_module,
    build_max_module, build_sum_1_to_n_module, x86_64_oracle_enabled, x86_64_triple_oracle_test,
};

#[test]
fn test_x86_64_triple_oracle_fibonacci() {
    if !x86_64_oracle_enabled("fibonacci") {
        return;
    }
    let module = build_fibonacci_module();
    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
long _fibonacci(long n) {
    if (n <= 1) return n;
    long a = 0, b = 1;
    for (long i = 2; i <= n; i++) {
        long tmp = a + b;
        a = b;
        b = tmp;
    }
    return b;
}
#endif

#ifdef EXTERN_ONLY
extern long _fibonacci(long n);
#endif

int main(void) {
    printf("fib(0)=%ld\n", _fibonacci(0));
    printf("fib(1)=%ld\n", _fibonacci(1));
    printf("fib(2)=%ld\n", _fibonacci(2));
    printf("fib(5)=%ld\n", _fibonacci(5));
    printf("fib(10)=%ld\n", _fibonacci(10));
    printf("fib(15)=%ld\n", _fibonacci(15));
    printf("fib(20)=%ld\n", _fibonacci(20));
    return 0;
}
"#;
    let cases = vec![
        TripleOracleCase::new("fib(0)", &[0]),
        TripleOracleCase::new("fib(1)", &[1]),
        TripleOracleCase::new("fib(2)", &[2]),
        TripleOracleCase::new("fib(5)", &[5]),
        TripleOracleCase::new("fib(10)", &[10]),
        TripleOracleCase::new("fib(15)", &[15]),
        TripleOracleCase::new("fib(20)", &[20]),
    ];
    let result = x86_64_triple_oracle_test("fibonacci", &module, "_fibonacci", c_source, &cases);
    assert!(
        result.is_ok(),
        "x86-64 triple oracle fibonacci failed: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_triple_oracle_gcd() {
    if !x86_64_oracle_enabled("gcd") {
        return;
    }
    let module = build_gcd_module();
    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
long _gcd(long a, long b) {
    while (b != 0) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}
#endif

#ifdef EXTERN_ONLY
extern long _gcd(long a, long b);
#endif

int main(void) {
    printf("gcd(12,8)=%ld\n", _gcd(12, 8));
    printf("gcd(100,75)=%ld\n", _gcd(100, 75));
    printf("gcd(48,18)=%ld\n", _gcd(48, 18));
    printf("gcd(17,13)=%ld\n", _gcd(17, 13));
    printf("gcd(0,5)=%ld\n", _gcd(0, 5));
    printf("gcd(7,0)=%ld\n", _gcd(7, 0));
    printf("gcd(1000,1)=%ld\n", _gcd(1000, 1));
    return 0;
}
"#;
    let cases = vec![
        TripleOracleCase::new("gcd(12,8)", &[12, 8]),
        TripleOracleCase::new("gcd(100,75)", &[100, 75]),
        TripleOracleCase::new("gcd(48,18)", &[48, 18]),
        TripleOracleCase::new("gcd(17,13)", &[17, 13]),
        TripleOracleCase::new("gcd(0,5)", &[0, 5]),
        TripleOracleCase::new("gcd(7,0)", &[7, 0]),
        TripleOracleCase::new("gcd(1000,1)", &[1000, 1]),
    ];
    let result = x86_64_triple_oracle_test("gcd", &module, "_gcd", c_source, &cases);
    assert!(
        result.is_ok(),
        "x86-64 triple oracle gcd failed: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_triple_oracle_sum_1_to_n() {
    if !x86_64_oracle_enabled("sum_1_to_n") {
        return;
    }
    let module = build_sum_1_to_n_module();
    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
long _sum_1_to_n(long n) {
    long sum = 0;
    for (long i = 1; i <= n; i++) {
        sum += i;
    }
    return sum;
}
#endif

#ifdef EXTERN_ONLY
extern long _sum_1_to_n(long n);
#endif

int main(void) {
    printf("sum(0)=%ld\n", _sum_1_to_n(0));
    printf("sum(1)=%ld\n", _sum_1_to_n(1));
    printf("sum(5)=%ld\n", _sum_1_to_n(5));
    printf("sum(10)=%ld\n", _sum_1_to_n(10));
    printf("sum(100)=%ld\n", _sum_1_to_n(100));
    printf("sum(1000)=%ld\n", _sum_1_to_n(1000));
    return 0;
}
"#;
    let cases = vec![
        TripleOracleCase::new("sum(0)", &[0]),
        TripleOracleCase::new("sum(1)", &[1]),
        TripleOracleCase::new("sum(5)", &[5]),
        TripleOracleCase::new("sum(10)", &[10]),
        TripleOracleCase::new("sum(100)", &[100]),
        TripleOracleCase::new("sum(1000)", &[1000]),
    ];
    let result = x86_64_triple_oracle_test("sum_1_to_n", &module, "_sum_1_to_n", c_source, &cases);
    assert!(
        result.is_ok(),
        "x86-64 triple oracle sum_1_to_n failed: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_triple_oracle_factorial() {
    if !x86_64_oracle_enabled("factorial") {
        return;
    }
    let module = build_factorial_module();
    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
long _factorial(long n) {
    if (n <= 1) return 1;
    long acc = 1;
    for (long i = 2; i <= n; i++) {
        acc *= i;
    }
    return acc;
}
#endif

#ifdef EXTERN_ONLY
extern long _factorial(long n);
#endif

int main(void) {
    printf("fact(0)=%ld\n", _factorial(0));
    printf("fact(1)=%ld\n", _factorial(1));
    printf("fact(2)=%ld\n", _factorial(2));
    printf("fact(5)=%ld\n", _factorial(5));
    printf("fact(10)=%ld\n", _factorial(10));
    printf("fact(15)=%ld\n", _factorial(15));
    return 0;
}
"#;
    let cases = vec![
        TripleOracleCase::new("fact(0)", &[0]),
        TripleOracleCase::new("fact(1)", &[1]),
        TripleOracleCase::new("fact(2)", &[2]),
        TripleOracleCase::new("fact(5)", &[5]),
        TripleOracleCase::new("fact(10)", &[10]),
        TripleOracleCase::new("fact(15)", &[15]),
    ];
    let result = x86_64_triple_oracle_test("factorial", &module, "_factorial", c_source, &cases);
    assert!(
        result.is_ok(),
        "x86-64 triple oracle factorial failed: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_triple_oracle_max() {
    if !x86_64_oracle_enabled("max") {
        return;
    }
    let module = build_max_module();
    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
long _max_val(long a, long b) {
    return (a > b) ? a : b;
}
#endif

#ifdef EXTERN_ONLY
extern long _max_val(long a, long b);
#endif

int main(void) {
    printf("max(10,20)=%ld\n", _max_val(10, 20));
    printf("max(20,10)=%ld\n", _max_val(20, 10));
    printf("max(5,5)=%ld\n", _max_val(5, 5));
    printf("max(-3,-7)=%ld\n", _max_val(-3, -7));
    printf("max(-1,1)=%ld\n", _max_val(-1, 1));
    return 0;
}
"#;
    let cases = vec![
        TripleOracleCase::new("max(10,20)", &[10, 20]),
        TripleOracleCase::new("max(20,10)", &[20, 10]),
        TripleOracleCase::new("max(5,5)", &[5, 5]),
        TripleOracleCase::new("max(-3,-7)", &[-3, -7]),
        TripleOracleCase::new("max(-1,1)", &[-1, 1]),
    ];
    let result = x86_64_triple_oracle_test("max", &module, "_max_val", c_source, &cases);
    assert!(
        result.is_ok(),
        "x86-64 triple oracle max failed: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_triple_oracle_abs() {
    if !x86_64_oracle_enabled("abs") {
        return;
    }
    let module = build_abs_module();
    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
long _abs_val(long x) {
    return (x < 0) ? -x : x;
}
#endif

#ifdef EXTERN_ONLY
extern long _abs_val(long x);
#endif

int main(void) {
    printf("abs(0)=%ld\n", _abs_val(0));
    printf("abs(1)=%ld\n", _abs_val(1));
    printf("abs(-1)=%ld\n", _abs_val(-1));
    printf("abs(42)=%ld\n", _abs_val(42));
    printf("abs(-42)=%ld\n", _abs_val(-42));
    return 0;
}
"#;
    let cases = vec![
        TripleOracleCase::new("abs(0)", &[0]),
        TripleOracleCase::new("abs(1)", &[1]),
        TripleOracleCase::new("abs(-1)", &[-1]),
        TripleOracleCase::new("abs(42)", &[42]),
        TripleOracleCase::new("abs(-42)", &[-42]),
    ];
    let result = x86_64_triple_oracle_test("abs", &module, "_abs_val", c_source, &cases);
    assert!(
        result.is_ok(),
        "x86-64 triple oracle abs failed: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_triple_oracle_ipow() {
    if !x86_64_oracle_enabled("ipow") {
        return;
    }
    let module = build_ipow_module();
    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
long _ipow(long base, long exp) {
    long result = 1;
    for (long i = 0; i < exp; i++) {
        result *= base;
    }
    return result;
}
#endif

#ifdef EXTERN_ONLY
extern long _ipow(long base, long exp);
#endif

int main(void) {
    printf("ipow(2,0)=%ld\n", _ipow(2, 0));
    printf("ipow(2,10)=%ld\n", _ipow(2, 10));
    printf("ipow(3,5)=%ld\n", _ipow(3, 5));
    printf("ipow(5,3)=%ld\n", _ipow(5, 3));
    printf("ipow(-2,7)=%ld\n", _ipow(-2, 7));
    return 0;
}
"#;
    let cases = vec![
        TripleOracleCase::new("ipow(2,0)", &[2, 0]),
        TripleOracleCase::new("ipow(2,10)", &[2, 10]),
        TripleOracleCase::new("ipow(3,5)", &[3, 5]),
        TripleOracleCase::new("ipow(5,3)", &[5, 3]),
        TripleOracleCase::new("ipow(-2,7)", &[-2, 7]),
    ];
    let result = x86_64_triple_oracle_test("ipow", &module, "_ipow", c_source, &cases);
    assert!(
        result.is_ok(),
        "x86-64 triple oracle ipow failed: {}",
        result.unwrap_err()
    );
}

/// Regression for the x86-64 deep-CMOV-chain register-allocator miscompile.
///
/// Seven distinct boolean predicates are simultaneously live into a seven-deep
/// `select`/CMOV chain; the earliest predicate (`cached_drop`) has the longest
/// live range. A coalescing-vs-splitting instruction-numbering desync used to
/// reuse that predicate's register for a later `SETBE` without preservation, so
/// the final CMOV tested the wrong byte and returned DROP(0) instead of KEEP(1)
/// for `(3,10,100,0,5,10,5)`. All three oracles must now agree.
#[test]
fn test_x86_64_triple_oracle_deep_select_chain() {
    if !x86_64_oracle_enabled("deep_select_chain") {
        return;
    }
    let module = build_deep_select_chain_module();
    let c_source = r#"
#include <stdio.h>

#define DROP 0
#define KEEP 1
#define CHECK 2
#define REMOVABLE 0x02
#define KEEPF 0x08
#define POISON 0x04
#define NO_REASON (-1)

#ifndef EXTERN_ONLY
int _deep_select_chain(int var_level, int trail_pos, int reason, int min_flags,
                       int level_seen_count, int level_seen_trail, int decision_level) {
    if (var_level == 0) return DROP;
    if ((min_flags & (REMOVABLE | KEEPF)) != 0) return DROP;
    if ((min_flags & POISON) != 0
        || var_level == decision_level
        || reason == NO_REASON
        || level_seen_count < 2
        || trail_pos <= level_seen_trail) {
        return KEEP;
    }
    return CHECK;
}
#endif

#ifdef EXTERN_ONLY
extern int _deep_select_chain(int, int, int, int, int, int, int);
#endif

int main(void) {
    printf("d(0,0,42,0,0,2147483647,5)=%d\n", _deep_select_chain(0, 0, 42, 0, 0, 2147483647, 5));
    printf("d(3,10,100,2,0,2147483647,5)=%d\n", _deep_select_chain(3, 10, 100, REMOVABLE, 0, 2147483647, 5));
    printf("d(3,10,100,8,0,2147483647,5)=%d\n", _deep_select_chain(3, 10, 100, KEEPF, 0, 2147483647, 5));
    printf("d(3,10,100,4,5,0,5)=%d\n", _deep_select_chain(3, 10, 100, POISON, 5, 0, 5));
    printf("d(5,10,100,0,5,0,5)=%d\n", _deep_select_chain(5, 10, 100, 0, 5, 0, 5));
    printf("d(3,10,-1,0,5,0,5)=%d\n", _deep_select_chain(3, 10, NO_REASON, 0, 5, 0, 5));
    printf("d(3,10,100,0,1,0,5)=%d\n", _deep_select_chain(3, 10, 100, 0, 1, 0, 5));
    printf("d(3,10,100,0,5,10,5)=%d\n", _deep_select_chain(3, 10, 100, 0, 5, 10, 5));
    printf("d(3,11,100,0,5,10,5)=%d\n", _deep_select_chain(3, 11, 100, 0, 5, 10, 5));
    return 0;
}
"#;
    let cases = vec![
        TripleOracleCase::new(
            "d(0,0,42,0,0,2147483647,5)",
            &[0, 0, 42, 0, 0, 2147483647, 5],
        ),
        TripleOracleCase::new(
            "d(3,10,100,2,0,2147483647,5)",
            &[3, 10, 100, 0x02, 0, 2147483647, 5],
        ),
        TripleOracleCase::new(
            "d(3,10,100,8,0,2147483647,5)",
            &[3, 10, 100, 0x08, 0, 2147483647, 5],
        ),
        TripleOracleCase::new("d(3,10,100,4,5,0,5)", &[3, 10, 100, 0x04, 5, 0, 5]),
        TripleOracleCase::new("d(5,10,100,0,5,0,5)", &[5, 10, 100, 0, 5, 0, 5]),
        TripleOracleCase::new("d(3,10,-1,0,5,0,5)", &[3, 10, -1, 0, 5, 0, 5]),
        TripleOracleCase::new("d(3,10,100,0,1,0,5)", &[3, 10, 100, 0, 1, 0, 5]),
        // The originally-failing case: returned DROP(0), must be KEEP(1).
        TripleOracleCase::new("d(3,10,100,0,5,10,5)", &[3, 10, 100, 0, 5, 10, 5]),
        TripleOracleCase::new("d(3,11,100,0,5,10,5)", &[3, 11, 100, 0, 5, 10, 5]),
    ];
    let result = x86_64_triple_oracle_test(
        "deep_select_chain",
        &module,
        "_deep_select_chain",
        c_source,
        &cases,
    );
    assert!(
        result.is_ok(),
        "x86-64 triple oracle deep_select_chain failed: {}",
        result.unwrap_err()
    );
}

/// i128 lowering through the i64-based triple oracle: high 64 bits of the
/// 128-bit signed product. Exercises SExt-to-i128, i128 MUL (cross terms),
/// i128 arithmetic right-shift across the 64-bit boundary, and Trunc-to-i64 —
/// all three oracles (interpreter, Trust Codegen, clang) must agree.
#[test]
fn test_x86_64_triple_oracle_i128_mulhi() {
    if !x86_64_oracle_enabled("i128_mulhi") {
        return;
    }
    let module = build_i128_mulhi_i64_module("_i128_mulhi");
    let c_source = r#"
#include <stdio.h>

#ifndef EXTERN_ONLY
long _i128_mulhi(long a, long b) {
    return (long)(((__int128)a * (__int128)b) >> 64);
}
#endif

#ifdef EXTERN_ONLY
extern long _i128_mulhi(long a, long b);
#endif

int main(void) {
    printf("mh(0)=%ld\n", _i128_mulhi(0, 0));
    printf("mh(1)=%ld\n", _i128_mulhi(1, 1));
    printf("mh(2)=%ld\n", _i128_mulhi(4611686018427387904L, 4));   // 2^62 * 4 = 2^64
    printf("mh(3)=%ld\n", _i128_mulhi(-1, -1));                    // (-1)*(-1)=1, hi=0
    printf("mh(4)=%ld\n", _i128_mulhi(-2, 4611686018427387904L)); // negative high
    printf("mh(5)=%ld\n", _i128_mulhi(9223372036854775807L, 9223372036854775807L));
    return 0;
}
"#;
    let cases = vec![
        TripleOracleCase::new("mh(0)", &[0, 0]),
        TripleOracleCase::new("mh(1)", &[1, 1]),
        TripleOracleCase::new("mh(2)", &[4611686018427387904, 4]),
        TripleOracleCase::new("mh(3)", &[-1, -1]),
        TripleOracleCase::new("mh(4)", &[-2, 4611686018427387904]),
        TripleOracleCase::new("mh(5)", &[9223372036854775807, 9223372036854775807]),
    ];
    let result = x86_64_triple_oracle_test("i128_mulhi", &module, "_i128_mulhi", c_source, &cases);
    assert!(
        result.is_ok(),
        "x86-64 triple oracle i128_mulhi failed: {}",
        result.unwrap_err()
    );
}
