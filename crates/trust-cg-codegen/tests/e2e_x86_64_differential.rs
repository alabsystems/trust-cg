// trust-cg-codegen/tests/e2e_x86_64_differential.rs - x86-64 differential vs clang
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// x86-64 mirror of `e2e_differential.rs`. Each integer program is compiled
// through BOTH Trust Codegen (targeting x86-64, AOT Mach-O on this macOS host)
// and the system C compiler (`cc -arch x86_64` / clang), each linked with a
// shared C driver, both run, and their stdout + exit codes asserted identical.
// clang is the golden reference: any divergence is a Trust Codegen x86-64 bug.
//
// Architecture: x86-64 host only. On AArch64 hosts these tests early-return so
// they never break the Apple-silicon dev machine. The corpus matches the
// AArch64 differential harness (simple arithmetic/branch, loops, recursion,
// fibonacci, gcd, collatz, factorial, integer power) — see
// `tests/common/x86_64_corpus.rs`.
//
// Part of #301 / WS0 of docs/x86_64_completion_plan.md — x86-64 oracle.

mod common;
use common::x86_64_corpus::{
    build_abs_module, build_add_module, build_collatz_steps_module, build_factorial_module,
    build_fibonacci_module, build_gcd_module, build_i128_binop_module, build_i128_cmp_module,
    build_ipow_module, build_max_module, build_recursive_fact_double_module,
    build_sum_1_to_n_module, x86_64_differential_test, x86_64_oracle_enabled,
};
use trust_ir::{BinOp, ICmpOp};

// =============================================================================
// Simple arithmetic / branch programs
// =============================================================================

#[test]
fn test_x86_64_differential_add() {
    if !x86_64_oracle_enabled("add") {
        return;
    }
    let module = build_add_module();
    let c_reference = r#"
int _add_two(int a, int b) {
    return a + b;
}
"#;
    let driver = r#"
#include <stdio.h>
extern int _add_two(int a, int b);
int main(void) {
    printf("add(3,4)=%d\n", _add_two(3, 4));
    printf("add(100,-50)=%d\n", _add_two(100, -50));
    printf("add(0,0)=%d\n", _add_two(0, 0));
    printf("add(-1,-1)=%d\n", _add_two(-1, -1));
    printf("add(2147483647,0)=%d\n", _add_two(2147483647, 0));
    return 0;
}
"#;
    let result = x86_64_differential_test("add", &module, c_reference, driver);
    assert!(
        result.is_ok(),
        "x86-64 differential add failed: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_differential_max() {
    if !x86_64_oracle_enabled("max") {
        return;
    }
    let module = build_max_module();
    let c_reference = r#"
long _max_val(long a, long b) {
    return (a > b) ? a : b;
}
"#;
    let driver = r#"
#include <stdio.h>
extern long _max_val(long a, long b);
int main(void) {
    printf("max(10,20)=%ld\n", _max_val(10, 20));
    printf("max(20,10)=%ld\n", _max_val(20, 10));
    printf("max(5,5)=%ld\n", _max_val(5, 5));
    printf("max(-3,-7)=%ld\n", _max_val(-3, -7));
    printf("max(-1,1)=%ld\n", _max_val(-1, 1));
    printf("max(0,0)=%ld\n", _max_val(0, 0));
    printf("max(-1000000,1000000)=%ld\n", _max_val(-1000000, 1000000));
    return 0;
}
"#;
    let result = x86_64_differential_test("max", &module, c_reference, driver);
    assert!(
        result.is_ok(),
        "x86-64 differential max failed: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_differential_abs() {
    if !x86_64_oracle_enabled("abs") {
        return;
    }
    let module = build_abs_module();
    let c_reference = r#"
long _abs_val(long x) {
    return (x < 0) ? -x : x;
}
"#;
    let driver = r#"
#include <stdio.h>
extern long _abs_val(long x);
int main(void) {
    printf("abs(0)=%ld\n", _abs_val(0));
    printf("abs(1)=%ld\n", _abs_val(1));
    printf("abs(-1)=%ld\n", _abs_val(-1));
    printf("abs(42)=%ld\n", _abs_val(42));
    printf("abs(-42)=%ld\n", _abs_val(-42));
    printf("abs(1000000)=%ld\n", _abs_val(1000000));
    printf("abs(-1000000)=%ld\n", _abs_val(-1000000));
    return 0;
}
"#;
    let result = x86_64_differential_test("abs", &module, c_reference, driver);
    assert!(
        result.is_ok(),
        "x86-64 differential abs failed: {}",
        result.unwrap_err()
    );
}

// =============================================================================
// Loop / accumulation programs
// =============================================================================

#[test]
fn test_x86_64_differential_sum_1_to_n() {
    if !x86_64_oracle_enabled("sum_1_to_n") {
        return;
    }
    let module = build_sum_1_to_n_module();
    let c_reference = r#"
long _sum_1_to_n(long n) {
    long sum = 0;
    for (long i = 1; i <= n; i++) {
        sum += i;
    }
    return sum;
}
"#;
    let driver = r#"
#include <stdio.h>
extern long _sum_1_to_n(long n);
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
    let result = x86_64_differential_test("sum_1_to_n", &module, c_reference, driver);
    assert!(
        result.is_ok(),
        "x86-64 differential sum_1_to_n failed: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_differential_factorial() {
    if !x86_64_oracle_enabled("factorial") {
        return;
    }
    let module = build_factorial_module();
    let c_reference = r#"
long _factorial(long n) {
    if (n <= 1) return 1;
    long acc = 1;
    for (long i = 2; i <= n; i++) {
        acc *= i;
    }
    return acc;
}
"#;
    let driver = r#"
#include <stdio.h>
extern long _factorial(long n);
int main(void) {
    printf("fact(0)=%ld\n", _factorial(0));
    printf("fact(1)=%ld\n", _factorial(1));
    printf("fact(2)=%ld\n", _factorial(2));
    printf("fact(5)=%ld\n", _factorial(5));
    printf("fact(10)=%ld\n", _factorial(10));
    printf("fact(20)=%ld\n", _factorial(20));
    return 0;
}
"#;
    let result = x86_64_differential_test("factorial", &module, c_reference, driver);
    assert!(
        result.is_ok(),
        "x86-64 differential factorial failed: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_differential_fibonacci() {
    if !x86_64_oracle_enabled("fibonacci") {
        return;
    }
    let module = build_fibonacci_module();
    let c_reference = r#"
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
"#;
    let driver = r#"
#include <stdio.h>
extern long _fibonacci(long n);
int main(void) {
    printf("fib(0)=%ld\n", _fibonacci(0));
    printf("fib(1)=%ld\n", _fibonacci(1));
    printf("fib(2)=%ld\n", _fibonacci(2));
    printf("fib(5)=%ld\n", _fibonacci(5));
    printf("fib(10)=%ld\n", _fibonacci(10));
    printf("fib(20)=%ld\n", _fibonacci(20));
    printf("fib(50)=%ld\n", _fibonacci(50));
    return 0;
}
"#;
    let result = x86_64_differential_test("fibonacci", &module, c_reference, driver);
    assert!(
        result.is_ok(),
        "x86-64 differential fibonacci failed: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_differential_ipow() {
    if !x86_64_oracle_enabled("ipow") {
        return;
    }
    let module = build_ipow_module();
    let c_reference = r#"
long _ipow(long base, long exp) {
    long result = 1;
    for (long i = 0; i < exp; i++) {
        result *= base;
    }
    return result;
}
"#;
    let driver = r#"
#include <stdio.h>
extern long _ipow(long base, long exp);
int main(void) {
    printf("ipow(2,0)=%ld\n", _ipow(2, 0));
    printf("ipow(2,1)=%ld\n", _ipow(2, 1));
    printf("ipow(2,10)=%ld\n", _ipow(2, 10));
    printf("ipow(3,5)=%ld\n", _ipow(3, 5));
    printf("ipow(5,3)=%ld\n", _ipow(5, 3));
    printf("ipow(-2,7)=%ld\n", _ipow(-2, 7));
    printf("ipow(10,9)=%ld\n", _ipow(10, 9));
    return 0;
}
"#;
    let result = x86_64_differential_test("ipow", &module, c_reference, driver);
    assert!(
        result.is_ok(),
        "x86-64 differential ipow failed: {}",
        result.unwrap_err()
    );
}

// =============================================================================
// Division / remainder loops
// =============================================================================

#[test]
fn test_x86_64_differential_gcd() {
    if !x86_64_oracle_enabled("gcd") {
        return;
    }
    let module = build_gcd_module();
    let c_reference = r#"
long _gcd(long a, long b) {
    while (b != 0) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}
"#;
    let driver = r#"
#include <stdio.h>
extern long _gcd(long a, long b);
int main(void) {
    printf("gcd(48,18)=%ld\n", _gcd(48, 18));
    printf("gcd(1071,462)=%ld\n", _gcd(1071, 462));
    printf("gcd(7,3)=%ld\n", _gcd(7, 3));
    printf("gcd(100,75)=%ld\n", _gcd(100, 75));
    printf("gcd(0,5)=%ld\n", _gcd(0, 5));
    printf("gcd(7,0)=%ld\n", _gcd(7, 0));
    return 0;
}
"#;
    let result = x86_64_differential_test("gcd", &module, c_reference, driver);
    assert!(
        result.is_ok(),
        "x86-64 differential gcd failed: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_differential_collatz_steps() {
    if !x86_64_oracle_enabled("collatz_steps") {
        return;
    }
    let module = build_collatz_steps_module();
    let c_reference = r#"
long _collatz_steps(long n) {
    if (n <= 1) {
        return 0;
    }
    long steps = 0;
    while (n != 1) {
        if ((n % 2) == 0) {
            n = n / 2;
        } else {
            n = 3 * n + 1;
        }
        steps = steps + 1;
    }
    return steps;
}
"#;
    let driver = r#"
#include <stdio.h>
extern long _collatz_steps(long n);
int main(void) {
    printf("collatz_steps(1)=%ld\n", _collatz_steps(1));
    printf("collatz_steps(2)=%ld\n", _collatz_steps(2));
    printf("collatz_steps(3)=%ld\n", _collatz_steps(3));
    printf("collatz_steps(7)=%ld\n", _collatz_steps(7));
    printf("collatz_steps(27)=%ld\n", _collatz_steps(27));
    return 0;
}
"#;
    let result = x86_64_differential_test("collatz_steps", &module, c_reference, driver);
    assert!(
        result.is_ok(),
        "x86-64 differential collatz_steps failed: {}",
        result.unwrap_err()
    );
}

// =============================================================================
// Recursion / call ABI
// =============================================================================

#[test]
fn test_x86_64_differential_recursive_fact_double() {
    if !x86_64_oracle_enabled("recursive_fact_double") {
        return;
    }
    let module = build_recursive_fact_double_module();
    let c_reference = r#"
long _fact_helper(long n, long acc) {
    if (n <= 1) {
        return acc;
    } else {
        return _fact_helper(n - 1, acc * n);
    }
}

long _fact_double(long n) {
    return _fact_helper(n, 1) * 2;
}
"#;
    let driver = r#"
#include <stdio.h>
extern long _fact_double(long n);
int main(void) {
    printf("fact_double(0)=%ld\n", _fact_double(0));
    printf("fact_double(1)=%ld\n", _fact_double(1));
    printf("fact_double(2)=%ld\n", _fact_double(2));
    printf("fact_double(3)=%ld\n", _fact_double(3));
    printf("fact_double(5)=%ld\n", _fact_double(5));
    printf("fact_double(8)=%ld\n", _fact_double(8));
    return 0;
}
"#;
    let result = x86_64_differential_test("recursive_fact_double", &module, c_reference, driver);
    assert!(
        result.is_ok(),
        "x86-64 differential recursive_fact_double failed: {}",
        result.unwrap_err()
    );
}

// =============================================================================
// i128 (128-bit integer) differential tests
//
// Permanent regressions for the x86-64 i128 silent-miscompile fix. Before the
// fix, the ISel lowered I128 arithmetic/compare/shift as a single 64-bit
// register (dropping the high half / carry), and passed/returned i128 in one
// GPR instead of a register pair. Each test below previously DISAGREED with
// clang's __int128 codegen; they now agree.
// =============================================================================

#[test]
fn test_x86_64_differential_i128_add_carry() {
    if !x86_64_oracle_enabled("i128_add_carry") {
        return;
    }
    let module = build_i128_binop_module("_i128_add", BinOp::Add);
    let c_reference = "__int128 _i128_add(__int128 a, __int128 b) { return a + b; }\n";
    // low halves sum carries into the high 64.
    let driver = r#"
#include <stdio.h>
extern __int128 _i128_add(__int128 a, __int128 b);
static void pr(const char* k, __int128 v) {
    unsigned long long lo = (unsigned long long)v;
    unsigned long long hi = (unsigned long long)(v >> 64);
    printf("%s=0x%016llx%016llx\n", k, hi, lo);
}
int main(void) {
    pr("carry", _i128_add(((__int128)0)|0xFFFFFFFFFFFFFFFFULL, ((__int128)0)|1ULL));
    pr("hi",    _i128_add(((__int128)5<<64)|3ULL, ((__int128)7<<64)|9ULL));
    pr("neg",   _i128_add((__int128)-1, (__int128)1));
    return 0;
}
"#;
    let result = x86_64_differential_test("i128_add_carry", &module, c_reference, driver);
    assert!(result.is_ok(), "x86-64 i128 add: {}", result.unwrap_err());
}

#[test]
fn test_x86_64_differential_i128_sub_borrow() {
    if !x86_64_oracle_enabled("i128_sub_borrow") {
        return;
    }
    let module = build_i128_binop_module("_i128_sub", BinOp::Sub);
    let c_reference = "__int128 _i128_sub(__int128 a, __int128 b) { return a - b; }\n";
    let driver = r#"
#include <stdio.h>
extern __int128 _i128_sub(__int128 a, __int128 b);
static void pr(const char* k, __int128 v) {
    unsigned long long lo = (unsigned long long)v;
    unsigned long long hi = (unsigned long long)(v >> 64);
    printf("%s=0x%016llx%016llx\n", k, hi, lo);
}
int main(void) {
    pr("borrow", _i128_sub(((__int128)1<<64)|0ULL, ((__int128)0)|1ULL));
    pr("plain",  _i128_sub(((__int128)9<<64)|5ULL, ((__int128)3<<64)|2ULL));
    return 0;
}
"#;
    let result = x86_64_differential_test("i128_sub_borrow", &module, c_reference, driver);
    assert!(result.is_ok(), "x86-64 i128 sub: {}", result.unwrap_err());
}

#[test]
fn test_x86_64_differential_i128_mul() {
    if !x86_64_oracle_enabled("i128_mul") {
        return;
    }
    let module = build_i128_binop_module("_i128_mul", BinOp::Mul);
    let c_reference = "__int128 _i128_mul(__int128 a, __int128 b) { return a * b; }\n";
    let driver = r#"
#include <stdio.h>
extern __int128 _i128_mul(__int128 a, __int128 b);
static void pr(const char* k, __int128 v) {
    unsigned long long lo = (unsigned long long)v;
    unsigned long long hi = (unsigned long long)(v >> 64);
    printf("%s=0x%016llx%016llx\n", k, hi, lo);
}
int main(void) {
    pr("cross", _i128_mul(((__int128)0)|0x100000000ULL, ((__int128)0)|0x100000000ULL));
    pr("hi",    _i128_mul(((__int128)0)|7ULL, ((__int128)3<<64)|5ULL));
    pr("big",   _i128_mul(((__int128)0)|0xFFFFFFFFFFFFFFFFULL, ((__int128)0)|3ULL));
    return 0;
}
"#;
    let result = x86_64_differential_test("i128_mul", &module, c_reference, driver);
    assert!(result.is_ok(), "x86-64 i128 mul: {}", result.unwrap_err());
}

fn i128_cmp_driver(extern_name: &str) -> String {
    format!(
        r#"
#include <stdio.h>
extern long {f}(__int128 a, __int128 b);
int main(void) {{
    // high halves equal, low differs
    printf("eqhi=%ld\n", {f}(((__int128)5<<64)|1ULL, ((__int128)5<<64)|2ULL));
    // high halves differ
    printf("hidiff=%ld\n", {f}(((__int128)2<<64)|0ULL, ((__int128)1<<64)|0xFFFFFFFFFFFFFFFFULL));
    // equal
    printf("eq=%ld\n", {f}(((__int128)9<<64)|9ULL, ((__int128)9<<64)|9ULL));
    // signed negative vs positive
    printf("negpos=%ld\n", {f}((__int128)-1, (__int128)1));
    return 0;
}}
"#,
        f = extern_name
    )
}

#[test]
fn test_x86_64_differential_i128_cmp_all_predicates() {
    if !x86_64_oracle_enabled("i128_cmp") {
        return;
    }
    let cases: &[(&str, ICmpOp, &str)] = &[
        ("_i128_eq", ICmpOp::Eq, "a == b"),
        ("_i128_ne", ICmpOp::Ne, "a != b"),
        ("_i128_slt", ICmpOp::Slt, "a < b"),
        ("_i128_sgt", ICmpOp::Sgt, "a > b"),
        ("_i128_sle", ICmpOp::Sle, "a <= b"),
        ("_i128_sge", ICmpOp::Sge, "a >= b"),
        (
            "_i128_ult",
            ICmpOp::Ult,
            "(unsigned __int128)a < (unsigned __int128)b",
        ),
        (
            "_i128_ugt",
            ICmpOp::Ugt,
            "(unsigned __int128)a > (unsigned __int128)b",
        ),
        (
            "_i128_ule",
            ICmpOp::Ule,
            "(unsigned __int128)a <= (unsigned __int128)b",
        ),
        (
            "_i128_uge",
            ICmpOp::Uge,
            "(unsigned __int128)a >= (unsigned __int128)b",
        ),
    ];
    for (name, op, expr) in cases {
        let module = build_i128_cmp_module(name, *op);
        let c_reference = format!("long {name}(__int128 a, __int128 b) {{ return {expr}; }}\n");
        let driver = i128_cmp_driver(name);
        let result =
            x86_64_differential_test(&format!("i128_cmp{name}"), &module, &c_reference, &driver);
        assert!(
            result.is_ok(),
            "x86-64 i128 cmp {name}: {}",
            result.unwrap_err()
        );
    }
}

fn i128_shift_driver(extern_name: &str, signed: bool) -> String {
    let ty = if signed {
        "__int128"
    } else {
        "unsigned __int128"
    };
    format!(
        r#"
#include <stdio.h>
extern {ty} {f}({ty} a, {ty} b);
static void pr(const char* k, {ty} v) {{
    unsigned long long lo = (unsigned long long)v;
    unsigned long long hi = (unsigned long long)(v >> 64);
    printf("%s=0x%016llx%016llx\n", k, hi, lo);
}}
int main(void) {{
    {ty} lo_full = ({ty})0xFFFFFFFFFFFFFFFFULL;        // lo=max, hi=0
    {ty} hi_full = (({ty})0xFFFFFFFFFFFFFFFFULL) << 64; // hi=max, lo=0
    {ty} src = {sel};
    pr("s0",   {f}(src, 0));
    pr("s1",   {f}(src, 1));
    pr("s63",  {f}(src, 63));
    pr("s64",  {f}(src, 64));
    pr("s65",  {f}(src, 65));
    pr("s127", {f}(src, 127));
    return 0;
}}
"#,
        ty = ty,
        f = extern_name,
        // shl uses lo_full (bits flow up); right shifts use hi_full (bits flow down).
        sel = if extern_name.contains("shl") {
            "lo_full"
        } else {
            "hi_full"
        }
    )
}

#[test]
fn test_x86_64_differential_i128_shl() {
    if !x86_64_oracle_enabled("i128_shl") {
        return;
    }
    let module = build_i128_binop_module("_i128_shl", BinOp::Shl);
    let c_reference = "__int128 _i128_shl(__int128 a, __int128 b) { return a << b; }\n";
    let driver = i128_shift_driver("_i128_shl", true);
    let result = x86_64_differential_test("i128_shl", &module, c_reference, &driver);
    assert!(result.is_ok(), "x86-64 i128 shl: {}", result.unwrap_err());
}

#[test]
fn test_x86_64_differential_i128_lshr() {
    if !x86_64_oracle_enabled("i128_lshr") {
        return;
    }
    let module = build_i128_binop_module("_i128_lshr", BinOp::LShr);
    let c_reference = "unsigned __int128 _i128_lshr(unsigned __int128 a, unsigned __int128 b) { return a >> b; }\n";
    let driver = i128_shift_driver("_i128_lshr", false);
    let result = x86_64_differential_test("i128_lshr", &module, c_reference, &driver);
    assert!(result.is_ok(), "x86-64 i128 lshr: {}", result.unwrap_err());
}

#[test]
fn test_x86_64_differential_i128_ashr() {
    if !x86_64_oracle_enabled("i128_ashr") {
        return;
    }
    let module = build_i128_binop_module("_i128_ashr", BinOp::AShr);
    let c_reference = "__int128 _i128_ashr(__int128 a, __int128 b) { return a >> b; }\n";
    let driver = i128_shift_driver("_i128_ashr", true);
    let result = x86_64_differential_test("i128_ashr", &module, c_reference, &driver);
    assert!(result.is_ok(), "x86-64 i128 ashr: {}", result.unwrap_err());
}
