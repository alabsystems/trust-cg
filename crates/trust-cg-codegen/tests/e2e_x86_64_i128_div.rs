// trust-cg-codegen/tests/e2e_x86_64_i128_div.rs - x86-64 i128 division differential vs clang
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Differential regressions for the x86-64 i128 division/remainder lowering.
//
// x86-64 has no native 128-bit DIV/IDIV, so i128 `sdiv`/`udiv`/`srem`/`urem`
// lower through the System V compiler-rt libcalls `__divti3` / `__udivti3` /
// `__modti3` / `__umodti3` (see `select_i128_div_libcall` in
// `trust-cg-lower/src/x86_64_isel.rs`), exactly as the AArch64 backend does.
//
// TRUST ASSUMPTION: like every libcall, the correctness of i128 division rests
// on the EXTERNAL compiler-rt implementation of those four symbols. It is NOT
// covered by an SMT lowering proof; it is verified by DIFFERENTIAL execution
// against clang's `__int128` / `unsigned __int128` operators below, whose
// runtime resolves the same compiler-rt symbols at link time.
//
// These use the AOT Mach-O path (`x86_64_differential_test`): the produced
// object is linked with `cc -arch x86_64`, which links in compiler-rt and
// resolves `__divti3` et al. Pure-JIT resolution of these libcalls is NOT
// exercised here — the JIT has no compiler-rt to bind the external CALL
// relocation against — so only the AOT differential path is asserted.
//
// Architecture: x86-64 host only. On AArch64 hosts these early-return so they
// never break the Apple-silicon dev machine.

mod common;
use common::x86_64_corpus::{
    build_i128_binop_module, x86_64_differential_test, x86_64_oracle_enabled,
};
use trust_ir::BinOp;

// The driver prints each 128-bit result as a hex (hi, lo) pair so the full
// 128-bit value is compared, not just the low 64 bits. `INT128_MIN` and the
// pathological `INT128_MIN / -1` overflow case (UB in C, and a trap in clang's
// own codegen) are deliberately avoided; every divisor is non-zero.
fn i128_div_driver(extern_name: &str, signed: bool) -> String {
    let ty = if signed {
        "__int128"
    } else {
        "unsigned __int128"
    };
    // INT128_MIN as an expression that does not itself overflow.
    let int128_min = "(((__int128)1) << 127)";
    let int128_max = "(~(((__int128)1) << 127))";
    let umax = "((unsigned __int128)0 - 1)";

    if signed {
        format!(
            r#"
#include <stdio.h>
extern {ty} {f}({ty} a, {ty} b);
static void pr(const char* k, __int128 v) {{
    unsigned long long lo = (unsigned long long)v;
    unsigned long long hi = (unsigned long long)(((unsigned __int128)v) >> 64);
    printf("%s=0x%016llx%016llx\n", k, hi, lo);
}}
int main(void) {{
    // positive / negative operand sign matrix
    pr("pp", {f}((__int128)100, (__int128)7));
    pr("np", {f}((__int128)-100, (__int128)7));
    pr("pn", {f}((__int128)100, (__int128)-7));
    pr("nn", {f}((__int128)-100, (__int128)-7));
    // wide values that straddle the 64-bit halves
    pr("hi",   {f}(((__int128)0x123456789abcdefULL << 64) | 0xfedcba9876543210ULL,
                   (__int128)0x100000001ULL));
    pr("hineg",{f}(-(((__int128)0x123456789abcdefULL << 64) | 0xfedcba9876543210ULL),
                   (__int128)1234567));
    // INT128 boundary values
    pr("maxby", {f}({max}, (__int128)3));
    pr("minby", {f}({min}, (__int128)3));
    pr("minbyneg", {f}({min}, (__int128)-7));
    // divide-by-large: |b| > |a| => quotient 0 / remainder a
    pr("bylarge", {f}((__int128)5, {max}));
    pr("byminlarge", {f}((__int128)-5, {min}));
    // exact division (no remainder)
    pr("exact", {f}((__int128)-700, (__int128)-7));
    return 0;
}}
"#,
            ty = ty,
            f = extern_name,
            max = int128_max,
            min = int128_min,
        )
    } else {
        format!(
            r#"
#include <stdio.h>
extern {ty} {f}({ty} a, {ty} b);
static void pr(const char* k, unsigned __int128 v) {{
    unsigned long long lo = (unsigned long long)v;
    unsigned long long hi = (unsigned long long)(v >> 64);
    printf("%s=0x%016llx%016llx\n", k, hi, lo);
}}
int main(void) {{
    pr("small", {f}((unsigned __int128)100, (unsigned __int128)7));
    pr("hi",    {f}(((unsigned __int128)0x123456789abcdefULL << 64) | 0xfedcba9876543210ULL,
                    (unsigned __int128)0x100000001ULL));
    // top-bit-set dividend: differs from the signed interpretation
    pr("topbit", {f}({umax}, (unsigned __int128)3));
    pr("topbit2",{f}({umax}, (unsigned __int128)0x100000000ULL));
    // divide-by-large: b > a => quotient 0 / remainder a
    pr("bylarge",{f}((unsigned __int128)5, {umax}));
    // exact division (no remainder)
    pr("exact",  {f}((unsigned __int128)700, (unsigned __int128)7));
    return 0;
}}
"#,
            ty = ty,
            f = extern_name,
            umax = umax,
        )
    }
}

#[test]
fn test_x86_64_differential_i128_sdiv() {
    if !x86_64_oracle_enabled("i128_sdiv") {
        return;
    }
    let module = build_i128_binop_module("_i128_sdiv", BinOp::SDiv);
    let c_reference = "__int128 _i128_sdiv(__int128 a, __int128 b) { return a / b; }\n";
    let driver = i128_div_driver("_i128_sdiv", /*signed=*/ true);
    let result = x86_64_differential_test("i128_sdiv", &module, c_reference, &driver);
    assert!(result.is_ok(), "x86-64 i128 sdiv: {}", result.unwrap_err());
}

#[test]
fn test_x86_64_differential_i128_udiv() {
    if !x86_64_oracle_enabled("i128_udiv") {
        return;
    }
    let module = build_i128_binop_module("_i128_udiv", BinOp::UDiv);
    let c_reference = "unsigned __int128 _i128_udiv(unsigned __int128 a, unsigned __int128 b) { return a / b; }\n";
    let driver = i128_div_driver("_i128_udiv", /*signed=*/ false);
    let result = x86_64_differential_test("i128_udiv", &module, c_reference, &driver);
    assert!(result.is_ok(), "x86-64 i128 udiv: {}", result.unwrap_err());
}

#[test]
fn test_x86_64_differential_i128_srem() {
    if !x86_64_oracle_enabled("i128_srem") {
        return;
    }
    let module = build_i128_binop_module("_i128_srem", BinOp::SRem);
    // C `%` on signed types: the result takes the sign of the dividend.
    let c_reference = "__int128 _i128_srem(__int128 a, __int128 b) { return a % b; }\n";
    let driver = i128_div_driver("_i128_srem", /*signed=*/ true);
    let result = x86_64_differential_test("i128_srem", &module, c_reference, &driver);
    assert!(result.is_ok(), "x86-64 i128 srem: {}", result.unwrap_err());
}

#[test]
fn test_x86_64_differential_i128_urem() {
    if !x86_64_oracle_enabled("i128_urem") {
        return;
    }
    let module = build_i128_binop_module("_i128_urem", BinOp::URem);
    let c_reference = "unsigned __int128 _i128_urem(unsigned __int128 a, unsigned __int128 b) { return a % b; }\n";
    let driver = i128_div_driver("_i128_urem", /*signed=*/ false);
    let result = x86_64_differential_test("i128_urem", &module, c_reference, &driver);
    assert!(result.is_ok(), "x86-64 i128 urem: {}", result.unwrap_err());
}
