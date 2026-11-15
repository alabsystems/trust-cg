// trust-cg-codegen/tests/e2e_x86_64_i128_checked_mul.rs - x86-64 u128/i128
// checked multiply (OD-224) executed against clang's __builtin_mul_overflow
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The adapter expands a 128-bit checked multiply (`Inst::Overflow {
// MulOverflow, U128 | I128 }`) on x86-64 into the division-free limb check
// (ruling OD-224): two `I64` `CheckedUmul`s, a carry compare and a
// both-high-limbs test, on the operands' magnitudes plus a sign check for
// `i128`. Before OD-224 it divided the low product by an operand, a call of
// `__udivti3` / `__divti3`.
//
// Native differential: Rust's `overflowing_mul`, `checked_mul` and
// `saturating_mul` of `u128` and `i128`, spelled in trust-ir as rustc lowers
// them, compiled by trust-cg for x86-64 at O0, O1, O2 and O3, linked with a C
// driver and RUN, against the same functions in C over
// `__builtin_mul_overflow`, on every pair of an edge-value set (0, 1, -1,
// MIN, MAX, 2^64, 2^64 - 1, products just under and just over 2^128 and
// 2^127). Each object is also checked to call no 128-bit division routine;
// and, as the fails-before control, the same trust-ir in the division form
// (`trust_cg_lower::with_x86_i128_mulo_division_form`) is checked to call
// `__udivti3` / `__divti3`. A test, statistical over its edge set: never a
// proof.
//
// Host: x86-64 (native, or `cc -arch x86_64` on a healthy Rosetta 2 host).
// Elsewhere every test skips, printing why.

mod common;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use common::rosetta::{
    codegen_link_timeout, codegen_run_timeout, command_output_with_timeout, has_cc_x86_64_link_run,
    run_executable_with_timeout, x86_64_cc,
};
use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::{ICmpOp, Module as TrustIrModule, OverflowOp, Ty};
use trust_ir_build::ModuleBuilder;

fn enabled(test: &str) -> bool {
    if !has_cc_x86_64_link_run() {
        eprintln!("SKIP {test}: cc -arch x86_64 link/run unavailable on this host");
        return false;
    }
    true
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// The six functions, as rustc lowers `overflowing_mul`, `checked_mul` and
/// `saturating_mul` (one `Inst::Overflow` each):
///
/// * `tcg_{u,i}128_overflowing(a, b, out) -> bool`: `*out = p; o`;
/// * `tcg_{u,i}128_checked(a, b, out) -> u8`: `if o { 0 } else { *out = p; 1 }`;
/// * `tcg_{u,i}128_saturating(a, b) -> T`: `o ? MAX : p` unsigned, `o ? ((a ^
///   b) < 0 ? MIN : MAX) : p` signed.
fn checked_mul_module() -> TrustIrModule {
    let mut builder = ModuleBuilder::new("e2e_x86_64_i128_checked_mul");
    for (prefix, ty) in [("tcg_u128", Ty::U128), ("tcg_i128", Ty::I128)] {
        let signed = ty == Ty::I128;
        let ptr = Ty::PtrMut(Box::new(ty.clone()));
        // overflowing
        let sig = builder.add_func_type(vec![ty.clone(), ty.clone(), ptr.clone()], vec![Ty::Bool]);
        let mut f = builder.function(format!("{prefix}_overflowing"), sig);
        let entry = f.create_block();
        let a = f.add_block_param(entry, ty.clone());
        let b = f.add_block_param(entry, ty.clone());
        let out = f.add_block_param(entry, ptr.clone());
        f.switch_to_block(entry);
        let (p, o) = f.overflow(OverflowOp::MulOverflow, ty.clone(), a, b);
        f.store(ty.clone(), out, p);
        f.ret(vec![o]);
        f.build();
        // checked
        let sig = builder.add_func_type(vec![ty.clone(), ty.clone(), ptr.clone()], vec![Ty::U8]);
        let mut f = builder.function(format!("{prefix}_checked"), sig);
        let entry = f.create_block();
        let a = f.add_block_param(entry, ty.clone());
        let b = f.add_block_param(entry, ty.clone());
        let out = f.add_block_param(entry, ptr.clone());
        f.switch_to_block(entry);
        let (p, o) = f.overflow(OverflowOp::MulOverflow, ty.clone(), a, b);
        let (none, some) = (f.create_block(), f.create_block());
        f.condbr(o, none, vec![], some, vec![]);
        f.switch_to_block(none);
        let zero = f.iconst(Ty::U8, 0);
        f.ret(vec![zero]);
        f.switch_to_block(some);
        f.store(ty.clone(), out, p);
        let one = f.iconst(Ty::U8, 1);
        f.ret(vec![one]);
        f.build();
        // saturating
        let sig = builder.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
        let mut f = builder.function(format!("{prefix}_saturating"), sig);
        let entry = f.create_block();
        let a = f.add_block_param(entry, ty.clone());
        let b = f.add_block_param(entry, ty.clone());
        f.switch_to_block(entry);
        let (p, o) = f.overflow(OverflowOp::MulOverflow, ty.clone(), a, b);
        let saturated = if signed {
            let sign = f.binop(trust_ir::BinOp::Xor, ty.clone(), a, b);
            let zero = f.iconst(ty.clone(), 0);
            let negative = f.icmp(ICmpOp::Slt, ty.clone(), sign, zero);
            let min = f.iconst(ty.clone(), i128::MIN);
            let max = f.iconst(ty.clone(), i128::MAX);
            f.select(ty.clone(), negative, min, max)
        } else {
            f.uconst(ty.clone(), u128::MAX)
        };
        let result = f.select(ty.clone(), o, saturated, p);
        f.ret(vec![result]);
        f.build();
    }
    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// The same six functions in C over `__builtin_mul_overflow` (the oracle).
const C_REFERENCE: &str = r#"
typedef unsigned __int128 u128;
typedef __int128 i128;
#define I128_MAX ((i128)(~(u128)0 >> 1))
#define I128_MIN (-I128_MAX - 1)
_Bool tcg_u128_overflowing(u128 a, u128 b, u128 *out) { return __builtin_mul_overflow(a, b, out); }
unsigned char tcg_u128_checked(u128 a, u128 b, u128 *out) {
    u128 p; if (__builtin_mul_overflow(a, b, &p)) return 0; *out = p; return 1;
}
u128 tcg_u128_saturating(u128 a, u128 b) {
    u128 p; if (__builtin_mul_overflow(a, b, &p)) return ~(u128)0; return p;
}
_Bool tcg_i128_overflowing(i128 a, i128 b, i128 *out) { return __builtin_mul_overflow(a, b, out); }
unsigned char tcg_i128_checked(i128 a, i128 b, i128 *out) {
    i128 p; if (__builtin_mul_overflow(a, b, &p)) return 0; *out = p; return 1;
}
i128 tcg_i128_saturating(i128 a, i128 b) {
    i128 p; if (__builtin_mul_overflow(a, b, &p)) return ((a ^ b) < 0) ? I128_MIN : I128_MAX;
    return p;
}
"#;

/// The driver: every pair of each edge set through each function; every
/// 128-bit value printed in full as hex.
const DRIVER: &str = r#"
#include <stdio.h>
typedef unsigned __int128 u128;
typedef __int128 i128;
_Bool tcg_u128_overflowing(u128, u128, u128 *);
unsigned char tcg_u128_checked(u128, u128, u128 *);
u128 tcg_u128_saturating(u128, u128);
_Bool tcg_i128_overflowing(i128, i128, i128 *);
unsigned char tcg_i128_checked(i128, i128, i128 *);
i128 tcg_i128_saturating(i128, i128);
#define W(hi, lo) ((((u128)(hi)) << 64) | (u128)(lo))
static const u128 U[] = {
    0, 1, 2, 3,
    W(0, 0xffffffffffffffffULL),            /* 2^64 - 1 */
    W(1, 0),                                /* 2^64 */
    W(1, 1),                                /* 2^64 + 1: times 2^64 - 1 is 2^128 - 1 */
    W(0, 0x8000000000000000ULL),            /* 2^63 */
    W(2, 0),                                /* 2^65 */
    W(0x8000000000000000ULL, 0),            /* 2^127 */
    W(0x7fffffffffffffffULL, 0xffffffffffffffffULL), /* 2^127 - 1 */
    W(0xffffffffffffffffULL, 0xffffffffffffffffULL), /* MAX */
    W(0xffffffffffffffffULL, 0xfffffffffffffffeULL), /* MAX - 1 */
    W(0x5555555555555555ULL, 0x5555555555555555ULL), /* MAX / 3 */
    W(0x5555555555555555ULL, 0x5555555555555556ULL), /* MAX / 3 + 1 */
    W(0xffffffffffffffffULL, 0),
    W(0x00000000ffffffffULL, 0xffffffffffffffffULL),
    W(0xdeadbeefcafef00dULL, 0x0123456789abcdefULL),
    W(0, 0x00000001ffffffffULL),
};
static const i128 S[] = {
    0, 1, -1, 2, -2, 3,
    (i128)W(0x8000000000000000ULL, 0),      /* MIN */
    (i128)W(0x7fffffffffffffffULL, 0xffffffffffffffffULL), /* MAX */
    (i128)W(0x8000000000000000ULL, 1),      /* MIN + 1 */
    (i128)W(1, 0), -(i128)W(1, 0),          /* +-2^64 */
    (i128)W(0, 0xffffffffffffffffULL), -(i128)W(0, 0xffffffffffffffffULL),
    (i128)W(0, 0x8000000000000000ULL), -(i128)W(0, 0x8000000000000000ULL), /* +-2^63 */
    (i128)W(0x4000000000000000ULL, 0), -(i128)W(0x4000000000000000ULL, 0), /* +-2^126 */
    (i128)W(0x2aaaaaaaaaaaaaaaULL, 0xaaaaaaaaaaaaaaaaULL),                 /* MAX / 3 */
    -(i128)W(0x2aaaaaaaaaaaaaaaULL, 0xaaaaaaaaaaaaaaaaULL),
    (i128)W(0, 0x4000000000000000ULL),      /* 2^62 */
};
static void hex(u128 v) {
    printf(" %016llx%016llx", (unsigned long long)(v >> 64), (unsigned long long)v);
}
int main(void) {
    const unsigned nu = sizeof U / sizeof U[0], ns = sizeof S / sizeof S[0];
    for (unsigned i = 0; i < nu; i++) for (unsigned j = 0; j < nu; j++) {
        u128 p = 0x1111; _Bool o = tcg_u128_overflowing(U[i], U[j], &p);
        printf("u %u %u o=%d", i, j, (int)o); hex(p);
        u128 q = 0x2222; unsigned char s = tcg_u128_checked(U[i], U[j], &q);
        printf(" c=%u", (unsigned)s); hex(q);
        printf(" s"); hex(tcg_u128_saturating(U[i], U[j])); printf("\n");
    }
    for (unsigned i = 0; i < ns; i++) for (unsigned j = 0; j < ns; j++) {
        i128 p = 0x1111; _Bool o = tcg_i128_overflowing(S[i], S[j], &p);
        printf("i %u %u o=%d", i, j, (int)o); hex((u128)p);
        i128 q = 0x2222; unsigned char s = tcg_i128_checked(S[i], S[j], &q);
        printf(" c=%u", (unsigned)s); hex((u128)q);
        printf(" s"); hex((u128)tcg_i128_saturating(S[i], S[j])); printf("\n");
    }
    return 0;
}
"#;

fn compile(module: &TrustIrModule, opt_level: OptLevel) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level,
        target: Target::X86_64,
        // One thread: the fails-before control's division-form seam is
        // per-thread.
        parallel: false,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed());
    let result = compiler
        .compile(module)
        .unwrap_or_else(|error| panic!("x86-64 compile at {opt_level:?}: {error:?}"));
    assert!(!result.object_code.is_empty());
    result.object_code
}

fn test_dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("trust_cg_x86_64_i128_mulo_{name}"));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create the test directory");
    dir
}

fn cc(args: &[&str]) -> (bool, String) {
    let mut cmd = x86_64_cc();
    cmd.args(args);
    let result = command_output_with_timeout(&mut cmd, codegen_link_timeout())
        .unwrap_or_else(|error| panic!("cc -arch x86_64: {error}"));
    assert!(!result.timed_out, "cc timed out: {args:?}");
    (
        result.output.status.success(),
        String::from_utf8_lossy(&result.output.stderr).into_owned(),
    )
}

fn run(binary: &Path) -> String {
    let result = run_executable_with_timeout(binary, codegen_run_timeout())
        .unwrap_or_else(|error| panic!("run {}: {error}", binary.display()));
    assert!(!result.timed_out, "{} timed out", binary.display());
    assert_eq!(
        result.output.status.code(),
        Some(0),
        "{} exited abnormally",
        binary.display()
    );
    String::from_utf8_lossy(&result.output.stdout).into_owned()
}

/// The undefined symbols of a Mach-O / ELF object (`nm -u`), leading
/// underscores kept.
fn undefined_symbols(object: &Path) -> Vec<String> {
    let output = Command::new("nm")
        .arg("-u")
        .arg(object)
        .output()
        .expect("nm runs");
    assert!(output.status.success(), "nm -u {}", object.display());
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(|line| line.trim().to_string())
        .filter(|line| !line.is_empty())
        .collect()
}

/// Whether `symbols` names a 128-bit multiply or division routine, with or
/// without the Mach-O underscore.
fn routines(symbols: &[String]) -> Vec<String> {
    symbols
        .iter()
        .filter(|symbol| {
            let bare = symbol.trim_start_matches('_');
            ["udivti3", "divti3", "umodti3", "modti3", "muloti4"].contains(&bare)
        })
        .cloned()
        .collect()
}

/// The C oracle's output for the driver.
fn oracle_output(dir: &Path) -> String {
    let (reference_c, driver_c) = (dir.join("reference.c"), dir.join("driver.c"));
    fs::write(&reference_c, C_REFERENCE).unwrap();
    fs::write(&driver_c, DRIVER).unwrap();
    let reference_o = dir.join("reference.o");
    let (ok, err) = cc(&[
        "-c",
        "-O0",
        "-o",
        reference_o.to_str().unwrap(),
        reference_c.to_str().unwrap(),
    ]);
    assert!(ok, "cc reference.c: {err}");
    let binary = dir.join("oracle");
    let (ok, err) = cc(&[
        "-o",
        binary.to_str().unwrap(),
        driver_c.to_str().unwrap(),
        reference_o.to_str().unwrap(),
    ]);
    assert!(ok, "link the oracle: {err}");
    run(&binary)
}

/// At O0, O1, O2 and O3 the trust-cg object computes, for every edge pair,
/// exactly what `__builtin_mul_overflow` computes (flag, wrapped product,
/// `checked_mul`'s store-on-success, `saturating_mul`'s clamp), and calls no
/// 128-bit multiply or division routine.
#[test]
fn x86_64_i128_checked_mul_matches_builtin_mul_overflow_at_every_level() {
    if !enabled("x86_64_i128_checked_mul_matches_builtin_mul_overflow_at_every_level") {
        return;
    }
    let dir = test_dir("levels");
    let oracle = oracle_output(&dir);
    let lines = oracle.lines().count();
    assert_eq!(lines, 19 * 19 + 20 * 20, "the driver's pair count");
    let driver_c = dir.join("driver.c");
    let module = checked_mul_module();
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let object = dir.join(format!("tcg_{level:?}.o"));
        fs::write(&object, compile(&module, level)).unwrap();
        assert_eq!(
            routines(&undefined_symbols(&object)),
            Vec::<String>::new(),
            "{level:?}: the division-free check calls no routine"
        );
        let binary = dir.join(format!("tcg_{level:?}"));
        let (ok, err) = cc(&[
            "-o",
            binary.to_str().unwrap(),
            driver_c.to_str().unwrap(),
            object.to_str().unwrap(),
        ]);
        assert!(ok, "{level:?}: link: {err}");
        let got = run(&binary);
        for (k, (want, got)) in oracle.lines().zip(got.lines()).enumerate() {
            assert_eq!(
                got, want,
                "{level:?}: line {k} differs from __builtin_mul_overflow"
            );
        }
        assert_eq!(got.lines().count(), lines, "{level:?}: line count");
        eprintln!("I128_MULO_NATIVE {level:?}: {lines} pairs equal __builtin_mul_overflow");
    }
    let _ = fs::remove_dir_all(&dir);
}

/// FAILS BEFORE: the same module in the division form OD-224 replaced calls
/// `__udivti3` and `__divti3` (and still computes the same answers); the
/// default form calls neither.
#[test]
fn x86_64_the_division_form_called_the_routines_and_the_limb_check_does_not() {
    if !enabled("x86_64_the_division_form_called_the_routines_and_the_limb_check_does_not") {
        return;
    }
    let dir = test_dir("fails_before");
    let oracle = oracle_output(&dir);
    let driver_c = dir.join("driver.c");
    let module = checked_mul_module();
    let old = dir.join("old.o");
    fs::write(
        &old,
        trust_cg_lower::with_x86_i128_mulo_division_form(true, || compile(&module, OptLevel::O0)),
    )
    .unwrap();
    let mut called = routines(&undefined_symbols(&old));
    called.sort();
    let mut bare: Vec<&str> = called.iter().map(|s| s.trim_start_matches('_')).collect();
    bare.dedup();
    assert_eq!(bare, ["divti3", "udivti3"], "the division form: {called:?}");
    let binary = dir.join("old");
    let (ok, err) = cc(&[
        "-o",
        binary.to_str().unwrap(),
        driver_c.to_str().unwrap(),
        old.to_str().unwrap(),
    ]);
    assert!(ok, "link the division form: {err}");
    assert_eq!(
        run(&binary),
        oracle,
        "the division form computes the same answers"
    );
    let new = dir.join("new.o");
    fs::write(&new, compile(&module, OptLevel::O0)).unwrap();
    assert_eq!(routines(&undefined_symbols(&new)), Vec::<String>::new());
    let _ = fs::remove_dir_all(&dir);
}

/// A measurement aid, not a check: writes the trust-cg x86-64 object of the
/// module at O0..O3, in the division-free form and in the division form, to
/// `$MULO_OBJ_DIR` (`<form>_<level>.o`) for a decoder to count instructions
/// per function. Run with `--ignored --exact`.
#[test]
#[ignore = "measurement aid: writes objects to $MULO_OBJ_DIR"]
fn write_x86_64_i128_checked_mul_objects() {
    let Some(dir) = std::env::var_os("MULO_OBJ_DIR").map(PathBuf::from) else {
        eprintln!("SKIP: MULO_OBJ_DIR is not set");
        return;
    };
    fs::create_dir_all(&dir).unwrap();
    let module = checked_mul_module();
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        for (form, division) in [("limb", false), ("division", true)] {
            let object = trust_cg_lower::with_x86_i128_mulo_division_form(division, || {
                compile(&module, level)
            });
            fs::write(dir.join(format!("{form}_{level:?}.o")), object).unwrap();
        }
    }
    eprintln!("MULO_OBJ_DIR {}: 8 objects written", dir.display());
}
