// Copyright 2026 Andrew Yates | Apache-2.0
//! DarwinPCS twin of `e2e_aarch64_variadic_linux.rs`: TrustCG variadic calls
//! read by independently compiled Apple clang `va_arg` consumers, natively on
//! `aarch64-apple-darwin` at O0-O3.
//!
//! Apple arm64 passes every anonymous argument on the stack, in 8-byte slots
//! (a sixteen-aligned one at the next 16-aligned offset), and its `va_list` is
//! a plain `char *` cursor. The anonymous tail starts after the last FIXED
//! stack byte, where named narrow arguments are packed at their natural size.
//! The producer performs C's default argument promotions explicitly
//! (`bool`/`char`/`short` to `int`, `float` to `double`), as a C frontend does.
//! The corpus is the Linux suite's (bank exhaustion, mixed GPR/FPR sequences
//! with 1, 5 and 17 named arguments, narrow named stack arguments, promoted
//! anonymous narrow values, `__int128`, 16-byte, 24-byte and HFA aggregates)
//! plus Darwin shapes: anonymous `bool`, anonymous arguments after packed named
//! stack bytes, after a named HFA packed behind a `float`, after both register
//! banks are exhausted by named arguments, and a named `__int128` starting in
//! an odd register. Each check also runs the clang-to-clang call against a
//! digest computed in Rust.
//!
//! Only the TrustCG-caller direction exists: TrustCG refuses variadic
//! definitions (`[TCG-VARIADIC-DEFINITION]`), and an anonymous non-homogeneous
//! aggregate over 16 bytes (by reference to a caller copy on Darwin) is refused
//! with `[TCG-VARARG-ABI]`. Both refusals are checked here. Execution evidence
//! on this host, not proof-emission authority.

#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

#[path = "common/darwin_c_boundary.rs"]
mod boundary;

use boundary::{Arg, Corpus, Scalar};
use trust_ir::Ty;
use trust_ir_build::ModuleBuilder;

const BOOL: Arg = Arg::S(Scalar::Bool);
const I8: Arg = Arg::S(Scalar::I8);
const U8: Arg = Arg::S(Scalar::U8);
const I16: Arg = Arg::S(Scalar::I16);
const U16: Arg = Arg::S(Scalar::U16);
const I64: Arg = Arg::S(Scalar::I64);
const U64: Arg = Arg::S(Scalar::U64);
const I128: Arg = Arg::S(Scalar::I128);
const F32: Arg = Arg::S(Scalar::F32);
const F64: Arg = Arg::S(Scalar::F64);

fn cat(parts: &[&[Arg]]) -> Vec<Arg> {
    parts.concat()
}

fn corpus() -> Corpus {
    let mut c = Corpus::new("variadic");
    let pair = c.aggregate("Pair", &[Scalar::U64, Scalar::U64]);
    let hfa = c.aggregate("Hfa", &[Scalar::F64; 3]);
    let hfa3f = c.aggregate("Hfa3f", &[Scalar::F32; 3]);

    // The Linux corpus.
    for count in [1, 2, 7, 8, 9, 12] {
        c.variadic_case(
            &format!("i64 named, {count} x i64 anonymous"),
            &vec![I64; count],
            1,
        );
        c.variadic_case(
            &format!("i64 named, {count} x f64 anonymous"),
            &cat(&[&[I64], &vec![F64; count]]),
            1,
        );
    }
    let alternating: Vec<Arg> = (0..20)
        .map(|index| if index % 2 == 0 { I64 } else { F64 })
        .collect();
    for fixed in [1, 5, 17] {
        c.variadic_case(
            &format!("20 alternating i64/f64, {fixed} named"),
            &alternating,
            fixed,
        );
    }
    c.variadic_case(
        "8 x i64, i8, i16, f32, f64 named; i64, f64 anonymous",
        &cat(&[&[I64; 8], &[I8, I16, F32, F64, I64, F64]]),
        12,
    );
    c.variadic_case(
        "i64 named; i8, u8, i16, u16, f32 anonymous (promoted)",
        &[I64, I8, U8, I16, U16, F32],
        1,
    );
    for prefix in [1, 7, 8, 9] {
        c.variadic_case(
            &format!("i64 named; {} x i64, i128, u64 anonymous", prefix - 1),
            &cat(&[&vec![I64; prefix], &[I128, U64]]),
            1,
        );
    }
    for (name, aggregate) in [("Pair", pair), ("Hfa", hfa)] {
        for prefix in [1, 7, 8, 9] {
            c.variadic_case(
                &format!("i64 named; {} x i64, {name}, u64 anonymous", prefix - 1),
                &cat(&[&vec![I64; prefix], &[aggregate, U64]]),
                1,
            );
        }
    }
    for count in [5, 6, 7, 8] {
        c.variadic_case(
            &format!("i64 named; {count} x f64, Hfa, f64 anonymous"),
            &cat(&[&[I64], &vec![F64; count], &[hfa, F64]]),
            1,
        );
    }

    // DarwinPCS shapes.
    c.variadic_case(
        "i64 named; bool, u8, bool, i16 anonymous (promoted)",
        &[I64, BOOL, U8, BOOL, I16],
        1,
    );
    c.variadic_case(
        "8 x u64, u8, i16, u8 named (packed); i64, i128, f32, bool anonymous",
        &cat(&[&[U64; 8], &[U8, I16, U8], &[I64, I128, F32, BOOL]]),
        11,
    );
    c.variadic_case(
        "8 x u64, bool named (one packed byte); i128, u8 anonymous",
        &cat(&[&[U64; 8], &[BOOL], &[I128, U8]]),
        9,
    );
    c.variadic_case(
        "8 x f64, f32, Hfa3f named (packed); f64, i64, Hfa3f anonymous",
        &cat(&[&[F64; 8], &[F32, hfa3f], &[F64, I64, hfa3f]]),
        10,
    );
    c.variadic_case(
        "8 x i64, 8 x f64 named; i64, f64, i128 anonymous",
        &cat(&[&[I64; 8], &[F64; 8], &[I64, F64, I128]]),
        16,
    );
    c.variadic_case(
        "u8, i128 named (odd register pair); i64, i128 anonymous",
        &[U8, I128, I64, I128],
        2,
    );
    c.variadic_case(
        "7 x u64, i128 named (the pair shadows X7); u8, i128 anonymous",
        &cat(&[&[U64; 7], &[I128], &[U8, I128]]),
        8,
    );
    c
}

#[test]
fn darwin_variadic_calls_match_clang_va_arg_o0_through_o3() {
    let fixture = corpus().finish();
    let executed = boundary::run_native(&fixture);
    assert_eq!(executed, fixture.checks * boundary::LEVELS.len());
    println!(
        "PASS {executed} DarwinPCS variadic checks ({} signatures at O0-O3)",
        fixture.cases
    );
}

#[test]
fn darwin_anonymous_by_reference_aggregate_fails_closed_by_name() {
    // The Linux suite passes `Big` (24 bytes, three u64) anonymously; DarwinPCS
    // passes it by reference to a caller copy, which TrustCG does not lower.
    let mut c = Corpus::new("variadic_refused");
    let big = c.aggregate("Big", &[Scalar::U64; 3]);
    c.variadic_case("i64 named; Big, u64 anonymous", &[I64, big, U64], 1);
    let fixture = c.finish();
    for level in boundary::LEVELS {
        let error = boundary::compile(&fixture.module, level)
            .expect_err("an anonymous by-reference aggregate must not compile for DarwinPCS");
        assert!(error.contains("[TCG-VARARG-ABI]"), "{level:?}: {error}");
    }
}

#[test]
fn darwin_variadic_definition_fails_closed_by_name() {
    // The clang-caller -> TrustCG-callee direction needs va_start/va_arg over
    // Apple's `char *` va_list, which TrustCG does not implement.
    let mut m = ModuleBuilder::new_with_target_info("variadic_definition", boundary::target_info());
    let sig = m.add_vararg_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut f = m.function("cg_variadic", sig);
    let entry = f.create_block();
    let first = f.add_block_param(entry, Ty::I64);
    f.switch_to_block(entry);
    f.ret(vec![first]);
    f.build();
    let module = m.build().expect("ModuleBuilder::build: test fixture");
    for level in boundary::LEVELS {
        let error =
            boundary::compile(&module, level).expect_err("a variadic definition must not compile");
        assert!(
            error.contains("[TCG-VARIADIC-DEFINITION]"),
            "{level:?}: {error}"
        );
    }
}
