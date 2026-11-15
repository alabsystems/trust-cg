// Copyright 2026 Andrew Yates | Apache-2.0
//! DarwinPCS twin of `e2e_aarch64_aggregate_stack_linux.rs`: aggregates and
//! 128-bit integers crossing the register/stack boundary, natively on
//! `aarch64-apple-darwin` with Apple clang as the oracle, in both directions
//! (clang caller -> TrustCG callee, TrustCG caller -> clang callee) at O0-O3.
//!
//! The corpus keeps the Linux suite's sixteen-aligned `Wide`/`Large` shapes and
//! prefixes, and adds the shapes on which DarwinPCS differs from AAPCS64:
//!
//! * narrow named stack arguments packed at their natural size and alignment
//!   (`u8` at `[sp]`, `i16` at `[sp, #2]`) ahead of aligned aggregates, so a
//!   following composite's start depends on the packed residue;
//! * `__int128` and sixteen-aligned composites starting in an ODD register
//!   (Apple does not round the NGRN to even), a pair that no longer fits
//!   shadowing X7 and going to a sixteen-aligned stack slot;
//! * non-homogeneous composites of at most 16 bytes, which clang coerces to
//!   `i64`/`[2 x i64]` and therefore places in 8-aligned stack slots whatever
//!   their natural alignment;
//! * HFAs of one to four members packed at their natural alignment on the
//!   stack (a `float` HFA after a packed `float` starts at `[sp, #4]`), the
//!   all-or-nothing FPR rule with no back-filling after a spilled HFA, and the
//!   HFA limits: five `float` members or mixed `float`/`double` members are
//!   not homogeneous;
//! * narrow arguments produced by truncation of dirty 64-bit carriers; `Trunc`
//!   leaves them zero-extended, so the negative `i8`/`i16` values make the
//!   clang callee's reliance on Apple's caller-side SIGN extension to 32 bits
//!   observable (caller zero extension of `bool`/`u8`/`u16` already holds
//!   before the boundary and is not independently exercised).
//!
//! Every value is folded into a 64-bit digest by the callee; the expected
//! digest is computed in Rust, so the clang-to-clang call is checked as well.
//! This is execution evidence on this host, not an ABI proof.

#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

#[path = "common/darwin_c_boundary.rs"]
mod boundary;

use boundary::{Arg, Corpus, Scalar};

const U8: Arg = Arg::S(Scalar::U8);
const I8: Arg = Arg::S(Scalar::I8);
const U16: Arg = Arg::S(Scalar::U16);
const I16: Arg = Arg::S(Scalar::I16);
const U32: Arg = Arg::S(Scalar::U32);
const I32: Arg = Arg::S(Scalar::I32);
const U64: Arg = Arg::S(Scalar::U64);
const I128: Arg = Arg::S(Scalar::I128);
const F32: Arg = Arg::S(Scalar::F32);
const F64: Arg = Arg::S(Scalar::F64);
const BOOL: Arg = Arg::S(Scalar::Bool);

fn repeat(arg: Arg, count: usize) -> Vec<Arg> {
    vec![arg; count]
}

fn cat(parts: &[&[Arg]]) -> Vec<Arg> {
    parts.concat()
}

fn corpus() -> Corpus {
    let mut c = Corpus::new("aggregate_stack");
    let wide = c.aggregate("Wide", &[Scalar::I128]);
    let large = c.aggregate("Large", &[Scalar::I128, Scalar::U64]);
    let p16 = c.aggregate("P16", &[Scalar::U64, Scalar::U64]);
    let small = c.aggregate("Small", &[Scalar::U8, Scalar::U16]);
    let w8 = c.aggregate("W8", &[Scalar::U32, Scalar::U32]);
    let s12 = c.aggregate("S12", &[Scalar::U32, Scalar::I32, Scalar::U32]);
    let hfa3f = c.aggregate("Hfa3f", &[Scalar::F32; 3]);
    let hfa4f = c.aggregate("Hfa4f", &[Scalar::F32; 4]);
    let hfa2d = c.aggregate("Hfa2d", &[Scalar::F64; 2]);
    let hfa4d = c.aggregate("Hfa4d", &[Scalar::F64; 4]);
    let f5 = c.aggregate("F5", &[Scalar::F32; 5]);
    let mixed = c.aggregate("Mixed", &[Scalar::F32, Scalar::F64]);
    let int_float = c.aggregate("IntFloat", &[Scalar::U32, Scalar::F32]);

    // The Linux suite's corpus: odd/even GPR starts, pair exhaustion and
    // NSAA residues zero/eight for a 16-aligned 16-byte and 32-byte aggregate.
    for (name, aggregate) in [("Wide", wide), ("Large", large)] {
        for prefix in [0, 1, 6, 7, 8, 9, 10, 11, 12] {
            c.case(
                &format!("{prefix} x u64, {name}, u64"),
                &cat(&[&repeat(U64, prefix), &[aggregate, U64]]),
            );
        }
    }

    // Packed narrow named stack arguments ahead of every composite class.
    let narrow_prefixes: [(&str, &[Arg]); 7] = [
        ("u8", &[U8]),
        ("i16", &[I16]),
        ("u8,i16", &[U8, I16]),
        ("u32", &[U32]),
        ("u8,u8,u8", &[U8, U8, U8]),
        ("bool,i8,u16,u32", &[BOOL, I8, U16, U32]),
        ("i32,u8", &[I32, U8]),
    ];
    let composites = [
        ("Wide", wide),
        ("P16", p16),
        ("Small", small),
        ("W8", w8),
        ("S12", s12),
        ("Large", large),
        ("i128", I128),
    ];
    for (prefix_name, prefix) in narrow_prefixes {
        for (name, composite) in composites {
            c.case(
                &format!("8 x u64, {prefix_name}, {name}, u8, u64"),
                &cat(&[&repeat(U64, 8), prefix, &[composite, U8, U64]]),
            );
        }
    }

    // Odd-register starts and the X7 shadow for 16-aligned values.
    for (name, value) in [("Wide", wide), ("i128", I128), ("P16", p16), ("S12", s12)] {
        for prefix in [1, 3, 5, 6, 7] {
            c.case(
                &format!("{prefix} x u8, {name}, u16"),
                &cat(&[&repeat(U8, prefix), &[value, U16]]),
            );
        }
    }
    c.case(
        "u8, i128, u8, i128, u8, i128 (the third pair shadows X7)",
        &[U8, I128, U8, I128, U8, I128],
    );
    c.case("4 x i128, u8", &[I128, I128, I128, I128, U8]);
    c.case(
        "8 x u64, u8, i128, u8, Wide, i16",
        &cat(&[&repeat(U64, 8), &[U8, I128, U8, wide, I16]]),
    );

    // HFAs: natural-alignment stack packing, all-or-nothing FPR allocation,
    // no back-filling, and the membership limits.
    for (name, hfa) in [
        ("Hfa3f", hfa3f),
        ("Hfa4f", hfa4f),
        ("Hfa2d", hfa2d),
        ("Hfa4d", hfa4d),
    ] {
        c.case(
            &format!("8 x f64, f32, {name}, f32, f64"),
            &cat(&[&repeat(F64, 8), &[F32, hfa, F32, F64]]),
        );
        c.case(
            &format!("8 x f64, f32, f32, f32, {name}, f32"),
            &cat(&[&repeat(F64, 8), &[F32, F32, F32, hfa, F32]]),
        );
        for prefix in [4, 5, 6, 7] {
            c.case(
                &format!("{prefix} x f64, {name}, f32, f64"),
                &cat(&[&repeat(F64, prefix), &[hfa, F32, F64]]),
            );
        }
    }
    c.case("F5 (not an HFA), f32", &[f5, F32]);
    c.case(
        "8 x u64, F5 by reference on the stack, u8",
        &cat(&[&repeat(U64, 8), &[f5, U8]]),
    );
    c.case("Mixed (not an HFA), u64", &[mixed, U64]);
    c.case(
        "7 x u64, Mixed, u8 (the pair does not fit)",
        &cat(&[&repeat(U64, 7), &[mixed, U8]]),
    );
    c.case("IntFloat, f32", &[int_float, F32]);
    c.case(
        "8 x u64, u16, IntFloat, u8",
        &cat(&[&repeat(U64, 8), &[U16, int_float, U8]]),
    );

    // Both banks exhausted, then every stack class interleaved.
    c.case(
        "8 x u64, 8 x f64, u8, f32, i16, Hfa3f, Small, Wide, f32, u64, bool, Hfa2d",
        &cat(&[
            &repeat(U64, 8),
            &repeat(F64, 8),
            &[U8, F32, I16, hfa3f, small, wide, F32, U64, BOOL, hfa2d],
        ]),
    );
    c.case(
        "u8, f32, i16, f64, Wide, Hfa3f, u32, P16, Hfa4d, i128, f32, S12, bool, u64",
        &[
            U8, F32, I16, F64, wide, hfa3f, U32, p16, hfa4d, I128, F32, s12, BOOL, U64,
        ],
    );

    // CG caller -> clang variadic callee with aggregates and i128 in the
    // anonymous tail (the Linux suite's va_arg helpers). DarwinPCS passes every
    // anonymous argument on the stack; sixteen-aligned ones at a 16-aligned
    // offset. `Large` is refused by name below.
    for (name, value) in [
        ("Wide", wide),
        ("i128", I128),
        ("P16", p16),
        ("Small", small),
        ("S12", s12),
        ("Hfa3f", hfa3f),
        ("Hfa4d", hfa4d),
    ] {
        for prefix in [1, 2, 7, 8, 9] {
            let params = cat(&[&repeat(U64, prefix), &[value, U64]]);
            c.variadic_case(
                &format!("{prefix} x u64, {name}, u64 with one named argument"),
                &params,
                1,
            );
            if prefix > 1 {
                c.variadic_case(
                    &format!("{prefix} x u64, {name}, u64 with {prefix} named arguments"),
                    &params,
                    prefix,
                );
            }
        }
    }
    c.variadic_case(
        "8 x u64, u8, i16 named; Wide, u8, i128 anonymous",
        &cat(&[&repeat(U64, 8), &[U8, I16, wide, U8, I128]]),
        10,
    );
    c
}

#[test]
fn darwin_aggregate_stack_matches_clang_both_directions_o0_through_o3() {
    let fixture = corpus().finish();
    let executed = boundary::run_native(&fixture);
    assert_eq!(executed, fixture.checks * boundary::LEVELS.len());
    println!(
        "PASS {executed} DarwinPCS aggregate/stack boundary checks ({} signatures at O0-O3)",
        fixture.cases
    );
}

#[test]
fn darwin_large_anonymous_aggregate_fails_closed_by_name() {
    // DarwinPCS passes a non-homogeneous anonymous aggregate over 16 bytes by
    // reference to a caller copy; TrustCG does not lower that placement.
    let mut c = Corpus::new("aggregate_stack_refused");
    let large = c.aggregate("Large", &[Scalar::I128, Scalar::U64]);
    c.variadic_case("u64, Large, u64", &[U64, large, U64], 1);
    let fixture = c.finish();
    for level in boundary::LEVELS {
        let error = boundary::compile(&fixture.module, level)
            .expect_err("an anonymous by-reference aggregate must not compile for DarwinPCS");
        assert!(error.contains("[TCG-VARARG-ABI]"), "{level:?}: {error}");
    }
}
