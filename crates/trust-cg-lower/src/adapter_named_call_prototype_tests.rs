// trust-cg-lower/adapter_named_call_prototype_tests.rs - a direct call is
// lowered by its callee's name only with the prototype that name needs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `classify_direct_call` reads a callee's name and its declared prototype
//! together (LD-100 in `docs/decision-record.md`):
//!
//! * `memcpy`, `memmove` and `memset` are the C library routines only when
//!   declared with C's prototype on an LP64 target and C's convention; any
//!   other declaration is an ordinary call of that symbol;
//! * an LLVM intrinsic name declared at another type than its own is refused
//!   by name.
//!
//! One case per rule of the gate (each fails when that rule is mutated away)
//! and the controls that keep the C and LLVM forms lowered as before. The
//! adapter's own `Inst::Call` lowering of the L02-P15 re-check's reproducers
//! is `tests/named_call_prototype.rs` (public API, so it also runs against an
//! adapter without the gate).

use super::*;
use trust_ir::FuncTy;

fn declaration(name: &str, conv: CallingConv) -> TrustIrFunction {
    let mut function =
        TrustIrFunction::new(FuncId::new(0), name, FuncTyId::new(0), BlockId::new(0));
    function.calling_conv = conv;
    function
}

fn signature(params: Vec<Ty>, returns: Vec<Ty>) -> FuncTy {
    FuncTy::unrecorded(params, returns, false)
}

fn classify_as(
    name: &str,
    conv: CallingConv,
    signature: &FuncTy,
) -> Result<AdapterNamedCallSemantics, String> {
    classify_direct_call(name, &declaration(name, conv), signature)
        .map(|semantics| AdapterNamedCallSemantics::of(&semantics))
}

fn classify(name: &str, signature: &FuncTy) -> Result<AdapterNamedCallSemantics, String> {
    classify_as(name, CallingConv::C, signature)
}

fn byte_ptr_mut() -> Ty {
    Ty::PtrMut(Box::new(Ty::U8))
}

fn byte_ptr_const() -> Ty {
    Ty::PtrConst(Box::new(Ty::U8))
}

/// The C library's prototypes, as the LLVM importer spells them (`ptr`,
/// `i32`, `i64`) and as the rustc bridge does (`*mut u8`, `*const u8`, `i32`,
/// `usize` mapped to `U64`), keep their library meaning.
#[test]
fn c_prototype_memory_calls_keep_their_library_meaning() {
    let copy = signature(vec![Ty::Ptr, Ty::Ptr, Ty::I64], vec![Ty::Ptr]);
    let fill = signature(vec![Ty::Ptr, Ty::I32, Ty::I64], vec![Ty::Ptr]);
    let bridge_copy = signature(
        vec![byte_ptr_mut(), byte_ptr_const(), Ty::U64],
        vec![byte_ptr_mut()],
    );
    let bridge_fill = signature(vec![byte_ptr_mut(), Ty::I32, Ty::U64], vec![byte_ptr_mut()]);
    for (name, sig, expected) in [
        ("memcpy", &copy, AdapterNamedCallSemantics::Memcpy),
        ("memmove", &copy, AdapterNamedCallSemantics::Memmove),
        ("memset", &fill, AdapterNamedCallSemantics::Memset),
        ("memcpy", &bridge_copy, AdapterNamedCallSemantics::Memcpy),
        ("memmove", &bridge_copy, AdapterNamedCallSemantics::Memmove),
        ("memset", &bridge_fill, AdapterNamedCallSemantics::Memset),
    ] {
        assert_eq!(classify(name, sig), Ok(expected), "{name} {sig:?}");
    }
    // `size_t` and `int` are read by width: the pointer-width and the
    // unsigned spellings are the same C argument.
    let usize_count = signature(vec![Ty::Ptr, Ty::Ptr, Ty::Usize], vec![Ty::Ptr]);
    assert_eq!(
        classify("memcpy", &usize_count),
        Ok(AdapterNamedCallSemantics::Memcpy)
    );
    let unsigned_fill = signature(vec![Ty::Ptr, Ty::U32, Ty::U64], vec![Ty::Ptr]);
    assert_eq!(
        classify("memset", &unsigned_fill),
        Ok(AdapterNamedCallSemantics::Memset)
    );
}

/// Each rule of the C prototype, one departure at a time: every such
/// declaration is an ordinary function of the library's name.
#[test]
fn a_memory_routine_declared_otherwise_is_an_ordinary_call() {
    let ptr = || Ty::Ptr;
    let cases: Vec<(&str, FuncTy, &str)> = vec![
        // n1_memcpy_ints: three integers in, one out.
        (
            "memcpy",
            signature(vec![Ty::I64, Ty::I64, Ty::I64], vec![Ty::I64]),
            "integer arguments and result",
        ),
        // n2_memset_ret_count: the result is not a pointer.
        (
            "memset",
            signature(vec![ptr(), Ty::I32, Ty::I64], vec![Ty::I64]),
            "integer result",
        ),
        // n3_memmove_ret_i32.
        (
            "memmove",
            signature(vec![ptr(), ptr(), Ty::I64], vec![Ty::I32]),
            "i32 result",
        ),
        (
            "memcpy",
            signature(vec![ptr(), ptr(), Ty::I64], vec![]),
            "no result",
        ),
        (
            "memcpy",
            signature(vec![ptr(), ptr(), Ty::I64], vec![ptr(), ptr()]),
            "two results",
        ),
        (
            "memcpy",
            signature(vec![Ty::I64, ptr(), Ty::I64], vec![ptr()]),
            "integer destination",
        ),
        (
            "memmove",
            signature(vec![ptr(), Ty::I64, Ty::I64], vec![ptr()]),
            "integer source",
        ),
        (
            "memcpy",
            signature(vec![ptr(), ptr(), Ty::I32], vec![ptr()]),
            "32-bit count",
        ),
        (
            "memcpy",
            signature(vec![ptr(), ptr(), Ty::I128], vec![ptr()]),
            "128-bit count",
        ),
        (
            "memcpy",
            signature(vec![ptr(), ptr(), ptr()], vec![ptr()]),
            "pointer count",
        ),
        (
            "memset",
            signature(vec![ptr(), Ty::I8, Ty::I64], vec![ptr()]),
            "8-bit fill",
        ),
        (
            "memset",
            signature(vec![ptr(), Ty::I16, Ty::I64], vec![ptr()]),
            "16-bit fill",
        ),
        (
            "memset",
            signature(vec![ptr(), Ty::I64, Ty::I64], vec![ptr()]),
            "64-bit fill",
        ),
        (
            "memset",
            signature(vec![ptr(), ptr(), Ty::I64], vec![ptr()]),
            "pointer fill",
        ),
        (
            "memcpy",
            signature(vec![ptr(), ptr()], vec![ptr()]),
            "two parameters",
        ),
        (
            "memcpy",
            signature(vec![ptr(), ptr(), Ty::I64, Ty::I64], vec![ptr()]),
            "four parameters",
        ),
        (
            "memcpy",
            signature(
                vec![ptr(), ptr(), Ty::I64],
                vec![Ty::Func(FuncTyId::new(0))],
            ),
            "function-pointer result",
        ),
        (
            "memcpy",
            FuncTy::unrecorded(vec![ptr(), ptr(), Ty::I64], vec![ptr()], true),
            "variadic",
        ),
    ];
    for (name, sig, why) in &cases {
        assert_eq!(
            classify(name, sig),
            Ok(AdapterNamedCallSemantics::Ordinary),
            "{name} ({why}): {sig:?}"
        );
    }
    // Another calling convention than C's, the prototype otherwise C's.
    let copy = signature(vec![Ty::Ptr, Ty::Ptr, Ty::I64], vec![Ty::Ptr]);
    for conv in [
        CallingConv::Fast,
        CallingConv::Cold,
        CallingConv::Rust,
        CallingConv::CUnwind,
    ] {
        assert_eq!(
            classify_as("memcpy", conv, &copy),
            Ok(AdapterNamedCallSemantics::Ordinary),
            "{conv:?}"
        );
    }
}

/// A module-local definition keeps its body whatever its name and prototype.
#[test]
fn a_module_local_definition_keeps_its_body() {
    let copy = signature(vec![Ty::Ptr, Ty::Ptr, Ty::I64], vec![Ty::Ptr]);
    for linkage in [Linkage::Internal, Linkage::Private] {
        let mut function = declaration("memcpy", CallingConv::C);
        function.linkage = linkage;
        function.blocks = vec![TrustIrBlock {
            id: BlockId::new(0),
            params: Vec::new(),
            body: vec![InstrNode::new(Inst::Unreachable)],
        }];
        assert!(matches!(
            classify_direct_call("memcpy", &function, &copy),
            Ok(NamedCallSemantics::Ordinary)
        ));
    }
}

/// LLVM's memory intrinsics at their own type (the volatile flag dropped by
/// the importer) keep their meaning; LLVM ignores an intrinsic's convention.
#[test]
fn llvm_memory_intrinsics_at_their_type_keep_their_meaning() {
    let copy64 = signature(vec![Ty::Ptr, Ty::Ptr, Ty::I64], vec![]);
    let copy32 = signature(vec![Ty::Ptr, Ty::Ptr, Ty::I32], vec![]);
    let fill = signature(vec![Ty::Ptr, Ty::I8, Ty::I64], vec![]);
    for (name, sig, expected) in [
        (
            "llvm.memcpy.p0.p0.i64",
            &copy64,
            AdapterNamedCallSemantics::Memcpy,
        ),
        (
            "llvm.memcpy.p0.p0.i32",
            &copy32,
            AdapterNamedCallSemantics::Memcpy,
        ),
        (
            "llvm.memmove.p0.p0.i64",
            &copy64,
            AdapterNamedCallSemantics::Memmove,
        ),
        (
            "llvm.memset.p0.i64",
            &fill,
            AdapterNamedCallSemantics::Memset,
        ),
    ] {
        assert_eq!(classify(name, sig), Ok(expected), "{name}");
        assert_eq!(
            classify_as(name, CallingConv::Fast, sig),
            Ok(expected),
            "{name} fastcc"
        );
    }
}

/// An LLVM intrinsic name declared at another type is refused by name.
#[test]
fn an_llvm_intrinsic_name_at_another_type_is_refused() {
    let ptr = || Ty::Ptr;
    let cases: Vec<(&str, FuncTy)> = vec![
        // The C library's prototype under the intrinsic's name.
        (
            "llvm.memcpy.p0.p0.i64",
            signature(vec![ptr(), ptr(), Ty::I64], vec![ptr()]),
        ),
        // The volatile flag kept.
        (
            "llvm.memcpy.p0.p0.i64",
            signature(vec![ptr(), ptr(), Ty::I64, Ty::Bool], vec![]),
        ),
        (
            "llvm.memmove.p0.p0.i64",
            signature(vec![ptr(), Ty::I64, Ty::I64], vec![]),
        ),
        (
            "llvm.memcpy.p0.p0.i64",
            signature(vec![ptr(), ptr(), Ty::I16], vec![]),
        ),
        (
            "llvm.memset.p0.i64",
            signature(vec![ptr(), Ty::I32, Ty::I64], vec![]),
        ),
        (
            "llvm.memset.p0.i64",
            signature(vec![Ty::I64, Ty::I8, Ty::I64], vec![]),
        ),
        (
            "llvm.memset.p0.i64",
            FuncTy::unrecorded(vec![ptr(), Ty::I8, Ty::I64], vec![], true),
        ),
        (
            "llvm.bitreverse.i32",
            signature(vec![Ty::I64], vec![Ty::I64]),
        ),
        (
            "llvm.bitreverse.i64",
            signature(vec![Ty::I64], vec![Ty::I32]),
        ),
        (
            "llvm.objectsize.i64.p0",
            signature(vec![ptr(), Ty::I8, Ty::Bool, Ty::Bool], vec![Ty::I64]),
        ),
        (
            "llvm.objectsize.i64.p0",
            signature(vec![Ty::I64, Ty::Bool, Ty::Bool, Ty::Bool], vec![Ty::I64]),
        ),
        (
            "llvm.objectsize.i64.p0",
            signature(vec![ptr(), Ty::Bool, Ty::Bool, Ty::Bool], vec![Ty::I32]),
        ),
        (
            "llvm.fma.f64",
            signature(vec![Ty::F32, Ty::F32, Ty::F32], vec![Ty::F32]),
        ),
        (
            "llvm.fmuladd.f32",
            signature(vec![Ty::I32, Ty::I32, Ty::I32], vec![Ty::I32]),
        ),
        (
            "llvm.fmuladd.v4f32",
            signature(
                vec![
                    Ty::Vector(Box::new(Ty::F64), 2),
                    Ty::Vector(Box::new(Ty::F64), 2),
                    Ty::Vector(Box::new(Ty::F64), 2),
                ],
                vec![Ty::Vector(Box::new(Ty::F64), 2)],
            ),
        ),
    ];
    for (name, sig) in &cases {
        let refusal = classify(name, sig).expect_err(name);
        assert!(
            refusal.contains("[TCG-NAMED-CALL-PROTOTYPE]") && refusal.contains(name),
            "{name}: {refusal}"
        );
    }
    let crc = classify(
        "llvm.aarch64.crc32w",
        &signature(vec![Ty::U64, Ty::U64], vec![Ty::U64]),
    )
    .expect_err("crc32w at u64");
    assert!(crc.contains("[TCG-CRC32-INTRINSIC]"), "{crc}");
    let variadic_crc = classify(
        "llvm.aarch64.crc32w",
        &FuncTy::unrecorded(vec![Ty::U32, Ty::U32], vec![Ty::U32], true),
    )
    .expect_err("variadic crc32w");
    assert!(
        variadic_crc.contains("[TCG-CRC32-INTRINSIC]"),
        "{variadic_crc}"
    );
}

/// The value intrinsics at their own types keep their meaning.
#[test]
fn llvm_value_intrinsics_at_their_type_keep_their_meaning() {
    let v4f32 = || Ty::Vector(Box::new(Ty::F32), 4);
    let v2f64 = || Ty::Vector(Box::new(Ty::F64), 2);
    for (name, sig, expected) in [
        (
            "llvm.bitreverse.i32",
            signature(vec![Ty::I32], vec![Ty::I32]),
            AdapterNamedCallSemantics::Bitreverse,
        ),
        (
            "llvm.bitreverse.i64",
            signature(vec![Ty::U64], vec![Ty::U64]),
            AdapterNamedCallSemantics::Bitreverse,
        ),
        (
            "llvm.objectsize.i64.p0",
            signature(vec![Ty::Ptr, Ty::Bool, Ty::Bool, Ty::Bool], vec![Ty::I64]),
            AdapterNamedCallSemantics::Objectsize,
        ),
        (
            "llvm.fma.f64",
            signature(vec![Ty::F64, Ty::F64, Ty::F64], vec![Ty::F64]),
            AdapterNamedCallSemantics::Fma,
        ),
        (
            "llvm.fmuladd.f32",
            signature(vec![Ty::F32, Ty::F32, Ty::F32], vec![Ty::F32]),
            AdapterNamedCallSemantics::Fma,
        ),
        (
            "llvm.fmuladd.v4f32",
            signature(vec![v4f32(), v4f32(), v4f32()], vec![v4f32()]),
            AdapterNamedCallSemantics::PackedFma,
        ),
        (
            "llvm.fmuladd.v2f64",
            signature(vec![v2f64(), v2f64(), v2f64()], vec![v2f64()]),
            AdapterNamedCallSemantics::PackedFma,
        ),
        (
            "llvm.aarch64.crc32cx",
            signature(vec![Ty::U32, Ty::U64], vec![Ty::U32]),
            AdapterNamedCallSemantics::Crc32,
        ),
    ] {
        assert_eq!(classify(name, &sig), Ok(expected), "{name}");
    }
}

/// The public reading (`classify_adapter_direct_call`) is this one decision.
#[test]
fn the_public_reading_is_the_lowering_decision() {
    let ints = signature(vec![Ty::I64, Ty::I64, Ty::I64], vec![Ty::I64]);
    let copy = signature(vec![Ty::Ptr, Ty::Ptr, Ty::I64], vec![Ty::Ptr]);
    let function = declaration("memcpy", CallingConv::C);
    assert_eq!(
        classify_adapter_direct_call("memcpy", &function, &ints),
        Ok(AdapterNamedCallSemantics::Ordinary)
    );
    assert_eq!(
        classify_adapter_direct_call("memcpy", &function, &copy),
        Ok(AdapterNamedCallSemantics::Memcpy)
    );
    // The name's claim alone is unchanged.
    assert_eq!(
        classify_adapter_named_call("memcpy"),
        AdapterNamedCallSemantics::Memcpy
    );
}
