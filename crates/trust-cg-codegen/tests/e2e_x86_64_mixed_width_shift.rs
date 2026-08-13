// trust-cg-codegen/tests/e2e_x86_64_mixed_width_shift.rs
//   x86-64 mixed-width variable shift: differential + triple oracle vs clang
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Regression for the x86-64 ISel gap where `select_shift` rejected any shift
// whose shift-amount operand had a different integer width than the shifted
// value ("Shift lhs=I64 rhs=I32 ... require matching scalar integer operands").
//
// On x86-64 the shift COUNT is taken from CL (the low 8 bits of RCX) regardless
// of the count operand's declared width, and is masked mod the shifted operand's
// width (mod 64 for r64, mod 32 for r32). A 32-bit shift amount for a 64-bit
// shift is therefore well-defined: the amount is moved into the matching RCX
// subregister (ECX zeroes the high bits) and the hardware reads CL. This is the
// exact shape the Rust front end (the rustc bridge) emits for `i64 << (x as
// u32)`-style MIR: `BinOp { op: Shl, ty: I64, lhs: <i64>, rhs: <i32> }` with the
// shift amount carried in a narrower I32 value.
//
// The fix relaxed the operand-width acceptance only; the emitted machine
// sequence (move count -> CL, then SHL/SHR/SAR r, CL) is the same already-proven
// CL-shift lowering verified by trust-cg-verify's proof_x86_{ishl,ushr,sshr}_i64
// obligations, so no new proof was required.
//
// These tests build the modules inline (mirroring the rustc-bridge shape) and
// hold x86-64 codegen to the clang oracle (differential) and the interpreter +
// clang oracles (triple). They early-return on non-x86-64 hosts.

mod common;
use common::x86_64_corpus::{
    TripleOracleCase, x86_64_differential_test, x86_64_oracle_enabled, x86_64_triple_oracle_test,
};

use trust_ir::{BinOp, CastOp, Inst, InstrNode};
use trust_ir::{
    Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Module as TrustIrModule, Ty,
};
use trust_ir::{BlockId, FuncId, ValueId};

// =============================================================================
// Inline trust_ir builders (rustc-bridge-shaped mixed-width variable shifts)
// =============================================================================

/// `long NAME(long a, long b) { return a OP (int)b; }`
///
/// The shifted value `a` is I64; the shift amount is `b` truncated to I32, so
/// the emitted `BinOp { op, ty: I64, lhs: <I64 a>, rhs: <I32 amt> }` is a
/// genuine mixed-width shift (the shape that previously failed ISel). `op` is
/// `Shl`/`LShr`/`AShr`. Single block, no proofs (unguarded => mask semantics,
/// which the interpreter, clang, and x86 hardware all share).
fn build_i64_shift_by_i32_amount_module(name: &str, op: BinOp) -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), name, ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            // amt: i32 = (i32) b   -- the narrower shift-amount operand
            InstrNode::new(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I64,
                dst_ty: Ty::I32,
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            // r: i64 = a OP amt    -- I64 lhs, I32 shift amount
            InstrNode::new(Inst::BinOp {
                op,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

/// `int NAME(long a, long b) { return (int)a << b; }` — the *wider* shape:
/// an I32 shifted value with an I64 shift amount. x86-64 moves the I64 amount
/// into the full RCX and the 32-bit SHL reads CL. Returns I32. This mirrors
/// MIR where a 32-bit value is shifted by a 64-bit (`usize`) amount.
fn build_i32_shift_by_i64_amount_module(name: &str) -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), name, ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body: vec![
            // val: i32 = (i32) a   -- the shifted value
            InstrNode::new(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I64,
                dst_ty: Ty::I32,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(2)),
            // r: i32 = val << b    -- I32 lhs, I64 shift amount (wider)
            InstrNode::new(Inst::BinOp {
                op: BinOp::Shl,
                ty: Ty::I32,
                lhs: ValueId::new(2),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

// =============================================================================
// Differential vs clang
// =============================================================================

#[test]
fn test_x86_64_differential_i64_shl_i32_amount() {
    if !x86_64_oracle_enabled("i64_shl_i32_amount") {
        return;
    }
    let module = build_i64_shift_by_i32_amount_module("_i64_shl_i32amt", BinOp::Shl);
    let c_reference = r#"
long _i64_shl_i32amt(long a, long b) {
    return a << (int)b;
}
"#;
    let driver = r#"
#include <stdio.h>
extern long _i64_shl_i32amt(long a, long b);
int main(void) {
    printf("shl(1,0)=%ld\n",   _i64_shl_i32amt(1, 0));
    printf("shl(1,1)=%ld\n",   _i64_shl_i32amt(1, 1));
    printf("shl(1,31)=%ld\n",  _i64_shl_i32amt(1, 31));
    printf("shl(1,32)=%ld\n",  _i64_shl_i32amt(1, 32));
    printf("shl(1,63)=%ld\n",  _i64_shl_i32amt(1, 63));
    printf("shl(-1,4)=%ld\n",  _i64_shl_i32amt(-1, 4));
    printf("shl(305419896,8)=%ld\n", _i64_shl_i32amt(305419896, 8));
    return 0;
}
"#;
    let result = x86_64_differential_test("i64_shl_i32_amount", &module, c_reference, driver);
    assert!(
        result.is_ok(),
        "x86-64 i64<<i32-amount: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_differential_i64_ushr_i32_amount() {
    if !x86_64_oracle_enabled("i64_ushr_i32_amount") {
        return;
    }
    let module = build_i64_shift_by_i32_amount_module("_i64_ushr_i32amt", BinOp::LShr);
    // unsigned long so the >> is logical (zero-fill), matching Ushr/LShr.
    let c_reference = r#"
unsigned long _i64_ushr_i32amt(unsigned long a, unsigned long b) {
    return a >> (int)b;
}
"#;
    let driver = r#"
#include <stdio.h>
extern unsigned long _i64_ushr_i32amt(unsigned long a, unsigned long b);
int main(void) {
    printf("ushr(256,0)=%lu\n",  _i64_ushr_i32amt(256, 0));
    printf("ushr(256,1)=%lu\n",  _i64_ushr_i32amt(256, 1));
    printf("ushr(256,8)=%lu\n",  _i64_ushr_i32amt(256, 8));
    printf("ushr(0xFFFFFFFFFFFFFFFF,4)=%lu\n", _i64_ushr_i32amt(0xFFFFFFFFFFFFFFFFUL, 4));
    printf("ushr(0xFFFFFFFFFFFFFFFF,63)=%lu\n", _i64_ushr_i32amt(0xFFFFFFFFFFFFFFFFUL, 63));
    printf("ushr(0x8000000000000000,32)=%lu\n", _i64_ushr_i32amt(0x8000000000000000UL, 32));
    return 0;
}
"#;
    let result = x86_64_differential_test("i64_ushr_i32_amount", &module, c_reference, driver);
    assert!(
        result.is_ok(),
        "x86-64 i64>>u i32-amount: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_differential_i64_sshr_i32_amount() {
    if !x86_64_oracle_enabled("i64_sshr_i32_amount") {
        return;
    }
    let module = build_i64_shift_by_i32_amount_module("_i64_sshr_i32amt", BinOp::AShr);
    // signed long so the >> is arithmetic (sign-fill), matching Sshr/AShr.
    let c_reference = r#"
long _i64_sshr_i32amt(long a, long b) {
    return a >> (int)b;
}
"#;
    let driver = r#"
#include <stdio.h>
extern long _i64_sshr_i32amt(long a, long b);
int main(void) {
    printf("sshr(-256,0)=%ld\n", _i64_sshr_i32amt(-256, 0));
    printf("sshr(-256,1)=%ld\n", _i64_sshr_i32amt(-256, 1));
    printf("sshr(-256,8)=%ld\n", _i64_sshr_i32amt(-256, 8));
    printf("sshr(256,4)=%ld\n",  _i64_sshr_i32amt(256, 4));
    printf("sshr(-1,63)=%ld\n",  _i64_sshr_i32amt(-1, 63));
    printf("sshr(-9223372036854775808,32)=%ld\n", _i64_sshr_i32amt((-9223372036854775807L - 1L), 32));
    return 0;
}
"#;
    let result = x86_64_differential_test("i64_sshr_i32_amount", &module, c_reference, driver);
    assert!(
        result.is_ok(),
        "x86-64 i64>>s i32-amount: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_differential_i32_shl_i64_amount() {
    if !x86_64_oracle_enabled("i32_shl_i64_amount") {
        return;
    }
    let module = build_i32_shift_by_i64_amount_module("_i32_shl_i64amt");
    let c_reference = r#"
int _i32_shl_i64amt(long a, long b) {
    return (int)a << b;
}
"#;
    let driver = r#"
#include <stdio.h>
extern int _i32_shl_i64amt(long a, long b);
int main(void) {
    printf("shl(1,0)=%d\n",   _i32_shl_i64amt(1, 0));
    printf("shl(1,1)=%d\n",   _i32_shl_i64amt(1, 1));
    printf("shl(1,31)=%d\n",  _i32_shl_i64amt(1, 31));
    printf("shl(1,32)=%d\n",  _i32_shl_i64amt(1, 32));
    printf("shl(-1,4)=%d\n",  _i32_shl_i64amt(-1, 4));
    printf("shl(305419896,8)=%d\n", _i32_shl_i64amt(305419896, 8));
    return 0;
}
"#;
    let result = x86_64_differential_test("i32_shl_i64_amount", &module, c_reference, driver);
    assert!(
        result.is_ok(),
        "x86-64 i32<<i64-amount: {}",
        result.unwrap_err()
    );
}

// =============================================================================
// Triple oracle: interpreter vs Trust Codegen (x86-64) vs clang
// =============================================================================

#[test]
fn test_x86_64_triple_oracle_i64_shl_i32_amount() {
    if !x86_64_oracle_enabled("triple_i64_shl_i32_amount") {
        return;
    }
    let module = build_i64_shift_by_i32_amount_module("_i64_shl_i32amt", BinOp::Shl);
    let c_source = r#"
#include <stdio.h>
#ifdef EXTERN_ONLY
extern long _i64_shl_i32amt(long a, long b);
#else
long _i64_shl_i32amt(long a, long b) { return a << (int)b; }
#endif
int main(void) {
    printf("a=%ld\n", _i64_shl_i32amt(1, 1));
    printf("b=%ld\n", _i64_shl_i32amt(1, 31));
    printf("c=%ld\n", _i64_shl_i32amt(1, 32));
    printf("d=%ld\n", _i64_shl_i32amt(7, 60));
    return 0;
}
"#;
    let cases = vec![
        TripleOracleCase::new("a", &[1, 1]),
        TripleOracleCase::new("b", &[1, 31]),
        TripleOracleCase::new("c", &[1, 32]),
        TripleOracleCase::new("d", &[7, 60]),
    ];
    let result = x86_64_triple_oracle_test(
        "triple_i64_shl_i32_amount",
        &module,
        "_i64_shl_i32amt",
        c_source,
        &cases,
    );
    assert!(
        result.is_ok(),
        "triple i64<<i32-amount: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_triple_oracle_i64_ushr_i32_amount() {
    if !x86_64_oracle_enabled("triple_i64_ushr_i32_amount") {
        return;
    }
    let module = build_i64_shift_by_i32_amount_module("_i64_ushr_i32amt", BinOp::LShr);
    let c_source = r#"
#include <stdio.h>
#ifdef EXTERN_ONLY
extern unsigned long _i64_ushr_i32amt(unsigned long a, unsigned long b);
#else
unsigned long _i64_ushr_i32amt(unsigned long a, unsigned long b) { return a >> (int)b; }
#endif
int main(void) {
    // print as signed long to match the interpreter's i64 view of the bits.
    printf("a=%ld\n", (long)_i64_ushr_i32amt(256, 1));
    printf("b=%ld\n", (long)_i64_ushr_i32amt(256, 8));
    printf("c=%ld\n", (long)_i64_ushr_i32amt(0x7FFFFFFFFFFFFFFFUL, 4));
    return 0;
}
"#;
    let cases = vec![
        TripleOracleCase::new("a", &[256, 1]),
        TripleOracleCase::new("b", &[256, 8]),
        TripleOracleCase::new("c", &[0x7FFF_FFFF_FFFF_FFFF, 4]),
    ];
    let result = x86_64_triple_oracle_test(
        "triple_i64_ushr_i32_amount",
        &module,
        "_i64_ushr_i32amt",
        c_source,
        &cases,
    );
    assert!(
        result.is_ok(),
        "triple i64>>u i32-amount: {}",
        result.unwrap_err()
    );
}

#[test]
fn test_x86_64_triple_oracle_i64_sshr_i32_amount() {
    if !x86_64_oracle_enabled("triple_i64_sshr_i32_amount") {
        return;
    }
    let module = build_i64_shift_by_i32_amount_module("_i64_sshr_i32amt", BinOp::AShr);
    let c_source = r#"
#include <stdio.h>
#ifdef EXTERN_ONLY
extern long _i64_sshr_i32amt(long a, long b);
#else
long _i64_sshr_i32amt(long a, long b) { return a >> (int)b; }
#endif
int main(void) {
    printf("a=%ld\n", _i64_sshr_i32amt(-256, 1));
    printf("b=%ld\n", _i64_sshr_i32amt(-256, 8));
    printf("c=%ld\n", _i64_sshr_i32amt(-1, 63));
    printf("d=%ld\n", _i64_sshr_i32amt(1024, 3));
    return 0;
}
"#;
    let cases = vec![
        TripleOracleCase::new("a", &[-256, 1]),
        TripleOracleCase::new("b", &[-256, 8]),
        TripleOracleCase::new("c", &[-1, 63]),
        TripleOracleCase::new("d", &[1024, 3]),
    ];
    let result = x86_64_triple_oracle_test(
        "triple_i64_sshr_i32_amount",
        &module,
        "_i64_sshr_i32amt",
        c_source,
        &cases,
    );
    assert!(
        result.is_ok(),
        "triple i64>>s i32-amount: {}",
        result.unwrap_err()
    );
}
