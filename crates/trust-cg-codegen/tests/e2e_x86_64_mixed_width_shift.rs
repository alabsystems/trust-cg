// trust-cg-codegen/tests/e2e_x86_64_mixed_width_shift.rs
//   x86-64 shifts whose amount starts at another integer width: differential +
//   triple oracle vs clang, and the refusal of the unconverted spelling
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// A source shift's AMOUNT carries its own type: C's `a << (int)b` shifts a
// `long` by an `int`, Rust's `x << n` shifts a `u64` by an `i32` or `usize`.
// trust-ir requires both operands of a shift to have the shifted value's type
// (trust-ir-build `check_binop_operand`: `BinOpTypeMismatch` and a role-tagged
// `OperandTypeMismatch`), and every trust-cg ingestion entry refuses what that
// validator refuses (WS7.3). A producer therefore spells such an amount at the
// value's type before the shift, as the rustc bridge does
// (`shift_amount_spelling`, rustc's own `cast_shift_expr_rhs`): a NARROWER
// amount is zero-extended, a WIDER one truncated. Either conversion keeps every
// bit below the value's width, and the shift reads no other bit, so the result
// is the source's for every amount the source defines.
//
// The fixtures below are spelled that way:
//
// * `long f(long a, long b) { return a OP (int)b; }` truncates `b` to an I32
//   amount (the C cast) and zero-extends it back to I64 (the conversion) before
//   the I64 `shl`/`lshr`/`ashr`;
// * `int f(long a, long b) { return (int)a << b; }` truncates the I64 amount to
//   the I32 value's type before the I32 `shl`.
//
// The backend lowers the conversion and then the variable-count shift: x86-64
// takes the count from CL (the low 8 bits of RCX) and masks it mod the operand
// width (mod 64 for r64, mod 32 for r32), so the amount is moved into RCX/ECX
// and `SHL/SHR/SAR r, CL` executes. Each test holds that lowering, at O0, to
// clang (differential) or to clang and the trust-ir interpreter (triple
// oracle) on the inputs below. The x86-64 oracle tests return early where no
// x86-64 executor exists (see `x86_64_oracle_enabled`).
//
// The other spelling, the amount left at its own type as the shift's `rhs`
// (`BinOp { ty: I64, lhs: <I64>, rhs: <I32> }`), is ill-typed trust-ir and is
// refused at ingestion before any lowering;
// `an_amount_at_its_own_type_is_refused_by_name_at_ingestion` pins that
// refusal, by trust-ir's named findings, on every host.

mod common;
use common::x86_64_corpus::{
    TripleOracleCase, compile_trust_ir_module_x86_64, x86_64_differential_test,
    x86_64_oracle_enabled, x86_64_triple_oracle_test,
};

use trust_cg_codegen::compiler::{CompileError, Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_cg_lower::AdmissionStage;
use trust_ir::{BinOp, CastOp, Inst, InstrNode};
use trust_ir::{
    Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Module as TrustIrModule, Ty,
};
use trust_ir::{BlockId, FuncId, ValueId};
use trust_ir_build::ValidationError;

// =============================================================================
// Inline trust_ir builders
// =============================================================================

/// How a fixture spells its shift amount.
#[derive(Clone, Copy, Debug)]
enum AmountSpelling {
    /// Converted to the shifted value's type first (`ZExt` from a narrower
    /// amount, `Trunc` from a wider one): valid trust-ir, the bridge's form.
    AtValueType,
    /// Left at its own type as the shift's `rhs`: ill-typed trust-ir, refused
    /// at ingestion.
    AtOwnType,
}

/// A single-block `(i64, i64) -> returns` function `name` whose body is
/// `body`, in a module named `test`.
fn single_block_module(name: &str, returns: Ty, body: Vec<InstrNode>) -> TrustIrModule {
    let mut module = TrustIrModule::new("test");
    let ft_id = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![returns],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(FuncId::new(0), name, ft_id, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
        body,
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

fn cast(op: CastOp, src_ty: Ty, dst_ty: Ty, operand: u32, result: u32) -> InstrNode {
    InstrNode::new(Inst::Cast {
        op,
        src_ty,
        dst_ty,
        operand: ValueId::new(operand),
    })
    .with_result(ValueId::new(result))
}

/// `long NAME(long a, long b) { return a OP (int)b; }`
///
/// The shifted value `a` is I64; the source amount is `b` truncated to I32.
/// [`AmountSpelling::AtValueType`] zero-extends that I32 amount back to I64
/// and shifts `I64 OP I64`; [`AmountSpelling::AtOwnType`] shifts by the I32
/// value directly. `op` is `Shl`/`LShr`/`AShr`. Single block, no proofs
/// (unguarded => mask semantics, which the interpreter, clang, and x86
/// hardware all share on these inputs).
fn i64_shift_by_i32_amount_module(
    name: &str,
    op: BinOp,
    spelling: AmountSpelling,
) -> TrustIrModule {
    // amt: i32 = (i32) b   -- the source's narrower shift amount
    let mut body = vec![cast(CastOp::Trunc, Ty::I64, Ty::I32, 1, 2)];
    let amount = match spelling {
        AmountSpelling::AtValueType => {
            // amt64: i64 = zext amt   -- the amount at the value's type
            body.push(cast(CastOp::ZExt, Ty::I32, Ty::I64, 2, 3));
            ValueId::new(3)
        }
        AmountSpelling::AtOwnType => ValueId::new(2),
    };
    body.push(
        // r: i64 = a OP amount
        InstrNode::new(Inst::BinOp {
            op,
            ty: Ty::I64,
            lhs: ValueId::new(0),
            rhs: amount,
        })
        .with_result(ValueId::new(4)),
    );
    body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(4)],
    }));
    single_block_module(name, Ty::I64, body)
}

/// `int NAME(long a, long b) { return (int)a << b; }` — the *wider* shape: an
/// I32 shifted value with an I64 source amount (MIR shifting a 32-bit value by
/// a 64-bit `usize`). [`AmountSpelling::AtValueType`] truncates the amount to
/// I32 and shifts `I32 << I32`; [`AmountSpelling::AtOwnType`] shifts by the
/// I64 value directly. Returns I32.
fn i32_shift_by_i64_amount_module(name: &str, spelling: AmountSpelling) -> TrustIrModule {
    // val: i32 = (i32) a   -- the shifted value
    let mut body = vec![cast(CastOp::Trunc, Ty::I64, Ty::I32, 0, 2)];
    let amount = match spelling {
        AmountSpelling::AtValueType => {
            // amt32: i32 = trunc b   -- the amount at the value's type
            body.push(cast(CastOp::Trunc, Ty::I64, Ty::I32, 1, 3));
            ValueId::new(3)
        }
        AmountSpelling::AtOwnType => ValueId::new(1),
    };
    body.push(
        // r: i32 = val << amount
        InstrNode::new(Inst::BinOp {
            op: BinOp::Shl,
            ty: Ty::I32,
            lhs: ValueId::new(2),
            rhs: amount,
        })
        .with_result(ValueId::new(4)),
    );
    body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(4)],
    }));
    single_block_module(name, Ty::I32, body)
}

/// The I64 fixture every oracle test below compiles: valid trust-ir.
fn build_i64_shift_by_i32_amount_module(name: &str, op: BinOp) -> TrustIrModule {
    i64_shift_by_i32_amount_module(name, op, AmountSpelling::AtValueType)
}

/// The I32 fixture the oracle test below compiles: valid trust-ir.
fn build_i32_shift_by_i64_amount_module(name: &str) -> TrustIrModule {
    i32_shift_by_i64_amount_module(name, AmountSpelling::AtValueType)
}

/// Every shape this file covers, spelled `spelling`, with its shift's
/// `(op token, value type, source amount type)`.
fn every_shape(spelling: AmountSpelling) -> Vec<(TrustIrModule, &'static str, Ty, Ty)> {
    let mut shapes: Vec<_> = [
        (BinOp::Shl, "shl"),
        (BinOp::LShr, "lshr"),
        (BinOp::AShr, "ashr"),
    ]
    .into_iter()
    .map(|(op, token)| {
        (
            i64_shift_by_i32_amount_module(&format!("_i64_{token}_i32amt"), op, spelling),
            token,
            Ty::I64,
            Ty::I32,
        )
    })
    .collect();
    shapes.push((
        i32_shift_by_i64_amount_module("_i32_shl_i64amt", spelling),
        "shl",
        Ty::I32,
        Ty::I64,
    ));
    shapes
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). The refusal test's compile states `Permit`, as the
/// oracle harness's does, so no refusal here is the license's.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

// =============================================================================
// Admission: the converted spelling is admitted, the unconverted one refused
// =============================================================================

/// Every fixture the oracle tests compile is valid trust-ir: trust-ir's
/// codegen admission has no finding for it, and the x86-64 backend compiles
/// it (on every host; executing it is the oracle tests' part).
#[test]
fn every_fixture_spells_its_amount_at_the_value_type() {
    for (module, token, value_ty, amount_ty) in every_shape(AmountSpelling::AtValueType) {
        assert_eq!(
            trust_cg_lower::admission_findings(&module, &permit_unlicensed(), &[]),
            Vec::<ValidationError>::new(),
            "{token} {value_ty} by a {amount_ty} amount, converted: trust-ir must admit it"
        );
        compile_trust_ir_module_x86_64(&module);
    }
}

/// The unconverted spelling — the shift's `rhs` left at the source amount's
/// type — is refused by every x86-64 compile at ingestion, before lowering,
/// with exactly trust-ir's two named findings for the shift: the operands
/// disagree (`BinOpTypeMismatch`) and the `rhs` is not the declared type
/// (`OperandTypeMismatch`). trust-ir's own admission reports the same two, so
/// the refusal is trust-ir's rule and not a backend arm.
#[test]
fn an_amount_at_its_own_type_is_refused_by_name_at_ingestion() {
    for (module, token, value_ty, amount_ty) in every_shape(AmountSpelling::AtOwnType) {
        let label = format!("{token} {value_ty} by a {amount_ty} amount, unconverted");
        let expected = vec![
            ValidationError::BinOpTypeMismatch {
                block: 0,
                op: token.to_string(),
                lhs_ty: value_ty.to_string(),
                rhs_ty: amount_ty.to_string(),
            },
            ValidationError::OperandTypeMismatch {
                block: 0,
                op: token.to_string(),
                role: "rhs".to_string(),
                expected: value_ty.to_string(),
                actual: amount_ty.to_string(),
            },
        ];
        assert_eq!(
            trust_cg_lower::admission_findings(&module, &permit_unlicensed(), &[]),
            expected,
            "{label}: trust-ir's admission findings"
        );
        let error = Compiler::new(CompilerConfig {
            opt_level: OptLevel::O0,
            target: Target::X86_64,
            ..CompilerConfig::default()
        })
        .with_codegen_license(permit_unlicensed())
        .compile(&module)
        .err()
        .unwrap_or_else(|| panic!("{label}: the x86-64 compile must refuse it"));
        match error {
            CompileError::InvalidTrustIr(refusal) => {
                assert_eq!(refusal.module, "test", "{label}");
                assert_eq!(
                    refusal.stage,
                    AdmissionStage::Received,
                    "{label}: refused as received"
                );
                assert_eq!(refusal.errors, expected, "{label}: the refusal's findings");
            }
            other => panic!("{label}: expected CompileError::InvalidTrustIr, got {other:?}"),
        }
    }
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
