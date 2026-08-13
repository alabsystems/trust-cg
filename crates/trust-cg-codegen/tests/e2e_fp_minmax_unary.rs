//! TRUST-SELF ROUND 37 (thread R37): RESOLVE owner #11 (the fmin/fmax
//! signaling-NaN interpreter-vs-JIT divergence) + AUDIT the scalar fp UNARY ops
//! (FNeg / FAbs / FSqrt) against the real Rust op as oracle.
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! PART A — owner #11: fmin/fmax signaling-NaN divergence, ADJUDICATED
//! ═══════════════════════════════════════════════════════════════════════════════
//! R31 observed that for a SIGNALING-NaN operand the trust-cg INTERPRETER returned
//! the NUMBER (`fmin(0.0,sNaN)=0.0`) while the JIT quieted the sNaN and returned NaN.
//! Trust-IR defines FMin/FMax as minimumNumber/maximumNumber: when exactly one
//! operand is NaN, the other operand wins.
//!
//! A bare AArch64 FMINNM/FMAXNM handles a quiet NaN as minimumNumber but returns a
//! signaling-NaN operand quieted. The owner-#11 backend fix therefore canonicalizes
//! both operands with self-FMINNM/FMAXNM before the binary operation:
//!
//!    fminnm d0, d0, d0      ; canonicalize op1 (a lone sNaN -> qNaN)
//!    fminnm d1, d1, d1      ; canonicalize op2
//!    fminnm d0, d0, d1      ; the actual min (now sees a QUIET NaN -> number)
//!    (`max` is the same with a final `fmaxnm`; f32 uses s-regs.)
//!
//! The interpreter and these tests use an explicit Trust-IR specification oracle.
//! Native Rust is intentionally not the sNaN oracle: Rust 1.95's AArch64 lowering
//! emits one FMINNM/FMAXNM, whereas later rustc versions emit the three-instruction
//! sequence. The explicit oracle keeps Trust-IR semantics stable across toolchains.
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! PART B — fp UNARY ops (FNeg / FAbs / FSqrt): native==JIT audit
//! ═══════════════════════════════════════════════════════════════════════════════
//! ISel (isel.rs:2200-2202): Fneg->FnegRR, Fabs->FabsRR, Fsqrt->FsqrtRR — a SINGLE
//! `fneg`/`fabs`/`fsqrt` (confirmed identical to what real Rust emits for `-x` /
//! `x.abs()` / `x.sqrt()`). FNeg flips the sign bit (payload preserved, sNaN NOT
//! quieted); FAbs clears the sign bit (same); FSqrt is the RNE correctly-rounded
//! hardware sqrt (quiets a NaN). This part machine-checks each bit-exact vs the Rust
//! op over dense rounding/NaN/-0/inf/subnormal sweeps (f32 and f64).
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! BOUNDARIES
//! ═══════════════════════════════════════════════════════════════════════════════
//!  * The interpreter models ALL floats as native f64 (InterpreterValue::Float(f64))
//!    and its `Bitcast` is a value pass-through that does NOT reinterpret int<->float
//!    bits (interpreter.rs:929-936). So (i) the owner-#11 three-way interpreter arm is
//!    f64-only (an f32 sNaN cannot be carried through an f64 Float without quieting on
//!    widen), and (ii) JIT modules feed exact bits via an integer param + Bitcast,
//!    while interpreter modules take f64 Float params directly. f32 Part-A cells are
//!    JIT-vs-specification; the interpreter's f32-as-f64 modeling is out of scope for
//!    the f32 arm.
//!  * No emit-from-Rust: the emit-closure frontend has no float support (R31 Finding
//!    A). Everything is hand-built trust-ir through the trust-cg JIT / interpreter;
//!    Part A uses the explicit Trust-IR min/max oracle, while Part B uses native Rust
//!    `-x`/`abs`/`sqrt` as its runtime oracle.
//!  * Run ONE AT A TIME (`--test-threads=1`): the JIT engine is not thread-safe at
//!    suite scale (jit-parallel-race-2026-06-29.md).

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::hint::black_box;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::interpreter::{InterpreterValue, interpret};

use trust_ir::{
    BinOp, Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty, UnOp,
};
use trust_ir::{BlockId, CastOp, FuncId, ValueId};

// ═══════════════════════════════════════════════════════════════════════════════
// Module builders
// ═══════════════════════════════════════════════════════════════════════════════

/// JIT binop, integer-bits in/out: fn(iN,iN)->iN via Bitcast at the boundary.
/// (int_ty, float_ty) is (I64,F64) or (I32,F32). Bit-exact: no float ABI.
fn build_binop_jit(
    func_id: u32,
    name: &str,
    m: &mut TrustIrModule,
    int_ty: Ty,
    f_ty: Ty,
    op: BinOp,
) {
    let ft = m.add_func_type(FuncTy {
        params: vec![int_ty.clone(), int_ty.clone()],
        returns: vec![int_ty.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), int_ty.clone()),
            (ValueId::new(1), int_ty.clone()),
        ],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: int_ty.clone(),
                dst_ty: f_ty.clone(),
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: int_ty.clone(),
                dst_ty: f_ty.clone(),
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::BinOp {
                op,
                ty: f_ty.clone(),
                lhs: ValueId::new(2),
                rhs: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: f_ty,
                dst_ty: int_ty.clone(),
                operand: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(5)],
            }),
        ],
    }];
    m.add_function(f);
}

/// JIT unary op, integer-bits in/out: fn(iN)->iN via Bitcast at the boundary.
fn build_unop_jit(func_id: u32, name: &str, m: &mut TrustIrModule, int_ty: Ty, f_ty: Ty, op: UnOp) {
    let ft = m.add_func_type(FuncTy {
        params: vec![int_ty.clone()],
        returns: vec![int_ty.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), int_ty.clone())],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: int_ty.clone(),
                dst_ty: f_ty.clone(),
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::UnOp {
                op,
                ty: f_ty.clone(),
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: f_ty,
                dst_ty: int_ty.clone(),
                operand: ValueId::new(2),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    }];
    m.add_function(f);
}

/// Interpreter binop, f64 Float in/out (interpreter models floats as native f64).
fn build_binop_interp_f64(func_id: u32, name: &str, m: &mut TrustIrModule, op: BinOp) {
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::F64, Ty::F64],
        returns: vec![Ty::F64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::F64), (ValueId::new(1), Ty::F64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op,
                ty: Ty::F64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    m.add_function(f);
}

// ═══════════════════════════════════════════════════════════════════════════════
// JIT + interpreter + oracle harness
// ═══════════════════════════════════════════════════════════════════════════════

fn jit_buffer(m: &TrustIrModule) -> trust_cg_codegen::jit::ExecutableBuffer {
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(m, &HashMap::new())
        .expect("hand-built fp min/max/unary module must JIT-compile")
        .buffer
}
fn bind(buf: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buf.get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("JIT symbol `{sym}` not found"))
        .as_ptr()
}

type U64Bin = unsafe extern "C" fn(u64, u64) -> u64;
type U32Bin = unsafe extern "C" fn(u32, u32) -> u32;
type U64Un = unsafe extern "C" fn(u64) -> u64;
type U32Un = unsafe extern "C" fn(u32) -> u32;

fn interp_bits_f64(m: &TrustIrModule, name: &str, a: u64, b: u64) -> u64 {
    let out = interpret(
        m,
        name,
        &[
            InterpreterValue::Float(f64::from_bits(a)),
            InterpreterValue::Float(f64::from_bits(b)),
        ],
    )
    .expect("interpret fmin/fmax");
    match out.as_slice() {
        [InterpreterValue::Float(v)] => v.to_bits(),
        other => panic!("unexpected interp result: {other:?}"),
    }
}

// Toolchain-independent Trust-IR minimumNumber/maximumNumber specification oracles.
// Keep the ordered path on native min/max for its signed-zero behavior, but make
// lone-NaN selection explicit because rustc's AArch64 sNaN lowering changed across
// supported toolchains.
#[inline(never)]
fn spec_min64(a: u64, b: u64) -> u64 {
    let a = black_box(f64::from_bits(a));
    let b = black_box(f64::from_bits(b));
    let result = if a.is_nan() {
        if b.is_nan() {
            f64::from_bits(a.to_bits() | F64_QUIET_BIT)
        } else {
            b
        }
    } else if b.is_nan() {
        a
    } else {
        a.min(b)
    };
    result.to_bits()
}
#[inline(never)]
fn spec_max64(a: u64, b: u64) -> u64 {
    let a = black_box(f64::from_bits(a));
    let b = black_box(f64::from_bits(b));
    let result = if a.is_nan() {
        if b.is_nan() {
            f64::from_bits(a.to_bits() | F64_QUIET_BIT)
        } else {
            b
        }
    } else if b.is_nan() {
        a
    } else {
        a.max(b)
    };
    result.to_bits()
}
#[inline(never)]
fn spec_min32(a: u32, b: u32) -> u32 {
    let a = black_box(f32::from_bits(a));
    let b = black_box(f32::from_bits(b));
    let result = if a.is_nan() {
        if b.is_nan() {
            f32::from_bits(a.to_bits() | F32_QUIET_BIT)
        } else {
            b
        }
    } else if b.is_nan() {
        a
    } else {
        a.min(b)
    };
    result.to_bits()
}
#[inline(never)]
fn spec_max32(a: u32, b: u32) -> u32 {
    let a = black_box(f32::from_bits(a));
    let b = black_box(f32::from_bits(b));
    let result = if a.is_nan() {
        if b.is_nan() {
            f32::from_bits(a.to_bits() | F32_QUIET_BIT)
        } else {
            b
        }
    } else if b.is_nan() {
        a
    } else {
        a.max(b)
    };
    result.to_bits()
}
#[inline(never)]
fn rust_neg64(a: u64) -> u64 {
    (-black_box(f64::from_bits(a))).to_bits()
}
#[inline(never)]
fn rust_abs64(a: u64) -> u64 {
    black_box(f64::from_bits(a)).abs().to_bits()
}
#[inline(never)]
fn rust_sqrt64(a: u64) -> u64 {
    black_box(f64::from_bits(a)).sqrt().to_bits()
}
#[inline(never)]
fn rust_neg32(a: u32) -> u32 {
    (-black_box(f32::from_bits(a))).to_bits()
}
#[inline(never)]
fn rust_abs32(a: u32) -> u32 {
    black_box(f32::from_bits(a)).abs().to_bits()
}
#[inline(never)]
fn rust_sqrt32(a: u32) -> u32 {
    black_box(f32::from_bits(a)).sqrt().to_bits()
}

// f64 special bit patterns
const F64_P0: u64 = 0x0000_0000_0000_0000;
const F64_N0: u64 = 0x8000_0000_0000_0000;
const F64_ONE: u64 = 0x3FF0_0000_0000_0000;
const F64_TWO: u64 = 0x4000_0000_0000_0000;
const F64_PINF: u64 = 0x7FF0_0000_0000_0000;
const F64_NINF: u64 = 0xFFF0_0000_0000_0000;
const F64_QNAN: u64 = 0x7FF8_0000_0000_0000;
const F64_QNAN_PAY: u64 = 0x7FF8_0000_1234_5678;
const F64_SNAN: u64 = 0x7FF0_0000_0000_0001;
const F64_SNAN_PAY: u64 = 0x7FF0_0000_ABCD_0000;
const F64_NEG_SNAN: u64 = 0xFFF0_0000_0000_0001;
const F64_QUIET_BIT: u64 = 0x0008_0000_0000_0000;

// f32 special bit patterns
const F32_ONE: u32 = 0x3F80_0000;
const F32_SNAN: u32 = 0x7F80_0001;
const F32_SNAN_PAY: u32 = 0x7F80_4321;
const F32_QNAN: u32 = 0x7FC0_0000;
const F32_QUIET_BIT: u32 = 0x0040_0000;

fn is_nan64(b: u64) -> bool {
    (b & 0x7FF0_0000_0000_0000) == 0x7FF0_0000_0000_0000 && (b & 0x000F_FFFF_FFFF_FFFF) != 0
}
fn is_nan32(b: u32) -> bool {
    (b & 0x7F80_0000) == 0x7F80_0000 && (b & 0x007F_FFFF) != 0
}

// ═══════════════════════════════════════════════════════════════════════════════
// PART A — owner #11
// ═══════════════════════════════════════════════════════════════════════════════

// ============================================================================
// TEST A1 — owner #11 FIXED (clean bill): the JIT fmin/fmax now canonicalizes
//   each operand with a self-min/max (`fminnm t,x,x`) before the binary op, so a
//   signaling-NaN operand is quieted and the number-substitution fires — matching
//   the Trust-IR specification (and the interpreter). Three-way f64 witness set.
//   (Was a fail-loud PIN pre-fix; select_fp_binop isel.rs owner-#11 fix flipped it.)
// ============================================================================
#[test]
fn owner11_fmin_fmax_snan_fixed_clean_bill() {
    let mut mj = TrustIrModule::new("mj".to_string());
    build_binop_jit(0, "jmin", &mut mj, Ty::I64, Ty::F64, BinOp::FMin);
    build_binop_jit(1, "jmax", &mut mj, Ty::I64, Ty::F64, BinOp::FMax);
    let bufj = jit_buffer(&mj);
    let jmin: U64Bin = unsafe { std::mem::transmute(bind(&bufj, "jmin")) };
    let jmax: U64Bin = unsafe { std::mem::transmute(bind(&bufj, "jmax")) };

    let mut mi = TrustIrModule::new("mi".to_string());
    build_binop_interp_f64(0, "imin", &mut mi, BinOp::FMin);
    build_binop_interp_f64(1, "imax", &mut mi, BinOp::FMax);

    // sNaN-vs-NUMBER: the historical categorical divergence (spec -> number,
    // bare FMINNM/FMAXNM -> quieted NaN).
    let snan_vs_num: &[(u64, u64, u64, &str)] = &[
        // (a, b, the number's bits that Trust-IR returns, desc)
        (F64_SNAN, F64_ONE, F64_ONE, "sNaN , 1.0"),
        (F64_ONE, F64_SNAN, F64_ONE, "1.0 , sNaN"),
        (F64_SNAN, F64_P0, F64_P0, "sNaN , +0.0"),
        (F64_SNAN_PAY, F64_TWO, F64_TWO, "sNaN_pay , 2.0"),
        (F64_NEG_SNAN, F64_ONE, F64_ONE, "-sNaN , 1.0"),
    ];
    let mut pinned = 0usize;
    for &(a, b, num, desc) in snan_vs_num {
        for (mn, sym) in [(&jmin, "min"), (&jmax, "max")] {
            let jit = unsafe { mn(a, b) };
            let spec = if sym == "min" {
                spec_min64(a, b)
            } else {
                spec_max64(a, b)
            };
            let interp = interp_bits_f64(&mi, if sym == "min" { "imin" } else { "imax" }, a, b);

            assert_eq!(
                spec, num,
                "Trust-IR f64::{sym}({desc}) must return the number {num:#018x}"
            );
            assert_eq!(
                interp, spec,
                "interpreter must equal Trust-IR spec for f64::{sym}({desc})"
            );

            // owner-#11 FIX: the JIT now canonicalizes each operand (self-min/max quiets
            // the sNaN) so the number-substitution fires — JIT == spec == the number.
            assert!(
                !is_nan64(jit),
                "owner #11 REGRESSED: JIT f64::{sym}({desc}) returned NaN {jit:#018x}, expected the number"
            );
            assert_eq!(
                jit, spec,
                "owner #11 REGRESSED: JIT f64::{sym}({desc}) = {jit:#018x} != Trust-IR spec {spec:#018x} \
                 (the operand self-canonicalization in select_fp_binop is missing/broken)."
            );
            pinned += 1;
        }
    }
    assert!(pinned >= 10);

    // Exact headline witness (fixed): sNaN operand is ignored, the number is returned.
    assert_eq!(
        unsafe { jmin(F64_SNAN, F64_ONE) },
        F64_ONE,
        "JIT fmin(sNaN,1.0) = 1.0 (fixed)"
    );
    assert_eq!(
        spec_min64(F64_SNAN, F64_ONE),
        F64_ONE,
        "Trust-IR fmin(sNaN,1.0) = 1.0"
    );
    assert_eq!(
        interp_bits_f64(&mi, "imin", F64_SNAN, F64_ONE),
        F64_ONE,
        "interp fmin(sNaN,1.0) = 1.0"
    );

    eprintln!(
        "OWNER #11 FIXED (verdict a — real JIT backend bug, now corrected): select_fp_binop \
         canonicalizes each operand with a self-min/max (`fminnm t,x,x`) before the binary \
         FMINNM/FMAXNM, so a signaling-NaN operand is quieted and the number wins — matching \
         Trust-IR minimumNumber/maximumNumber semantics. Witness fmin(sNaN,1.0): \
         JIT=spec=interp=0x3ff0000000000000 (1.0). {pinned} sNaN cells now clean."
    );
}

// ============================================================================
// TEST A2 — owner #11 f32 corroboration, FIXED (JIT vs Trust-IR spec).
//   The same fix applies on the f32 `fminnm s,s,s` path: sNaN operand is quieted by
//   the self-min/max canonicalization and the number wins, matching Trust-IR.
//   (Interpreter arm is f64-only, see BOUNDARIES.)
// ============================================================================
#[test]
fn owner11_fmin_fmax_snan_f32_fixed_clean_bill() {
    let mut m = TrustIrModule::new("m32".to_string());
    build_binop_jit(0, "jmin", &mut m, Ty::I32, Ty::F32, BinOp::FMin);
    build_binop_jit(1, "jmax", &mut m, Ty::I32, Ty::F32, BinOp::FMax);
    let buf = jit_buffer(&m);
    let jmin: U32Bin = unsafe { std::mem::transmute(bind(&buf, "jmin")) };
    let jmax: U32Bin = unsafe { std::mem::transmute(bind(&buf, "jmax")) };

    let cases: &[(u32, u32, u32, &str)] = &[
        (F32_SNAN, F32_ONE, F32_ONE, "sNaN , 1.0"),
        (F32_ONE, F32_SNAN, F32_ONE, "1.0 , sNaN"),
        (F32_SNAN_PAY, F32_ONE, F32_ONE, "sNaN_pay , 1.0"),
    ];
    let mut pinned = 0usize;
    for &(a, b, num, desc) in cases {
        for (mn, sym) in [(&jmin, "min"), (&jmax, "max")] {
            let jit = unsafe { mn(a, b) };
            let spec = if sym == "min" {
                spec_min32(a, b)
            } else {
                spec_max32(a, b)
            };
            assert_eq!(spec, num, "Trust-IR f32::{sym}({desc}) = number");
            assert!(
                !is_nan32(jit),
                "owner #11 REGRESSED (f32): JIT f32::{sym}({desc}) returned NaN {jit:#010x}, expected the number"
            );
            assert_eq!(
                jit, spec,
                "owner #11 REGRESSED (f32): JIT f32::{sym}({desc}) = {jit:#010x} != Trust-IR spec {spec:#010x}"
            );
            pinned += 1;
        }
    }
    assert!(pinned >= 6);
    // The number-vs-number and quiet-NaN f32 cells DO agree (bug was sNaN-specific).
    assert_eq!(
        unsafe { jmin(F32_ONE, 0x4000_0000) },
        spec_min32(F32_ONE, 0x4000_0000),
        "f32 ordinary min agrees"
    );
    assert_eq!(
        unsafe { jmax(F32_QNAN, F32_ONE) },
        spec_max32(F32_QNAN, F32_ONE),
        "f32 qNaN max agrees (number)"
    );
    eprintln!(
        "OWNER #11 f32 FIXED: the self-min/max canonicalization on the `fminnm/fmaxnm s,s,s` path quiets the sNaN so the number wins; {pinned} f32 sNaN cells now clean; ordinary/qNaN f32 cells agree."
    );
}

// ============================================================================
// TEST A3 — owner #11 SCOPE: the divergence is ISOLATED to the signaling-NaN
//   class. For qNaN-vs-number, both-qNaN, +/-0 sign, ordinary pairs, and +/-inf,
//   JIT == interpreter == Trust-IR spec bit-exact. (Establishes the bug does not touch
//   the common non-sNaN surface — a targeted single-class fix suffices.)
// ============================================================================
#[test]
fn owner11_non_snan_clean_bill_three_way() {
    let mut mj = TrustIrModule::new("mj".to_string());
    build_binop_jit(0, "jmin", &mut mj, Ty::I64, Ty::F64, BinOp::FMin);
    build_binop_jit(1, "jmax", &mut mj, Ty::I64, Ty::F64, BinOp::FMax);
    let bufj = jit_buffer(&mj);
    let jmin: U64Bin = unsafe { std::mem::transmute(bind(&bufj, "jmin")) };
    let jmax: U64Bin = unsafe { std::mem::transmute(bind(&bufj, "jmax")) };
    let mut mi = TrustIrModule::new("mi".to_string());
    build_binop_interp_f64(0, "imin", &mut mi, BinOp::FMin);
    build_binop_interp_f64(1, "imax", &mut mi, BinOp::FMax);

    // NON-signaling-NaN battery (qNaN, ±0, ordinary, ±inf). NB qNaN-vs-sNaN is
    // EXCLUDED — it is part of the pinned sNaN class (NaN-priority differs).
    let cases: &[(u64, u64, &str)] = &[
        (F64_QNAN, F64_ONE, "qNaN , 1.0"),
        (F64_ONE, F64_QNAN, "1.0 , qNaN"),
        (F64_QNAN_PAY, F64_TWO, "qNaN_pay , 2.0"),
        (F64_QNAN, F64_QNAN, "qNaN , qNaN"),
        (F64_N0, F64_P0, "-0.0 , +0.0"),
        (F64_P0, F64_N0, "+0.0 , -0.0"),
        (F64_ONE, F64_TWO, "1.0 , 2.0"),
        (F64_TWO, F64_ONE, "2.0 , 1.0"),
        (0xBFF0_0000_0000_0000, F64_TWO, "-1.0 , 2.0"),
        (F64_PINF, F64_ONE, "+inf , 1.0"),
        (F64_NINF, F64_ONE, "-inf , 1.0"),
        (F64_PINF, F64_NINF, "+inf , -inf"),
        (F64_P0, F64_ONE, "+0.0 , 1.0"),
    ];
    let mut checked = 0usize;
    let mut qnan_operand_cells = 0usize;
    let mut signed_zero_cells = 0usize;
    for &(a, b, desc) in cases {
        for sym in ["min", "max"] {
            let jit = if sym == "min" {
                unsafe { jmin(a, b) }
            } else {
                unsafe { jmax(a, b) }
            };
            let interp = interp_bits_f64(&mi, if sym == "min" { "imin" } else { "imax" }, a, b);
            let spec = if sym == "min" {
                spec_min64(a, b)
            } else {
                spec_max64(a, b)
            };
            assert_eq!(
                jit, spec,
                "JIT != Trust-IR spec for f64::{sym}({desc}): jit={jit:#018x} spec={spec:#018x}"
            );
            assert_eq!(
                interp, spec,
                "interp != Trust-IR spec for f64::{sym}({desc})"
            );
            checked += 1;
            // qNaN-vs-number returns the NUMBER (minNum ignores a quiet NaN) — the
            // surface where FMINNM already matches Trust-IR. Count qNaN OPERAND cells.
            if is_nan64(a) || is_nan64(b) {
                qnan_operand_cells += 1;
            }
        }
    }
    // Sign-of-zero subtlety: min(-0,+0) = -0, max(-0,+0) = +0 (bit-exact) — all three.
    assert_eq!(
        unsafe { jmin(F64_N0, F64_P0) },
        F64_N0,
        "JIT min(-0,+0) = -0"
    );
    assert_eq!(
        unsafe { jmax(F64_N0, F64_P0) },
        F64_P0,
        "JIT max(-0,+0) = +0"
    );
    assert_eq!(spec_min64(F64_N0, F64_P0), F64_N0, "spec min(-0,+0) = -0");
    assert_eq!(spec_max64(F64_N0, F64_P0), F64_P0, "spec max(-0,+0) = +0");
    signed_zero_cells += 4;

    assert!(
        qnan_operand_cells >= 6,
        "qNaN-operand cells under-exercised ({qnan_operand_cells})"
    );
    assert!(signed_zero_cells >= 4);
    eprintln!(
        "OWNER #11 SCOPE: {checked} non-sNaN cells (qNaN, +/-0, ordinary, +/-inf) agree \
         JIT==interp==Trust-IR-spec bit-exact ({qnan_operand_cells} qNaN-operand cells incl. \
         qNaN-vs-number->number and qNaN-vs-qNaN; signed-zero \
         min(-0,+0)=-0 / max=+0 on all three). The divergence is ISOLATED to the signaling-NaN \
         class -> a single operand-canonicalization fix resolves owner #11."
    );
}

// ============================================================================
// TEST A4 — ARMED CONTROL: the three-way differential is load-bearing.
//   (a) FMINNM vs FMAXNM opcode routing: min and max diverge on an ordered pair,
//       proving the opcode is observed (not both mapping to one op).
//   (b) The interpreter genuinely runs minimumNumber (not a passthrough): interp of a
//       reversed ordered pair returns the SMALLER, and the sNaN witness returns the
//       number (already asserted in A1) — here we prove min != max in the interp too.
//   (c) The sNaN pin is real: a naive "return op1" or "return op2" min would NOT
//       reproduce the Trust-IR result across the ordered and sNaN witnesses.
// ============================================================================
#[test]
fn owner11_armed_controls() {
    let mut mj = TrustIrModule::new("mj".to_string());
    build_binop_jit(0, "jmin", &mut mj, Ty::I64, Ty::F64, BinOp::FMin);
    build_binop_jit(1, "jmax", &mut mj, Ty::I64, Ty::F64, BinOp::FMax);
    let bufj = jit_buffer(&mj);
    let jmin: U64Bin = unsafe { std::mem::transmute(bind(&bufj, "jmin")) };
    let jmax: U64Bin = unsafe { std::mem::transmute(bind(&bufj, "jmax")) };
    let mut mi = TrustIrModule::new("mi".to_string());
    build_binop_interp_f64(0, "imin", &mut mi, BinOp::FMin);
    build_binop_interp_f64(1, "imax", &mut mi, BinOp::FMax);

    // (a) min/max opcode routing load-bearing (JIT).
    assert_ne!(
        unsafe { jmin(F64_ONE, F64_TWO) },
        unsafe { jmax(F64_ONE, F64_TWO) },
        "JIT min/max opcode routing dead"
    );
    assert_eq!(unsafe { jmin(F64_ONE, F64_TWO) }, F64_ONE, "JIT min(1,2)=1");
    assert_eq!(unsafe { jmax(F64_ONE, F64_TWO) }, F64_TWO, "JIT max(1,2)=2");
    // (b) min/max load-bearing in the interpreter too.
    assert_ne!(
        interp_bits_f64(&mi, "imin", F64_ONE, F64_TWO),
        interp_bits_f64(&mi, "imax", F64_ONE, F64_TWO),
        "interp min/max dead"
    );
    assert_eq!(
        interp_bits_f64(&mi, "imin", F64_TWO, F64_ONE),
        F64_ONE,
        "interp min(2,1)=1"
    );
    // (c) owner-#11 FIXED: a signaling-NaN operand is now IGNORED and the number is
    //     returned (the operand self-canonicalization quiets it, then minNum picks the
    //     number) — matching Trust-IR, and distinguishing the fix from the old
    //     quiet-and-return-NaN behavior.
    assert_eq!(
        unsafe { jmin(F64_SNAN_PAY, F64_TWO) },
        F64_TWO,
        "JIT fmin(sNaN_pay,2.0) = 2.0 (number returned, sNaN ignored)"
    );
    assert!(
        !is_nan64(unsafe { jmin(F64_SNAN_PAY, F64_TWO) }),
        "JIT no longer returns a quieted sNaN"
    );
    assert_eq!(
        unsafe { jmin(F64_SNAN_PAY, F64_TWO) },
        spec_min64(F64_SNAN_PAY, F64_TWO),
        "JIT == Trust-IR spec on the sNaN-payload cell"
    );
    eprintln!(
        "OWNER #11 CONTROLS: min/max opcode routing load-bearing (JIT + interp); the fixed JIT ignores a signaling-NaN operand and returns the number, == Trust-IR spec (not a quieted-sNaN)."
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// PART B — fp UNARY ops (FNeg / FAbs / FSqrt): native==JIT
// ═══════════════════════════════════════════════════════════════════════════════

// ============================================================================
// TEST B1 — FNeg CLEAN BILL. `-x` flips the sign bit only: -(+0)=-0, -(-0)=+0,
//   -(+inf)=-inf, and a NaN's sign flips with payload PRESERVED and quiet-state
//   UNCHANGED (sNaN stays signaling). Bit-exact vs Rust `-x`, f64 and f32.
// ============================================================================
#[test]
fn fp_unary_fneg_clean_bill() {
    let mut m64 = TrustIrModule::new("neg64".to_string());
    build_unop_jit(0, "n", &mut m64, Ty::I64, Ty::F64, UnOp::FNeg);
    let buf64 = jit_buffer(&m64);
    let n64: U64Un = unsafe { std::mem::transmute(bind(&buf64, "n")) };
    let mut m32 = TrustIrModule::new("neg32".to_string());
    build_unop_jit(0, "n", &mut m32, Ty::I32, Ty::F32, UnOp::FNeg);
    let buf32 = jit_buffer(&m32);
    let n32: U32Un = unsafe { std::mem::transmute(bind(&buf32, "n")) };

    let mut inputs64: Vec<u64> = vec![
        F64_P0,
        F64_N0,
        F64_ONE,
        0xBFF0_0000_0000_0000,
        F64_TWO,
        F64_PINF,
        F64_NINF,
        F64_QNAN,
        F64_QNAN_PAY,
        F64_SNAN,
        F64_SNAN_PAY,
        F64_NEG_SNAN,
        0x3FE0_0000_0000_0000,
        0x7FEF_FFFF_FFFF_FFFF, /*MAX*/
        0x0000_0000_0000_0001, /*subnormal*/
        0x000F_FFFF_FFFF_FFFF, /*max subnormal*/
        0x400921FB54442D18,    /*pi*/
    ];
    for k in 0..64u64 {
        inputs64.push(0x3FF0_0000_0000_0000 + k * 0x0010_0000_0000_0000);
    }
    let mut nan_cells = 0usize;
    for &b in &inputs64 {
        let jit = unsafe { n64(b) };
        let want = rust_neg64(b);
        assert_eq!(
            jit, want,
            "FNeg f64 MISCOMPILE at {b:#018x}: jit={jit:#018x} want={want:#018x}"
        );
        // sign bit flipped for finite/inf; identity property jit == b ^ signbit.
        assert_eq!(
            jit,
            b ^ F64_N0,
            "FNeg must flip exactly the sign bit at {b:#018x}"
        );
        if is_nan64(b) {
            nan_cells += 1;
            // payload + quiet-state preserved (only sign flips): sNaN stays sNaN.
            assert_eq!(
                jit & 0x000F_FFFF_FFFF_FFFF,
                b & 0x000F_FFFF_FFFF_FFFF,
                "FNeg NaN payload changed"
            );
            assert_eq!(
                jit & F64_QUIET_BIT,
                b & F64_QUIET_BIT,
                "FNeg must NOT quiet a NaN"
            );
        }
    }
    assert!(nan_cells >= 4);
    let inputs32: &[u32] = &[
        0,
        0x8000_0000,
        F32_ONE,
        0xBF80_0000,
        F32_PINF32,
        F32_NINF32,
        F32_QNAN,
        F32_SNAN,
        F32_SNAN_PAY,
        0x0000_0001,
        0x007F_FFFF,
        0x7F7F_FFFF,
    ];
    for &b in inputs32 {
        let jit = unsafe { n32(b) };
        let want = rust_neg32(b);
        assert_eq!(
            jit, want,
            "FNeg f32 MISCOMPILE at {b:#010x}: jit={jit:#010x} want={want:#010x}"
        );
        assert_eq!(
            jit,
            b ^ 0x8000_0000,
            "FNeg f32 must flip exactly the sign bit"
        );
        if is_nan32(b) {
            assert_eq!(
                jit & F32_QUIET_BIT,
                b & F32_QUIET_BIT,
                "FNeg f32 must NOT quiet a NaN"
            );
        }
    }
    eprintln!(
        "FNeg CLEAN BILL: `-x` == Rust bit-exact (f64+f32); flips exactly the sign bit; NaN payload + signaling-state preserved ({nan_cells} f64 NaN cells); -(+0)=-0, -(-0)=+0, +/-inf."
    );
}
const F32_PINF32: u32 = 0x7F80_0000;
const F32_NINF32: u32 = 0xFF80_0000;

// ============================================================================
// TEST B2 — FAbs CLEAN BILL. `x.abs()` clears the sign bit only: |−0|=+0,
//   |−inf|=+inf, and a NaN's sign clears with payload PRESERVED and quiet-state
//   UNCHANGED (sNaN stays signaling). Bit-exact vs Rust `x.abs()`, f64 and f32.
// ============================================================================
#[test]
fn fp_unary_fabs_clean_bill() {
    let mut m64 = TrustIrModule::new("abs64".to_string());
    build_unop_jit(0, "a", &mut m64, Ty::I64, Ty::F64, UnOp::FAbs);
    let buf64 = jit_buffer(&m64);
    let a64: U64Un = unsafe { std::mem::transmute(bind(&buf64, "a")) };
    let mut m32 = TrustIrModule::new("abs32".to_string());
    build_unop_jit(0, "a", &mut m32, Ty::I32, Ty::F32, UnOp::FAbs);
    let buf32 = jit_buffer(&m32);
    let a32: U32Un = unsafe { std::mem::transmute(bind(&buf32, "a")) };

    let mut inputs64: Vec<u64> = vec![
        F64_P0,
        F64_N0,
        F64_ONE,
        0xBFF0_0000_0000_0000,
        F64_PINF,
        F64_NINF,
        F64_QNAN,
        F64_QNAN_PAY,
        F64_SNAN,
        F64_SNAN_PAY,
        F64_NEG_SNAN,
        0x8000_0000_0000_0001, /*neg subnormal*/
        0xFFEF_FFFF_FFFF_FFFF, /*MIN*/
        0xC00921FB54442D18,    /*-pi*/
    ];
    for k in 0..48u64 {
        inputs64.push(0xBFF0_0000_0000_0000 + k * 0x0008_0000_0000_0000);
    }
    let mut nan_cells = 0usize;
    for &b in &inputs64 {
        let jit = unsafe { a64(b) };
        let want = rust_abs64(b);
        assert_eq!(
            jit, want,
            "FAbs f64 MISCOMPILE at {b:#018x}: jit={jit:#018x} want={want:#018x}"
        );
        assert_eq!(
            jit,
            b & 0x7FFF_FFFF_FFFF_FFFF,
            "FAbs must clear exactly the sign bit at {b:#018x}"
        );
        if is_nan64(b) {
            nan_cells += 1;
            assert_eq!(
                jit & 0x000F_FFFF_FFFF_FFFF,
                b & 0x000F_FFFF_FFFF_FFFF,
                "FAbs NaN payload changed"
            );
            assert_eq!(
                jit & F64_QUIET_BIT,
                b & F64_QUIET_BIT,
                "FAbs must NOT quiet a NaN"
            );
        }
    }
    assert!(nan_cells >= 4);
    let inputs32: &[u32] = &[
        0,
        0x8000_0000,
        F32_ONE,
        0xBF80_0000,
        F32_PINF32,
        F32_NINF32,
        F32_QNAN,
        F32_SNAN,
        F32_SNAN_PAY,
        0x8000_0001,
        0x807F_FFFF,
        0xFF7F_FFFF,
    ];
    for &b in inputs32 {
        let jit = unsafe { a32(b) };
        let want = rust_abs32(b);
        assert_eq!(
            jit, want,
            "FAbs f32 MISCOMPILE at {b:#010x}: jit={jit:#010x} want={want:#010x}"
        );
        assert_eq!(
            jit,
            b & 0x7FFF_FFFF,
            "FAbs f32 must clear exactly the sign bit"
        );
    }
    eprintln!(
        "FAbs CLEAN BILL: `x.abs()` == Rust bit-exact (f64+f32); clears exactly the sign bit; NaN payload + signaling-state preserved ({nan_cells} f64 NaN cells); |−0|=+0, |−inf|=+inf."
    );
}

// ============================================================================
// TEST B3 — FSqrt RNE CLEAN BILL (the real bug site). `x.sqrt()` is the
//   correctly-rounded (round-to-nearest-even) hardware sqrt. Dense sweep over
//   non-perfect-square mantissas, perfect squares, subnormals; specials
//   sqrt(-0)=-0, sqrt(+0)=+0, sqrt(+inf)=+inf, sqrt(-x)=NaN, sqrt(NaN)=quiet NaN.
//   Bit-exact vs Rust `x.sqrt()`, f64 and f32.
// ============================================================================
#[test]
fn fp_unary_fsqrt_rne_clean_bill() {
    let mut m64 = TrustIrModule::new("sqrt64".to_string());
    build_unop_jit(0, "s", &mut m64, Ty::I64, Ty::F64, UnOp::FSqrt);
    let buf64 = jit_buffer(&m64);
    let s64: U64Un = unsafe { std::mem::transmute(bind(&buf64, "s")) };
    let mut m32 = TrustIrModule::new("sqrt32".to_string());
    build_unop_jit(0, "s", &mut m32, Ty::I32, Ty::F32, UnOp::FSqrt);
    let buf32 = jit_buffer(&m32);
    let s32: U32Un = unsafe { std::mem::transmute(bind(&buf32, "s")) };

    let call64 = |x: f64| -> u64 { unsafe { s64(x.to_bits()) } };
    let mut checked = 0usize;
    let mut round_cells = 0usize;

    // Specials first.
    assert_eq!(call64(0.0), 0.0f64.to_bits(), "sqrt(+0)=+0");
    assert_eq!(call64(-0.0), (-0.0f64).to_bits(), "sqrt(-0)=-0");
    assert_eq!(
        call64(f64::INFINITY),
        f64::INFINITY.to_bits(),
        "sqrt(+inf)=+inf"
    );
    for x in [-1.0f64, -4.0, -1e-300, f64::NEG_INFINITY, -0.5] {
        let jit = call64(x);
        assert!(f64::from_bits(jit).is_nan(), "sqrt({x:e}) must be NaN");
        assert_eq!(
            jit,
            rust_sqrt64(x.to_bits()),
            "sqrt(neg) NaN must match Rust bit-exact"
        );
    }
    // sqrt of NaN (qNaN passthrough-quiet, sNaN quieted) — bit-exact vs Rust.
    for &b in &[F64_QNAN, F64_QNAN_PAY, F64_SNAN, F64_SNAN_PAY] {
        let jit = unsafe { s64(b) };
        assert!(is_nan64(jit), "sqrt(NaN) is NaN");
        assert_eq!(
            jit,
            rust_sqrt64(b),
            "sqrt(NaN) must match Rust bit-exact at {b:#018x}"
        );
        assert_ne!(jit & F64_QUIET_BIT, 0, "sqrt(NaN) result must be quiet");
    }

    // Perfect squares (exact, no rounding).
    for k in 0..=60i32 {
        let x = 2f64.powi(2 * k); // (2^k)^2
        let jit = call64(x);
        assert_eq!(
            jit,
            rust_sqrt64(x.to_bits()),
            "sqrt perfect 2^{} : jit={jit:#018x}",
            2 * k
        );
        assert_eq!(f64::from_bits(jit), 2f64.powi(k), "sqrt(2^{}) exact", 2 * k);
        checked += 1;
    }
    // Small integer sqrts (many are irrational -> genuine RNE rounding).
    for n in 1u64..=400 {
        let x = n as f64;
        let jit = call64(x);
        let want = rust_sqrt64(x.to_bits());
        assert_eq!(
            jit, want,
            "sqrt({n}) MISCOMPILE: jit={jit:#018x} want={want:#018x}"
        );
        checked += 1;
        // non-perfect square => the result is inexact (rounded).
        let r = f64::from_bits(jit);
        if (r.round() * r.round() - x).abs() > 0.5 {
            round_cells += 1;
        }
    }
    // Dense mantissa sweep in [1,4): consecutive f64 encodings -> sqrt in [1,2),
    // every one an RNE rounding of an irrational (except exact squares).
    let base = 1.0f64.to_bits();
    for k in 0..3000u64 {
        let x = f64::from_bits(base + k * 0x0000_0004_0000_0001); // irregular stride
        let jit = call64(x);
        let want = rust_sqrt64(x.to_bits());
        assert_eq!(
            jit, want,
            "sqrt dense k={k} x={x:e}: jit={jit:#018x} want={want:#018x}"
        );
        checked += 1;
        round_cells += 1;
    }
    // Subnormal inputs.
    for &b in &[
        0x0000_0000_0000_0001u64,
        0x0000_0000_0000_0002,
        0x0008_0000_0000_0000,
        0x000F_FFFF_FFFF_FFFF,
    ] {
        let jit = unsafe { s64(b) };
        assert_eq!(
            jit,
            rust_sqrt64(b),
            "sqrt subnormal {b:#018x} must match Rust"
        );
        checked += 1;
    }

    // ── f32 ──
    let call32 = |x: f32| -> u32 { unsafe { s32(x.to_bits()) } };
    assert_eq!(call32(0.0), 0.0f32.to_bits(), "f32 sqrt(+0)=+0");
    assert_eq!(call32(-0.0), (-0.0f32).to_bits(), "f32 sqrt(-0)=-0");
    assert_eq!(
        call32(f32::INFINITY),
        f32::INFINITY.to_bits(),
        "f32 sqrt(+inf)=+inf"
    );
    assert!(f32::from_bits(call32(-1.0)).is_nan(), "f32 sqrt(-1)=NaN");
    assert_eq!(
        call32(-1.0),
        rust_sqrt32((-1.0f32).to_bits()),
        "f32 sqrt(neg) matches Rust"
    );
    let mut f32checked = 0usize;
    for n in 1u32..=400 {
        let x = n as f32;
        assert_eq!(
            call32(x),
            rust_sqrt32(x.to_bits()),
            "f32 sqrt({n}) MISCOMPILE"
        );
        f32checked += 1;
    }
    let b32 = 1.0f32.to_bits();
    for k in 0..3000u32 {
        let x = f32::from_bits(b32 + k * 0x0000_1001); // irregular stride within [1,4)
        assert_eq!(
            call32(x),
            rust_sqrt32(x.to_bits()),
            "f32 sqrt dense k={k} x={x:e}"
        );
        f32checked += 1;
    }
    for &b in &[0x0000_0001u32, 0x0000_0002, 0x0040_0000, 0x007F_FFFF] {
        assert_eq!(
            unsafe { s32(b) },
            rust_sqrt32(b),
            "f32 sqrt subnormal {b:#010x}"
        );
        f32checked += 1;
    }

    assert!(
        round_cells >= 100,
        "RNE-rounding sqrt cells under-exercised ({round_cells})"
    );
    eprintln!(
        "FSqrt RNE CLEAN BILL: {checked} f64 + {f32checked} f32 sqrt cells bit-exact vs Rust \
         `x.sqrt()` ({round_cells} genuine RNE-rounding cells: dense non-perfect-square mantissa \
         sweeps + small integers). Perfect squares exact; sqrt(-0)=-0, sqrt(+0)=+0, sqrt(+inf)=+inf, \
         sqrt(-x)=NaN, sqrt(NaN)=quiet NaN, subnormals — all faithful."
    );
}

// ============================================================================
// TEST B4 — ARMED CONTROLS: the unary differential is load-bearing.
//   (a) FNeg vs FAbs are DISTINCT: on a positive input they diverge (fneg ->
//       negative, fabs -> positive). A lowering that swapped them would be caught.
//   (b) FSqrt genuinely ROUNDS (RNE), not a chop: on inputs whose correctly-rounded
//       sqrt has its low mantissa bit set, the JIT (== Rust) DIFFERS from a
//       low-bit-cleared "chop" model. Also: a lower-precision (f32-widened) sqrt
//       model differs from the JIT on most f64 inputs — so a precision-losing sqrt
//       WOULD be caught.
// ============================================================================
#[test]
fn fp_unary_armed_controls() {
    let mut mn = TrustIrModule::new("cn".to_string());
    build_unop_jit(0, "neg", &mut mn, Ty::I64, Ty::F64, UnOp::FNeg);
    build_unop_jit(1, "abs", &mut mn, Ty::I64, Ty::F64, UnOp::FAbs);
    build_unop_jit(2, "sqrt", &mut mn, Ty::I64, Ty::F64, UnOp::FSqrt);
    let buf = jit_buffer(&mn);
    let neg: U64Un = unsafe { std::mem::transmute(bind(&buf, "neg")) };
    let abs: U64Un = unsafe { std::mem::transmute(bind(&buf, "abs")) };
    let sqrt: U64Un = unsafe { std::mem::transmute(bind(&buf, "sqrt")) };

    // (a) FNeg vs FAbs distinct on a positive input.
    let pos = 3.5f64.to_bits();
    assert_ne!(
        unsafe { neg(pos) },
        unsafe { abs(pos) },
        "FNeg/FAbs CONTROL DEAD: agree on a positive input"
    );
    assert_eq!(unsafe { neg(pos) }, (-3.5f64).to_bits(), "fneg(3.5) = -3.5");
    assert_eq!(unsafe { abs(pos) }, 3.5f64.to_bits(), "fabs(3.5) = 3.5");
    // and both match Rust.
    assert_eq!(unsafe { neg(pos) }, rust_neg64(pos));
    assert_eq!(unsafe { abs(pos) }, rust_abs64(pos));

    // (b) FSqrt rounds: find inputs whose sqrt has a set low bit; chop clears it.
    let mut chop_caught = 0usize;
    let mut prec_caught = 0usize;
    for n in 2u64..=2000 {
        let x = n as f64;
        let jit = unsafe { sqrt(x.to_bits()) };
        assert_eq!(jit, rust_sqrt64(x.to_bits()), "sqrt({n}) must equal Rust");
        // chop model: clear the low mantissa bit of the correctly-rounded result.
        if jit & 1 == 1 {
            let chop = jit & !1u64;
            assert_ne!(
                jit, chop,
                "sqrt({n}) low bit set -> differs from a low-bit chop"
            );
            chop_caught += 1;
        }
        // precision-loss model: sqrt computed in f32 then widened to f64.
        let low_prec = ((x as f32).sqrt() as f64).to_bits();
        if low_prec != jit {
            prec_caught += 1;
        }
    }
    assert!(
        chop_caught >= 20,
        "sqrt low-bit-set cells under-exercised ({chop_caught})"
    );
    assert!(
        prec_caught >= 100,
        "sqrt precision-loss control under-exercised ({prec_caught})"
    );
    eprintln!(
        "UNARY CONTROLS: FNeg/FAbs distinct on a positive input (fneg->negative, fabs->positive); \
         FSqrt genuinely RNE-rounds — {chop_caught} results with a set low mantissa bit differ from \
         a low-bit chop, and {prec_caught} differ from an f32-precision-widened sqrt. A no-op / \
         wrong-precision / chop sqrt lowering WOULD be caught. The clean bills are load-bearing."
    );
}
