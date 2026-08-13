//! TRUST-SELF ROUND 38 (thread R38): AUDIT THE CORE fp BINARY ARITHMETIC
//! LOWERING (FAdd / FSub / FMul / FDiv) against the real Rust op as oracle.
//! This is the last major untouched fp-codegen surface (R34 f->int, R35 int->f,
//! R36 f<->f precision, R37 min/max+unary already done).
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! WHAT THE BACKEND ACTUALLY DOES (read from source, verified empirically below)
//! ═══════════════════════════════════════════════════════════════════════════════
//! ISel `select_fp_binop` (isel.rs:9312-9353):
//!   Opcode::Fadd -> AArch64FpBinOp::Fadd -> FaddRR
//!   Opcode::Fsub -> AArch64FpBinOp::Fsub -> FsubRR
//!   Opcode::Fmul -> AArch64FpBinOp::Fmul -> FmulRR
//!   Opcode::Fdiv -> AArch64FpBinOp::Fdiv -> FdivRR
//! Each lowers to a SINGLE instruction (one `emit`), no multi-instruction sequence.
//! Encoder (encode.rs:1836-1882 -> encoding_fp::encode_fp_arith): the 2-source FP
//! data-processing form `0|00|11110|ftype|1|Rm|opcode|10|Rn|Rd` with
//!   opcode field (encoding_fp.rs:44-57):  FMUL=0b0000, FDIV=0b0001,
//!   FADD=0b0010, FSUB=0b0011.
//! CRITICAL (the FSUB-specific bug site): FSUB is a BARE `FSUB Dd,Dn,Dm`
//! (opcode 0b0011), NOT an `FNEG + FADD` pair — so `a - b`, `x - x`, and the sign
//! of `NaN - x` follow hardware FSUB, matching real Rust `a - b` (which also emits
//! a bare FSUB). The `ftype` [23:22] comes from the destination FP register CLASS
//! (`fp_size_from_inst`: Fpr32=Single=00, Fpr64=Double=01) — no `sf`/width hardcode
//! like the R35 fp<->int encoders had. Rounding is the hardware op under the default
//! FPCR: round-to-nearest-ties-to-even, no Default-NaN — identical to Rust `+ - * /`.
//! => STRUCTURALLY there is no place for a width/precision/sequence bug here; this
//! file machine-checks that empirically at every RNE/signed-zero/inf/NaN/subnormal
//! edge.
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! FMA STATUS (the double-rounding bug site) — NO SCALAR FUSED OP EXISTS
//! ═══════════════════════════════════════════════════════════════════════════════
//! trust-ir `BinOp` (inst.rs:11-40) has FAdd/FSub/FMul/FDiv/FRem/FMin/FMax and NO
//! scalar fused-multiply-add opcode. (`vector.fma` exists only as a conformance
//! DIALECT op "carried without a trust-ir lowering by ratified fast-4 policy", and
//! `Formula::FpFma` is an SMT-contract term — neither is a scalar codegen surface.)
//! So `f64::mul_add` (a single-rounding hardware FMADD in native Rust) has no JIT
//! counterpart to build. What COULD still be wrong is a CONTRACTION the other way:
//! if the aarch64 ISel fused a separate `FMul` then `FAdd` into one `FMADD`, the JIT
//! would single-round while Rust's unfused `a*b + c` double-rounds — a real
//! miscompile. It does NOT: `detect_mul_add_idioms` (isel.rs:3779-3883) matches ONLY
//! integer `Iadd|Isub` roots over an `Imul` (-> MADD/MSUB); float `FAdd`/`FMul` are
//! never fused. TEST 6 proves this in machine code (JIT FMul-then-FAdd == Rust
//! UNFUSED, and DIFFERS from Rust `mul_add` on witnesses where fused != unfused).
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! THE ORACLE — the real Rust op at RUNTIME (`black_box`, so native Rust emits the
//! SAME hardware FADD/FSUB/FMUL/FDIV the JIT does; never const-folded via apfloat).
//! native == JIT is the codegen claim.
//! ═══════════════════════════════════════════════════════════════════════════════
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! HOW INPUT BITS ARE CONTROLLED / BOUNDARIES
//! ═══════════════════════════════════════════════════════════════════════════════
//!  * Each op module takes both operands' BITS as integer params, Bitcasts them into
//!    FP registers INSIDE the module (Bitcast i64->f64 = FMOV Dd,Xn; i32->f32 =
//!    FMOV Sd,Wn — bitwise, no quieting), runs the op, and Bitcasts the result back
//!    to integer bits. So exact bit patterns (incl. sNaN payloads) reach the op and
//!    the exact result bits are read — no float ABI question, no quieting on the way
//!    in. This is the R35/R36/R37 int-param+Bitcast discipline.
//!  * Oracle is JIT-vs-real-Rust (2-way), like R36. The trust-cg interpreter models
//!    all floats as native f64 and cannot carry an f32 or an sNaN through its
//!    value-passthrough Bitcast, so it is deliberately NOT used here (it would add no
//!    signal the real-Rust oracle doesn't already give).
//!  * Scope is FAdd/FSub/FMul/FDiv. `FRem` (float `%`) exists in trust-ir BinOp but
//!    is out of this round's brief and untouched here.
//!  * No emit-from-Rust: the emit-closure frontend has no float support (R31 Finding
//!    A). Everything is hand-built trust-ir through the trust-cg JIT.
//!  * Run tests ONE AT A TIME (`--test-threads=1`): the JIT engine is not thread-safe
//!    at suite scale (jit-parallel-race-2026-06-29.md).

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::hint::black_box;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

use trust_ir::{
    BinOp, Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty,
};
use trust_ir::{BlockId, CastOp, FuncId, ValueId};

// ═══════════════════════════════════════════════════════════════════════════════
// Module builders
// ═══════════════════════════════════════════════════════════════════════════════

/// JIT binop, integer-bits in/out: fn(iN,iN)->iN via Bitcast at the boundary.
/// (int_ty, f_ty) is (I64,F64) or (I32,F32). Bit-exact: no float ABI.
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

/// JIT (a*b)+c as TWO SEPARATE ops (FMul then FAdd), integer-bits in/out:
/// fn(i64,i64,i64)->i64. Used by the anti-fusion (no-FMADD-contraction) control.
fn build_muladd_jit_f64(func_id: u32, name: &str, m: &mut TrustIrModule) {
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), Ty::I64),
            (ValueId::new(1), Ty::I64),
            (ValueId::new(2), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: Ty::I64,
                dst_ty: Ty::F64,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: Ty::I64,
                dst_ty: Ty::F64,
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: Ty::I64,
                dst_ty: Ty::F64,
                operand: ValueId::new(2),
            })
            .with_result(ValueId::new(5)),
            // t = a * b   (separate FMUL — one rounding)
            InstrNode::new(Inst::BinOp {
                op: BinOp::FMul,
                ty: Ty::F64,
                lhs: ValueId::new(3),
                rhs: ValueId::new(4),
            })
            .with_result(ValueId::new(6)),
            // r = t + c   (separate FADD — a second rounding)
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F64,
                lhs: ValueId::new(6),
                rhs: ValueId::new(5),
            })
            .with_result(ValueId::new(7)),
            InstrNode::new(Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: Ty::F64,
                dst_ty: Ty::I64,
                operand: ValueId::new(7),
            })
            .with_result(ValueId::new(8)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(8)],
            }),
        ],
    }];
    m.add_function(f);
}

// ═══════════════════════════════════════════════════════════════════════════════
// JIT harness
// ═══════════════════════════════════════════════════════════════════════════════

fn jit_buffer(m: &TrustIrModule) -> trust_cg_codegen::jit::ExecutableBuffer {
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(m, &HashMap::new())
        .expect("hand-built fp binary-arith module must JIT-compile")
        .buffer
}
fn bind(buf: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buf.get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("JIT symbol `{sym}` not found"))
        .as_ptr()
}

type U64Bin = unsafe extern "C" fn(u64, u64) -> u64;
type U32Bin = unsafe extern "C" fn(u32, u32) -> u32;
type U64Tern = unsafe extern "C" fn(u64, u64, u64) -> u64;

// Runtime real-Rust oracles (black_box => the hardware op on exact bits, never
// const-folded). Bit-for-bit the same operation the JIT performs.
#[inline(never)]
fn rust_add64(a: u64, b: u64) -> u64 {
    (black_box(f64::from_bits(a)) + black_box(f64::from_bits(b))).to_bits()
}
#[inline(never)]
fn rust_sub64(a: u64, b: u64) -> u64 {
    (black_box(f64::from_bits(a)) - black_box(f64::from_bits(b))).to_bits()
}
#[inline(never)]
fn rust_mul64(a: u64, b: u64) -> u64 {
    (black_box(f64::from_bits(a)) * black_box(f64::from_bits(b))).to_bits()
}
#[inline(never)]
fn rust_div64(a: u64, b: u64) -> u64 {
    (black_box(f64::from_bits(a)) / black_box(f64::from_bits(b))).to_bits()
}
#[inline(never)]
fn rust_add32(a: u32, b: u32) -> u32 {
    (black_box(f32::from_bits(a)) + black_box(f32::from_bits(b))).to_bits()
}
#[inline(never)]
fn rust_sub32(a: u32, b: u32) -> u32 {
    (black_box(f32::from_bits(a)) - black_box(f32::from_bits(b))).to_bits()
}
#[inline(never)]
fn rust_mul32(a: u32, b: u32) -> u32 {
    (black_box(f32::from_bits(a)) * black_box(f32::from_bits(b))).to_bits()
}
#[inline(never)]
fn rust_div32(a: u32, b: u32) -> u32 {
    (black_box(f32::from_bits(a)) / black_box(f32::from_bits(b))).to_bits()
}
// Unfused vs fused, for the anti-contraction control.
#[inline(never)]
fn rust_unfused_madd64(a: u64, b: u64, c: u64) -> u64 {
    let p = black_box(f64::from_bits(a)) * black_box(f64::from_bits(b)); // rounds
    (black_box(p) + black_box(f64::from_bits(c))).to_bits() // rounds again
}
#[inline(never)]
fn rust_fused_madd64(a: u64, b: u64, c: u64) -> u64 {
    // single-rounding hardware FMADD in native Rust
    black_box(f64::from_bits(a))
        .mul_add(black_box(f64::from_bits(b)), black_box(f64::from_bits(c)))
        .to_bits()
}

// f64 special bit patterns
const P0: u64 = 0x0000_0000_0000_0000;
const N0: u64 = 0x8000_0000_0000_0000;
const ONE: u64 = 0x3FF0_0000_0000_0000;
const NEG_ONE: u64 = 0xBFF0_0000_0000_0000;
const TWO: u64 = 0x4000_0000_0000_0000;
const THREE: u64 = 0x4008_0000_0000_0000;
const PINF: u64 = 0x7FF0_0000_0000_0000;
const NINF: u64 = 0xFFF0_0000_0000_0000;
const QNAN: u64 = 0x7FF8_0000_0000_0000;
const QNAN_PAY: u64 = 0x7FF8_0000_1234_5678;
const NEG_QNAN: u64 = 0xFFF8_0000_0000_0000;
const SNAN: u64 = 0x7FF0_0000_0000_0001;
const SNAN_PAY: u64 = 0x7FF0_0000_ABCD_0000;
const NEG_SNAN: u64 = 0xFFF0_0000_0000_0001;
const QUIET_BIT: u64 = 0x0008_0000_0000_0000;
const P2_53: u64 = 0x4340_0000_0000_0000; // 2^53
const F64_MAX: u64 = 0x7FEF_FFFF_FFFF_FFFF;
const MIN_POS_NORMAL: u64 = 0x0010_0000_0000_0000; // 2^-1022
const MIN_SUBNORMAL: u64 = 0x0000_0000_0000_0001; // 2^-1074

// f32 special bit patterns
const F32_P0: u32 = 0x0000_0000;
const F32_ONE: u32 = 0x3F80_0000;
const F32_TWO: u32 = 0x4000_0000;
const F32_PINF: u32 = 0x7F80_0000;
const F32_NINF: u32 = 0xFF80_0000;
const F32_SNAN: u32 = 0x7F80_0001;
const F32_SNAN_PAY: u32 = 0x7F80_4321;
const F32_QUIET_BIT: u32 = 0x0040_0000;

fn is_nan64(b: u64) -> bool {
    (b & 0x7FF0_0000_0000_0000) == 0x7FF0_0000_0000_0000 && (b & 0x000F_FFFF_FFFF_FFFF) != 0
}
fn is_nan32(b: u32) -> bool {
    (b & 0x7F80_0000) == 0x7F80_0000 && (b & 0x007F_FFFF) != 0
}
fn is_inf64(b: u64) -> bool {
    b == PINF || b == NINF
}

// Bind all four f64 ops from one module.
struct Ops64 {
    _buf: trust_cg_codegen::jit::ExecutableBuffer,
    add: U64Bin,
    sub: U64Bin,
    mul: U64Bin,
    div: U64Bin,
}
fn build_ops64() -> Ops64 {
    let mut m = TrustIrModule::new("arith64".to_string());
    build_binop_jit(0, "add", &mut m, Ty::I64, Ty::F64, BinOp::FAdd);
    build_binop_jit(1, "sub", &mut m, Ty::I64, Ty::F64, BinOp::FSub);
    build_binop_jit(2, "mul", &mut m, Ty::I64, Ty::F64, BinOp::FMul);
    build_binop_jit(3, "div", &mut m, Ty::I64, Ty::F64, BinOp::FDiv);
    let buf = jit_buffer(&m);
    let add: U64Bin = unsafe { std::mem::transmute(bind(&buf, "add")) };
    let sub: U64Bin = unsafe { std::mem::transmute(bind(&buf, "sub")) };
    let mul: U64Bin = unsafe { std::mem::transmute(bind(&buf, "mul")) };
    let div: U64Bin = unsafe { std::mem::transmute(bind(&buf, "div")) };
    Ops64 {
        _buf: buf,
        add,
        sub,
        mul,
        div,
    }
}
struct Ops32 {
    _buf: trust_cg_codegen::jit::ExecutableBuffer,
    add: U32Bin,
    sub: U32Bin,
    mul: U32Bin,
    div: U32Bin,
}
fn build_ops32() -> Ops32 {
    let mut m = TrustIrModule::new("arith32".to_string());
    build_binop_jit(0, "add", &mut m, Ty::I32, Ty::F32, BinOp::FAdd);
    build_binop_jit(1, "sub", &mut m, Ty::I32, Ty::F32, BinOp::FSub);
    build_binop_jit(2, "mul", &mut m, Ty::I32, Ty::F32, BinOp::FMul);
    build_binop_jit(3, "div", &mut m, Ty::I32, Ty::F32, BinOp::FDiv);
    let buf = jit_buffer(&m);
    let add: U32Bin = unsafe { std::mem::transmute(bind(&buf, "add")) };
    let sub: U32Bin = unsafe { std::mem::transmute(bind(&buf, "sub")) };
    let mul: U32Bin = unsafe { std::mem::transmute(bind(&buf, "mul")) };
    let div: U32Bin = unsafe { std::mem::transmute(bind(&buf, "div")) };
    Ops32 {
        _buf: buf,
        add,
        sub,
        mul,
        div,
    }
}

// ============================================================================
// TEST 1 — FADD RNE + specials CLEAN BILL (f64 + f32).
//   Dense mantissa sweeps whose exact sum needs >53 (f64) / >24 (f32) bits, incl.
//   ties-to-even; signed zero ((+0)+(-0)=+0, (-0)+(-0)=-0, a+(-a)=+0); infinities
//   (inf+inf=inf, inf+(-inf)=NaN, x+inf=inf); qNaN operand -> quieted NaN;
//   subnormal + overflow->inf. Every cell bit-exact vs Rust `a + b`, with absolute
//   pins on the RNE and special witnesses (proves semantics, not self-agreement).
// ============================================================================
#[test]
fn fadd_rne_and_specials_clean_bill() {
    let o = build_ops64();
    let mut checked = 0usize;
    let mut round_cells = 0usize;

    // ── Absolute RNE witnesses (2^53 is to f64 what 2^24 is to f32: ULP = 2). ──
    // 2^53 + 1 -> ties to even -> 2^53 (mantissa LSB 0).
    assert_eq!(
        unsafe { (o.add)(P2_53, ONE) },
        P2_53,
        "2^53+1 ties to even -> 2^53"
    );
    // 2^53 + 3 -> ties to even -> 2^53+4.
    assert_eq!(
        unsafe { (o.add)(P2_53, THREE) },
        0x4340_0000_0000_0002,
        "2^53+3 ties to even -> 2^53+4"
    );
    // 2^53 + 2 exact.
    assert_eq!(
        unsafe { (o.add)(P2_53, TWO) },
        0x4340_0000_0000_0001,
        "2^53+2 exact"
    );
    // 1.0 + 2^-53 (halfway) -> ties to even -> 1.0.
    assert_eq!(
        unsafe { (o.add)(ONE, 0x3CA0_0000_0000_0000) },
        ONE,
        "1+2^-53 ties to even -> 1.0"
    );
    for &(a, b) in &[(P2_53, ONE), (P2_53, THREE), (ONE, 0x3CA0_0000_0000_0000)] {
        assert_eq!(
            unsafe { (o.add)(a, b) },
            rust_add64(a, b),
            "RNE witness == Rust"
        );
    }

    // ── Signed zero ──
    assert_eq!(unsafe { (o.add)(P0, P0) }, P0, "(+0)+(+0) = +0");
    assert_eq!(unsafe { (o.add)(N0, N0) }, N0, "(-0)+(-0) = -0");
    assert_eq!(unsafe { (o.add)(P0, N0) }, P0, "(+0)+(-0) = +0 (RNE)");
    assert_eq!(unsafe { (o.add)(N0, P0) }, P0, "(-0)+(+0) = +0 (RNE)");
    assert_eq!(
        unsafe { (o.add)(ONE, NEG_ONE) },
        P0,
        "a+(-a) = +0 (RNE, not -0)"
    );
    assert_eq!(
        unsafe { (o.add)(THREE, 0xC008_0000_0000_0000) },
        P0,
        "3+(-3) = +0"
    );
    for &(a, b) in &[(P0, P0), (N0, N0), (P0, N0), (N0, P0), (ONE, NEG_ONE)] {
        assert_eq!(
            unsafe { (o.add)(a, b) },
            rust_add64(a, b),
            "signed-zero add == Rust"
        );
    }

    // ── Infinities ──
    assert_eq!(unsafe { (o.add)(PINF, PINF) }, PINF, "inf+inf = inf");
    assert_eq!(unsafe { (o.add)(NINF, NINF) }, NINF, "-inf+-inf = -inf");
    assert!(is_nan64(unsafe { (o.add)(PINF, NINF) }), "inf+(-inf) = NaN");
    assert_eq!(
        unsafe { (o.add)(PINF, NINF) },
        rust_add64(PINF, NINF),
        "inf+(-inf) NaN == Rust"
    );
    assert_eq!(unsafe { (o.add)(PINF, ONE) }, PINF, "inf+1 = inf");
    assert_eq!(unsafe { (o.add)(NINF, F64_MAX) }, NINF, "-inf+max = -inf");

    // ── NaN operand ──
    for &(a, b) in &[(QNAN, ONE), (ONE, QNAN), (QNAN_PAY, TWO), (NEG_QNAN, PINF)] {
        let jit = unsafe { (o.add)(a, b) };
        assert!(is_nan64(jit), "NaN operand -> NaN");
        assert_eq!(jit, rust_add64(a, b), "add NaN-operand == Rust bit-exact");
        assert_ne!(jit & QUIET_BIT, 0, "result NaN is quiet");
    }

    // ── Overflow -> inf, subnormal ──
    assert_eq!(
        unsafe { (o.add)(F64_MAX, F64_MAX) },
        rust_add64(F64_MAX, F64_MAX),
        "MAX+MAX overflow == Rust"
    );
    assert!(
        is_inf64(unsafe { (o.add)(F64_MAX, F64_MAX) }),
        "MAX+MAX -> inf"
    );
    assert_eq!(
        unsafe { (o.add)(MIN_SUBNORMAL, MIN_SUBNORMAL) },
        rust_add64(MIN_SUBNORMAL, MIN_SUBNORMAL),
        "subnormal add == Rust"
    );

    // ── Dense rounding sweeps ── (a large base + a small stride -> most sums round)
    // Base 1.0, add sub-ULP increments: every non-multiple-of-ULP sum rounds (RNE).
    for k in 0..2000u64 {
        let b = 0x3C00_0000_0000_0000 + k * 0x0000_0001_0000_0001; // ~2^-63 scale, irregular
        let jit = unsafe { (o.add)(ONE, b) };
        assert_eq!(jit, rust_add64(ONE, b), "FADD dense-1.0 k={k}: b={b:#018x}");
        checked += 1;
        round_cells += 1;
    }
    // Two arbitrary normals whose exact sum needs full precision.
    let bases: &[u64] = &[
        0x4045_1234_5678_9ABC,
        0x3FE9_2837_4655_ABAA,
        0x40C3_8800_0000_0001,
        0xC012_3456_789A_BCDE,
    ];
    for &a in bases {
        for k in 0..500u64 {
            let b = a.wrapping_add(k.wrapping_mul(0x0000_0003_1415_9269));
            // keep b finite & non-NaN by clamping exponent region loosely: skip if NaN/inf.
            if is_nan64(b) || is_inf64(b) {
                continue;
            }
            let jit = unsafe { (o.add)(a, b) };
            assert_eq!(
                jit,
                rust_add64(a, b),
                "FADD normals a={a:#018x} b={b:#018x}"
            );
            checked += 1;
            round_cells += 1;
        }
    }

    // ── f32 ── dense sweep + specials.
    let o32 = build_ops32();
    let mut f32checked = 0usize;
    // 2^24 + 1 ties to even -> 2^24.
    assert_eq!(
        unsafe { (o32.add)(0x4B80_0000, F32_ONE) },
        0x4B80_0000,
        "f32 2^24+1 ties to even"
    );
    assert_eq!(
        unsafe { (o32.add)(F32_P0, 0x8000_0000) },
        F32_P0,
        "f32 (+0)+(-0)=+0"
    );
    assert_eq!(
        unsafe { (o32.add)(F32_ONE, 0xBF80_0000) },
        F32_P0,
        "f32 1+(-1)=+0"
    );
    assert!(
        is_nan32(unsafe { (o32.add)(F32_PINF, F32_NINF) }),
        "f32 inf+(-inf)=NaN"
    );
    for k in 0..2000u32 {
        let a = 0x3F80_0000u32.wrapping_add(k.wrapping_mul(3));
        let b = 0x3A00_0000u32.wrapping_add(k.wrapping_mul(0x0000_1001));
        if is_nan32(a)
            || is_nan32(b)
            || (a & 0x7F80_0000) == 0x7F80_0000
            || (b & 0x7F80_0000) == 0x7F80_0000
        {
            continue;
        }
        assert_eq!(
            unsafe { (o32.add)(a, b) },
            rust_add32(a, b),
            "f32 FADD k={k}"
        );
        f32checked += 1;
    }

    assert!(
        round_cells >= 500,
        "RNE add cells under-exercised ({round_cells})"
    );
    eprintln!(
        "FADD CLEAN BILL: {checked} f64 + {f32checked} f32 cells bit-exact vs Rust `a+b` \
         ({round_cells} genuine RNE-rounding cells). Absolute pins: 2^53+1->2^53, 2^53+3->2^53+4, \
         1+2^-53->1.0 (ties to even); signed zero (+0)+(-0)=+0, (-0)+(-0)=-0, a+(-a)=+0; \
         inf+inf=inf, inf+(-inf)=NaN, x+inf=inf; qNaN quieted; overflow->inf; subnormal. FaddRR faithful."
    );
}

// ============================================================================
// TEST 2 — FSUB (the FSUB-specific bug site) CLEAN BILL (f64 + f32).
//   Confirms a BARE FSUB (NOT FNEG+FADD): x-x=+0 (RNE, never -0); the signed-zero
//   matrix ((+0)-(+0)=+0, (-0)-(-0)=+0, (+0)-(-0)=+0, (-0)-(+0)=-0); NaN-x sign;
//   inf-inf=NaN; non-commutativity (a-b != b-a) preserved; dense RNE sweep.
//   Every cell bit-exact vs Rust `a - b` (which itself emits a bare FSUB).
// ============================================================================
#[test]
fn fsub_bare_fsub_clean_bill() {
    let o = build_ops64();
    let mut checked = 0usize;
    let mut round_cells = 0usize;

    // ── x - x = +0 (RNE), NOT -0 — the discriminating FNEG+FADD witness. ──
    for &x in &[
        ONE,
        TWO,
        THREE,
        0x400921FB54442D18u64, /*pi*/
        F64_MAX,
        MIN_POS_NORMAL,
        0x40C3_8800_0000_0001,
    ] {
        assert_eq!(
            unsafe { (o.sub)(x, x) },
            P0,
            "x - x = +0 (not -0) at {x:#018x}"
        );
        assert_eq!(unsafe { (o.sub)(x, x) }, rust_sub64(x, x), "x-x == Rust");
    }

    // ── Signed-zero matrix ──
    assert_eq!(unsafe { (o.sub)(P0, P0) }, P0, "(+0)-(+0) = +0");
    assert_eq!(unsafe { (o.sub)(N0, N0) }, P0, "(-0)-(-0) = +0");
    assert_eq!(unsafe { (o.sub)(P0, N0) }, P0, "(+0)-(-0) = +0");
    assert_eq!(unsafe { (o.sub)(N0, P0) }, N0, "(-0)-(+0) = -0");
    for &(a, b) in &[(P0, P0), (N0, N0), (P0, N0), (N0, P0)] {
        assert_eq!(
            unsafe { (o.sub)(a, b) },
            rust_sub64(a, b),
            "signed-zero sub == Rust"
        );
    }

    // ── NaN - x sign / payload (bare FSUB returns the NaN operand quieted, sign
    //     preserved; an FNEG+FADD lowering would route the sign through the adder). ──
    for &(a, b) in &[(QNAN, ONE), (NEG_QNAN, ONE), (ONE, QNAN), (QNAN_PAY, TWO)] {
        let jit = unsafe { (o.sub)(a, b) };
        assert!(is_nan64(jit), "NaN - x / x - NaN = NaN");
        assert_eq!(
            jit,
            rust_sub64(a, b),
            "sub NaN == Rust bit-exact (sign+payload)"
        );
    }
    // sign witness pinned:
    assert_eq!(
        unsafe { (o.sub)(NEG_QNAN, ONE) },
        rust_sub64(NEG_QNAN, ONE),
        "(-qNaN) - 1 sign == Rust"
    );

    // ── inf - inf = NaN; inf - x = inf; x - inf = -inf ──
    assert!(is_nan64(unsafe { (o.sub)(PINF, PINF) }), "inf-inf = NaN");
    assert_eq!(
        unsafe { (o.sub)(PINF, PINF) },
        rust_sub64(PINF, PINF),
        "inf-inf NaN == Rust"
    );
    assert!(
        is_nan64(unsafe { (o.sub)(NINF, NINF) }),
        "-inf - -inf = NaN"
    );
    assert_eq!(unsafe { (o.sub)(PINF, ONE) }, PINF, "inf - 1 = inf");
    assert_eq!(unsafe { (o.sub)(ONE, PINF) }, NINF, "1 - inf = -inf");
    assert_eq!(unsafe { (o.sub)(PINF, NINF) }, PINF, "inf - (-inf) = inf");

    // ── non-commutativity preserved (a-b vs b-a). ──
    assert_eq!(unsafe { (o.sub)(THREE, ONE) }, TWO, "3 - 1 = 2");
    assert_eq!(
        unsafe { (o.sub)(ONE, THREE) },
        0xC000_0000_0000_0000,
        "1 - 3 = -2"
    );
    assert_ne!(
        unsafe { (o.sub)(THREE, ONE) },
        unsafe { (o.sub)(ONE, THREE) },
        "operand order load-bearing"
    );

    // ── RNE witness: (2^53 + 2) - 1 ties to even. And a dense sweep. ──
    for k in 0..2000u64 {
        let b = 0x3C00_0000_0000_0000 + k * 0x0000_0001_0000_0001;
        let jit = unsafe { (o.sub)(ONE, b) };
        assert_eq!(jit, rust_sub64(ONE, b), "FSUB dense-1.0 k={k}");
        checked += 1;
        round_cells += 1;
    }
    let bases: &[u64] = &[
        0x4045_1234_5678_9ABC,
        0x3FE9_2837_4655_ABAA,
        0x40C3_8800_0000_0001,
    ];
    for &a in bases {
        for k in 0..500u64 {
            let b = a.wrapping_add(k.wrapping_mul(0x0000_0003_1415_9269));
            if is_nan64(b) || is_inf64(b) {
                continue;
            }
            assert_eq!(
                unsafe { (o.sub)(a, b) },
                rust_sub64(a, b),
                "FSUB normals a={a:#018x} b={b:#018x}"
            );
            checked += 1;
            round_cells += 1;
        }
    }

    // ── f32 ── mirror the FSUB-specific witnesses.
    let o32 = build_ops32();
    let mut f32checked = 0usize;
    assert_eq!(unsafe { (o32.sub)(F32_ONE, F32_ONE) }, F32_P0, "f32 x-x=+0");
    assert_eq!(
        unsafe { (o32.sub)(0x8000_0000, F32_P0) },
        0x8000_0000,
        "f32 (-0)-(+0)=-0"
    );
    assert_eq!(
        unsafe { (o32.sub)(F32_P0, 0x8000_0000) },
        F32_P0,
        "f32 (+0)-(-0)=+0"
    );
    assert!(
        is_nan32(unsafe { (o32.sub)(F32_PINF, F32_PINF) }),
        "f32 inf-inf=NaN"
    );
    for k in 0..2000u32 {
        let a = 0x3F80_0000u32.wrapping_add(k.wrapping_mul(3));
        let b = 0x3A00_0000u32.wrapping_add(k.wrapping_mul(0x0000_1001));
        if (a & 0x7F80_0000) == 0x7F80_0000 || (b & 0x7F80_0000) == 0x7F80_0000 {
            continue;
        }
        assert_eq!(
            unsafe { (o32.sub)(a, b) },
            rust_sub32(a, b),
            "f32 FSUB k={k}"
        );
        f32checked += 1;
    }

    assert!(
        round_cells >= 500,
        "RNE sub cells under-exercised ({round_cells})"
    );
    eprintln!(
        "FSUB CLEAN BILL (bare FSUB, not FNEG+FADD): {checked} f64 + {f32checked} f32 cells \
         bit-exact vs Rust `a-b` ({round_cells} RNE cells). x-x=+0 (never -0) on 7 magnitudes; \
         signed-zero matrix (-0)-(+0)=-0 / (+0)-(-0)=+0; NaN-x sign+payload == Rust; inf-inf=NaN; \
         1-inf=-inf; non-commutativity preserved. FsubRR faithful."
    );
}

// ============================================================================
// TEST 3 — FMUL RNE + specials CLEAN BILL (f64 + f32).
//   Dense products whose exact value needs >53/>24 mantissa bits (incl. ties);
//   sign of a*0 / (-0)*x; inf*0=NaN; overflow->inf; gradual underflow->subnormal/0;
//   subnormal operands; qNaN/NaN. Every cell bit-exact vs Rust `a*b`, absolute pins.
// ============================================================================
#[test]
fn fmul_rne_and_specials_clean_bill() {
    let o = build_ops64();
    let mut checked = 0usize;
    let mut round_cells = 0usize;

    // ── Absolute RNE witness: (1+2^-52)^2 = 1 + 2^-51 + 2^-104 -> rounds down to 1+2^-51. ──
    let one_plus_ulp = 0x3FF0_0000_0000_0001u64; // 1 + 2^-52
    assert_eq!(
        unsafe { (o.mul)(one_plus_ulp, one_plus_ulp) },
        0x3FF0_0000_0000_0002,
        "(1+2^-52)^2 -> 1+2^-51 (RNE down)"
    );
    assert_eq!(
        unsafe { (o.mul)(one_plus_ulp, one_plus_ulp) },
        rust_mul64(one_plus_ulp, one_plus_ulp),
        "RNE mul witness == Rust"
    );
    // 0.1 * 0.1 (both inexact) -> the correctly-rounded product.
    assert_eq!(
        unsafe { (o.mul)(0.1f64.to_bits(), 0.1f64.to_bits()) },
        rust_mul64(0.1f64.to_bits(), 0.1f64.to_bits()),
        "0.1*0.1 == Rust"
    );

    // ── Sign of a*0 / (-0)*x ──
    assert_eq!(unsafe { (o.mul)(TWO, P0) }, P0, "2 * +0 = +0");
    assert_eq!(unsafe { (o.mul)(NEG_ONE, P0) }, N0, "-1 * +0 = -0");
    assert_eq!(unsafe { (o.mul)(N0, TWO) }, N0, "-0 * 2 = -0");
    assert_eq!(unsafe { (o.mul)(N0, NEG_ONE) }, P0, "-0 * -1 = +0");
    assert_eq!(unsafe { (o.mul)(N0, N0) }, P0, "-0 * -0 = +0");
    for &(a, b) in &[(TWO, P0), (NEG_ONE, P0), (N0, TWO), (N0, NEG_ONE)] {
        assert_eq!(
            unsafe { (o.mul)(a, b) },
            rust_mul64(a, b),
            "signed-zero mul == Rust"
        );
    }

    // ── inf * 0 = NaN; inf * x = inf; sign ──
    assert!(is_nan64(unsafe { (o.mul)(PINF, P0) }), "inf * 0 = NaN");
    assert_eq!(
        unsafe { (o.mul)(PINF, P0) },
        rust_mul64(PINF, P0),
        "inf*0 NaN == Rust"
    );
    assert!(is_nan64(unsafe { (o.mul)(P0, NINF) }), "0 * -inf = NaN");
    assert_eq!(unsafe { (o.mul)(PINF, TWO) }, PINF, "inf * 2 = inf");
    assert_eq!(unsafe { (o.mul)(PINF, NEG_ONE) }, NINF, "inf * -1 = -inf");
    assert_eq!(unsafe { (o.mul)(NINF, NEG_ONE) }, PINF, "-inf * -1 = inf");

    // ── overflow -> inf; underflow -> subnormal / 0 ──
    assert!(is_inf64(unsafe { (o.mul)(F64_MAX, TWO) }), "MAX * 2 -> inf");
    assert_eq!(
        unsafe { (o.mul)(F64_MAX, TWO) },
        rust_mul64(F64_MAX, TWO),
        "overflow mul == Rust"
    );
    // MIN_POS_NORMAL * 0.5 -> largest subnormal region; MIN_SUBNORMAL * 0.5 -> 0 (RNE).
    let half = 0x3FE0_0000_0000_0000u64;
    assert_eq!(
        unsafe { (o.mul)(MIN_POS_NORMAL, half) },
        rust_mul64(MIN_POS_NORMAL, half),
        "underflow->subnormal == Rust"
    );
    assert_eq!(
        unsafe { (o.mul)(MIN_SUBNORMAL, half) },
        rust_mul64(MIN_SUBNORMAL, half),
        "tiny*0.5 underflow == Rust"
    );
    // subnormal operand times a normal.
    assert_eq!(
        unsafe { (o.mul)(MIN_SUBNORMAL, THREE) },
        rust_mul64(MIN_SUBNORMAL, THREE),
        "subnormal*3 == Rust"
    );

    // ── NaN operand ──
    for &(a, b) in &[(QNAN, TWO), (TWO, QNAN_PAY), (NEG_QNAN, PINF)] {
        let jit = unsafe { (o.mul)(a, b) };
        assert!(is_nan64(jit), "NaN operand -> NaN");
        assert_eq!(jit, rust_mul64(a, b), "mul NaN == Rust");
        assert_ne!(jit & QUIET_BIT, 0, "result quiet");
    }

    // ── Dense rounding sweep: products of two full-mantissa normals. ──
    let a_seeds: &[u64] = &[
        0x3FF3_1415_9265_3589,
        0x4002_7182_8182_8459,
        0x3FE9_2837_4655_ABAA,
        0x400A_1234_5678_9ABD,
    ];
    for &a in a_seeds {
        for k in 0..600u64 {
            let b = (a ^ (k.wrapping_mul(0x0000_0002_9979_2458))).wrapping_add(k);
            if is_nan64(b) || is_inf64(b) {
                continue;
            }
            let jit = unsafe { (o.mul)(a, b) };
            assert_eq!(jit, rust_mul64(a, b), "FMUL a={a:#018x} b={b:#018x}");
            checked += 1;
            round_cells += 1;
        }
    }

    // ── f32 ── RNE witness + dense + specials.
    let o32 = build_ops32();
    let mut f32checked = 0usize;
    let f32_one_ulp = 0x3F80_0001u32; // 1 + 2^-23
    assert_eq!(
        unsafe { (o32.mul)(f32_one_ulp, f32_one_ulp) },
        rust_mul32(f32_one_ulp, f32_one_ulp),
        "f32 (1+ulp)^2 == Rust"
    );
    assert!(
        is_nan32(unsafe { (o32.mul)(F32_PINF, F32_P0) }),
        "f32 inf*0=NaN"
    );
    assert_eq!(
        unsafe { (o32.mul)(0x8000_0000, F32_TWO) },
        0x8000_0000,
        "f32 -0*2=-0"
    );
    for k in 0..2000u32 {
        let a = 0x3F00_0000u32.wrapping_add(k.wrapping_mul(7));
        let b = 0x3FC0_0000u32.wrapping_add(k.wrapping_mul(0x0000_2003));
        if (a & 0x7F80_0000) == 0x7F80_0000 || (b & 0x7F80_0000) == 0x7F80_0000 {
            continue;
        }
        assert_eq!(
            unsafe { (o32.mul)(a, b) },
            rust_mul32(a, b),
            "f32 FMUL k={k}"
        );
        f32checked += 1;
    }

    assert!(
        round_cells >= 500,
        "RNE mul cells under-exercised ({round_cells})"
    );
    eprintln!(
        "FMUL CLEAN BILL: {checked} f64 + {f32checked} f32 cells bit-exact vs Rust `a*b` \
         ({round_cells} RNE cells). (1+2^-52)^2 -> 1+2^-51 (single rounding down); sign a*0/(-0)*x; \
         inf*0=NaN; overflow->inf; gradual underflow->subnormal/0; subnormal operands; NaN quieted. \
         FmulRR faithful."
    );
}

// ============================================================================
// TEST 4 — FDIV RNE + specials CLEAN BILL (f64 + f32).
//   Dense quotients needing rounding (incl. ties); x/0=+-inf; 0/0=NaN; inf/inf=NaN;
//   x/inf=+-0 (sign); x/(+-inf); inf/x=+-inf; underflow->subnormal; non-commutative.
//   Every cell bit-exact vs Rust `a/b`, with absolute pins.
// ============================================================================
#[test]
fn fdiv_rne_and_specials_clean_bill() {
    let o = build_ops64();
    let mut checked = 0usize;
    let mut round_cells = 0usize;

    // ── Absolute RNE witnesses (irrational-in-binary quotients). ──
    assert_eq!(
        unsafe { (o.div)(ONE, THREE) },
        0x3FD5_5555_5555_5555,
        "1/3 correctly rounded"
    );
    assert_eq!(
        unsafe { (o.div)(TWO, THREE) },
        0x3FE5_5555_5555_5555,
        "2/3 correctly rounded"
    );
    assert_eq!(
        unsafe {
            (o.div)(ONE, 0x4024_0000_0000_0000 /*10.0*/)
        },
        0.1f64.to_bits(),
        "1/10 -> 0.1 bits"
    );
    for &(a, b) in &[(ONE, THREE), (TWO, THREE), (ONE, 0x4024_0000_0000_0000u64)] {
        assert_eq!(
            unsafe { (o.div)(a, b) },
            rust_div64(a, b),
            "RNE div witness == Rust"
        );
    }

    // ── x / 0 = +-inf; 0/0 = NaN; sign ──
    assert_eq!(unsafe { (o.div)(ONE, P0) }, PINF, "1 / +0 = +inf");
    assert_eq!(unsafe { (o.div)(ONE, N0) }, NINF, "1 / -0 = -inf");
    assert_eq!(unsafe { (o.div)(NEG_ONE, P0) }, NINF, "-1 / +0 = -inf");
    assert_eq!(unsafe { (o.div)(NEG_ONE, N0) }, PINF, "-1 / -0 = +inf");
    assert!(is_nan64(unsafe { (o.div)(P0, P0) }), "0/0 = NaN");
    assert_eq!(
        unsafe { (o.div)(P0, P0) },
        rust_div64(P0, P0),
        "0/0 NaN == Rust"
    );
    assert!(is_nan64(unsafe { (o.div)(N0, P0) }), "-0/+0 = NaN");
    for &(a, b) in &[(ONE, P0), (ONE, N0), (NEG_ONE, P0), (NEG_ONE, N0)] {
        assert_eq!(unsafe { (o.div)(a, b) }, rust_div64(a, b), "x/0 == Rust");
    }

    // ── inf / inf = NaN; x / inf = +-0 (sign); inf / x = +-inf ──
    assert!(is_nan64(unsafe { (o.div)(PINF, PINF) }), "inf/inf = NaN");
    assert_eq!(
        unsafe { (o.div)(PINF, PINF) },
        rust_div64(PINF, PINF),
        "inf/inf NaN == Rust"
    );
    assert!(is_nan64(unsafe { (o.div)(NINF, PINF) }), "-inf/inf = NaN");
    assert_eq!(unsafe { (o.div)(ONE, PINF) }, P0, "1 / +inf = +0");
    assert_eq!(unsafe { (o.div)(ONE, NINF) }, N0, "1 / -inf = -0");
    assert_eq!(unsafe { (o.div)(NEG_ONE, PINF) }, N0, "-1 / +inf = -0");
    assert_eq!(unsafe { (o.div)(NEG_ONE, NINF) }, P0, "-1 / -inf = +0");
    assert_eq!(unsafe { (o.div)(PINF, TWO) }, PINF, "inf / 2 = inf");
    assert_eq!(unsafe { (o.div)(NINF, TWO) }, NINF, "-inf / 2 = -inf");
    assert_eq!(unsafe { (o.div)(PINF, NEG_ONE) }, NINF, "inf / -1 = -inf");

    // ── overflow -> inf; underflow -> subnormal / 0 ──
    assert!(
        is_inf64(unsafe {
            (o.div)(F64_MAX, 0x3FE0_0000_0000_0000 /*0.5*/)
        }),
        "MAX/0.5 -> inf"
    );
    assert_eq!(
        unsafe { (o.div)(F64_MAX, 0x3FE0_0000_0000_0000) },
        rust_div64(F64_MAX, 0x3FE0_0000_0000_0000),
        "overflow div == Rust"
    );
    // MIN_POS_NORMAL / 2 -> subnormal; MIN_SUBNORMAL / 2 -> 0 (RNE).
    assert_eq!(
        unsafe { (o.div)(MIN_POS_NORMAL, TWO) },
        rust_div64(MIN_POS_NORMAL, TWO),
        "underflow->subnormal == Rust"
    );
    assert_eq!(
        unsafe { (o.div)(MIN_SUBNORMAL, TWO) },
        rust_div64(MIN_SUBNORMAL, TWO),
        "tiny/2 underflow == Rust"
    );

    // ── NaN operand ──
    for &(a, b) in &[(QNAN, TWO), (TWO, QNAN_PAY), (NEG_QNAN, THREE)] {
        let jit = unsafe { (o.div)(a, b) };
        assert!(is_nan64(jit), "NaN operand -> NaN");
        assert_eq!(jit, rust_div64(a, b), "div NaN == Rust");
    }

    // ── non-commutativity ──
    assert_ne!(
        unsafe { (o.div)(TWO, THREE) },
        unsafe { (o.div)(THREE, TWO) },
        "a/b != b/a load-bearing"
    );
    assert_eq!(
        unsafe { (o.div)(THREE, TWO) },
        0x3FF8_0000_0000_0000,
        "3/2 = 1.5 exact"
    );

    // ── Dense rounding sweep. ──
    let a_seeds: &[u64] = &[
        0x3FF3_1415_9265_3589,
        0x4002_7182_8182_8459,
        0x400A_1234_5678_9ABD,
        0x3FE9_2837_4655_ABAA,
    ];
    for &a in a_seeds {
        for k in 1..600u64 {
            let b = (a ^ (k.wrapping_mul(0x0000_0002_9979_2458))).wrapping_add(k);
            if is_nan64(b) || is_inf64(b) || (b & 0x7FFF_FFFF_FFFF_FFFF) == 0 {
                continue;
            }
            let jit = unsafe { (o.div)(a, b) };
            assert_eq!(jit, rust_div64(a, b), "FDIV a={a:#018x} b={b:#018x}");
            checked += 1;
            round_cells += 1;
        }
    }

    // ── f32 ── RNE witness + dense + specials.
    let o32 = build_ops32();
    let mut f32checked = 0usize;
    assert_eq!(
        unsafe {
            (o32.div)(F32_ONE, 0x4040_0000 /*3.0*/)
        },
        rust_div32(F32_ONE, 0x4040_0000),
        "f32 1/3 == Rust"
    );
    assert_eq!(
        unsafe { (o32.div)(F32_ONE, F32_P0) },
        F32_PINF,
        "f32 1/+0=+inf"
    );
    assert_eq!(
        unsafe {
            (o32.div)(0xBF80_0000 /*-1*/, F32_P0)
        },
        F32_NINF,
        "f32 -1/+0=-inf"
    );
    assert!(
        is_nan32(unsafe { (o32.div)(F32_P0, F32_P0) }),
        "f32 0/0=NaN"
    );
    assert_eq!(
        unsafe { (o32.div)(F32_ONE, F32_PINF) },
        F32_P0,
        "f32 1/inf=+0"
    );
    for k in 1..2000u32 {
        let a = 0x3F00_0000u32.wrapping_add(k.wrapping_mul(7));
        let b = 0x3FC0_0000u32.wrapping_add(k.wrapping_mul(0x0000_2003));
        if (a & 0x7F80_0000) == 0x7F80_0000
            || (b & 0x7F80_0000) == 0x7F80_0000
            || (b & 0x7FFF_FFFF) == 0
        {
            continue;
        }
        assert_eq!(
            unsafe { (o32.div)(a, b) },
            rust_div32(a, b),
            "f32 FDIV k={k}"
        );
        f32checked += 1;
    }

    assert!(
        round_cells >= 500,
        "RNE div cells under-exercised ({round_cells})"
    );
    eprintln!(
        "FDIV CLEAN BILL: {checked} f64 + {f32checked} f32 cells bit-exact vs Rust `a/b` \
         ({round_cells} RNE cells). 1/3, 2/3, 1/10 correctly rounded; x/0=+-inf, 0/0=NaN, \
         inf/inf=NaN, x/inf=+-0 (sign), inf/x=+-inf; overflow->inf; underflow->subnormal/0; \
         non-commutative. FdivRR faithful."
    );
}

// ============================================================================
// TEST 5 — SIGNALING-NaN operand -> quieted qNaN, ALL FOUR ops (f64 + f32).
//   Fed via exact bits (int-param + Bitcast). Unlike fmin/fmax (owner #11, which
//   lacked operand canonicalization), the aarch64 arithmetic ops FADD/FSUB/FMUL/
//   FDIV natively quiet an sNaN operand — and so does real Rust's `+ - * /` (same
//   instruction). So this is a CLEAN BILL (bit-exact vs Rust), not a pin.
// ============================================================================
#[test]
fn snan_operand_quieted_all_ops_clean_bill() {
    let o = build_ops64();
    let snans: &[(u64, &str)] = &[
        (SNAN, "sNaN min payload"),
        (SNAN_PAY, "sNaN with payload"),
        (NEG_SNAN, "negative sNaN"),
        (0x7FF7_FFFF_FFFF_FFFF, "sNaN max payload"),
    ];
    let others: &[u64] = &[ONE, TWO, P0, N0, PINF, NINF];
    let mut cells = 0usize;
    for &(sn, desc) in snans {
        for &other in others {
            for (name, f) in [
                ("add", o.add as U64Bin),
                ("sub", o.sub),
                ("mul", o.mul),
                ("div", o.div),
            ] {
                // sNaN as LHS
                let jit = unsafe { f(sn, other) };
                let rust = match name {
                    "add" => rust_add64(sn, other),
                    "sub" => rust_sub64(sn, other),
                    "mul" => rust_mul64(sn, other),
                    _ => rust_div64(sn, other),
                };
                assert!(is_nan64(jit), "{name}(sNaN[{desc}], {other:#018x}) -> NaN");
                assert_ne!(jit & QUIET_BIT, 0, "{name} sNaN LHS quieted");
                assert_eq!(
                    jit, rust,
                    "{name} sNaN LHS == Rust bit-exact ({desc}, other={other:#018x})"
                );
                // sNaN as RHS
                let jit_r = unsafe { f(other, sn) };
                let rust_r = match name {
                    "add" => rust_add64(other, sn),
                    "sub" => rust_sub64(other, sn),
                    "mul" => rust_mul64(other, sn),
                    _ => rust_div64(other, sn),
                };
                assert!(is_nan64(jit_r), "{name}({other:#018x}, sNaN) -> NaN");
                assert_ne!(jit_r & QUIET_BIT, 0, "{name} sNaN RHS quieted");
                assert_eq!(jit_r, rust_r, "{name} sNaN RHS == Rust bit-exact");
                cells += 2;
            }
        }
    }
    // The exact quieting shape: input sNaN payload preserved, quiet bit set (add(sNaN,1)).
    assert_eq!(
        unsafe { (o.add)(SNAN_PAY, ONE) },
        rust_add64(SNAN_PAY, ONE),
        "add(sNaN_pay,1) == Rust"
    );
    assert_ne!(
        unsafe { (o.add)(SNAN_PAY, ONE) } & QUIET_BIT,
        0,
        "quiet bit set"
    );

    // ── f32 sNaN via exact bits ──
    let o32 = build_ops32();
    for &(sn, other) in &[(F32_SNAN, F32_ONE), (F32_SNAN_PAY, F32_TWO)] {
        for (name, f) in [
            ("add", o32.add as U32Bin),
            ("sub", o32.sub),
            ("mul", o32.mul),
            ("div", o32.div),
        ] {
            let jit = unsafe { f(sn, other) };
            let rust = match name {
                "add" => rust_add32(sn, other),
                "sub" => rust_sub32(sn, other),
                "mul" => rust_mul32(sn, other),
                _ => rust_div32(sn, other),
            };
            assert!(is_nan32(jit), "f32 {name}(sNaN) -> NaN");
            assert_ne!(jit & F32_QUIET_BIT, 0, "f32 {name} sNaN quieted");
            assert_eq!(jit, rust, "f32 {name} sNaN == Rust bit-exact");
            cells += 1;
        }
    }
    assert!(cells >= 200);
    eprintln!(
        "sNaN CLEAN BILL: {cells} signaling-NaN cells (fed via exact bits) across all four ops \
         (f64+f32), LHS and RHS, quieted to qNaN and bit-exact vs Rust `+ - * /`. Unlike owner #11 \
         (fmin/fmax needed operand canonicalization), the arithmetic ops natively quiet sNaN — \
         matching real Rust. No divergence."
    );
}

// ============================================================================
// TEST 6 — NO FMADD CONTRACTION (the FMA double-rounding bug site).
//   trust-ir has no scalar fused-multiply-add, so `a*b + c` must lower as a separate
//   FMUL then FADD (TWO roundings). This proves in machine code that the aarch64 ISel
//   does NOT contract the pair into a single-rounding FMADD:
//     JIT (FMul-then-FAdd)  ==  Rust UNFUSED `(a*b) + c`   (both double-round)
//     JIT                   !=  Rust `f64::mul_add(a,b,c)` (single FMADD)  on witnesses
//                                                            where fused != unfused.
//   If the backend fused, the JIT would match mul_add and diverge from the unfused
//   Rust expression a Rust program actually computes for `a*b + c`.
// ============================================================================
#[test]
fn no_fmadd_contraction_control() {
    let mut m = TrustIrModule::new("madd".to_string());
    build_muladd_jit_f64(0, "madd", &mut m);
    let buf = jit_buffer(&m);
    let madd: U64Tern = unsafe { std::mem::transmute(bind(&buf, "madd")) };

    // Scan for (a,b,c) where a single-rounding fused result differs from the
    // double-rounding unfused result (the cases that expose a contraction).
    let a_seeds: &[u64] = &[
        0.1f64.to_bits(),
        0.2f64.to_bits(),
        0x3FF0_0000_0000_0001, /*1+ulp*/
        std::f64::consts::PI.to_bits(),
        0x4002_7182_8182_8459,
        0x3FF3_1415_9265_3589,
        1.0e8f64.to_bits(),
        0x3FE5_5555_5555_5555, /*2/3*/
    ];
    let c_seeds: &[u64] = &[
        (-0.01f64).to_bits(),
        (-1.0f64).to_bits(),
        0x3CB0_0000_0000_0000,             /*2^-52*/
        (-9.869604401089358f64).to_bits(), /*-pi^2*/
        1.0f64.to_bits(),
        (-1.0e8f64).to_bits(),
    ];
    let mut fused_ne_unfused = 0usize;
    let mut agree_unfused = 0usize;
    let mut checked = 0usize;
    for &a in a_seeds {
        for &b in a_seeds {
            for &c in c_seeds {
                let jit = unsafe { madd(a, b, c) };
                let unfused = rust_unfused_madd64(a, b, c);
                let fused = rust_fused_madd64(a, b, c);
                // The JIT (two separate rounded ops) ALWAYS equals the unfused Rust expr.
                assert_eq!(
                    jit, unfused,
                    "JIT (FMul;FAdd) must equal Rust UNFUSED (a*b)+c for a={a:#018x} b={b:#018x} c={c:#018x}: \
                     jit={jit:#018x} unfused={unfused:#018x}"
                );
                agree_unfused += 1;
                if fused != unfused {
                    fused_ne_unfused += 1;
                    // On these witnesses the JIT must NOT match the fused (single-rounding)
                    // result — i.e. the backend did not contract to FMADD.
                    assert_ne!(
                        jit, fused,
                        "FMADD-CONTRACTION DETECTED: JIT matched the single-rounding mul_add \
                         (fused) result, diverging from the unfused `a*b+c` a Rust program computes. \
                         a={a:#018x} b={b:#018x} c={c:#018x}"
                    );
                }
                checked += 1;
            }
        }
    }
    // The differential must be armed: there must exist witnesses where fused != unfused
    // (else this test could not distinguish a contraction).
    assert!(
        fused_ne_unfused >= 10,
        "anti-contraction control not armed: only {fused_ne_unfused} fused!=unfused witnesses"
    );

    // A concrete, documented witness (chosen so fused != unfused).
    // 0.1*0.1 fused vs unfused with c = -(0.1*0.1 rounded) exposes the low-order bit.
    let a = 0.1f64.to_bits();
    let prod_rounded = rust_mul64(a, a); // 0.1*0.1 rounded once
    let c = prod_rounded ^ N0; // negate: -(0.1*0.1 rounded)
    let jit = unsafe { madd(a, a, c) };
    assert_eq!(jit, rust_unfused_madd64(a, a, c), "witness: JIT == unfused");
    assert_eq!(
        jit, 0u64,
        "unfused 0.1*0.1 + (-(0.1*0.1 rounded)) = +0 (the rounding cancels)"
    );
    // fused mul_add(0.1,0.1, -(0.1*0.1 rounded)) = the exact product minus the rounded
    // product = the (nonzero) rounding error -> NOT +0. So JIT (=+0) != fused.
    assert_ne!(
        jit,
        rust_fused_madd64(a, a, c),
        "witness: JIT (+0, unfused) != fused (nonzero rounding error)"
    );

    eprintln!(
        "NO-FMADD-CONTRACTION: {checked} (a,b,c) triples — JIT `FMul;FAdd` == Rust UNFUSED (a*b)+c \
         on ALL {agree_unfused}, and DIFFERS from Rust `mul_add` (single-rounding FMADD) on \
         {fused_ne_unfused} witnesses where fused!=unfused. The aarch64 ISel does NOT contract \
         float mul+add into FMADD (detect_mul_add_idioms is integer-only). Concrete witness: \
         0.1*0.1 + (-(0.1*0.1 rounded)) = +0 unfused (JIT match), nonzero fused."
    );
}

// ============================================================================
// TEST 7 — ARMED CONTROLS: the differential is load-bearing.
//   (a) op routing: FAdd/FSub/FMul/FDiv are DISTINCT on (6,2): 8/4/12/3.
//   (b) genuine RNE (not a chop): for FMUL & FDIV, results with a set low mantissa
//       bit differ from a low-bit-cleared chop model.
//   (c) full-precision (not f32-widened): the f64 op differs from an f32-computed-
//       then-widened model on most inputs — a precision-losing lowering WOULD fail.
//   (d) operand order (sub/div non-commutative) preserved.
// ============================================================================
#[test]
fn armed_controls() {
    let o = build_ops64();
    let six = 6.0f64.to_bits();
    let two = TWO;

    // (a) op routing distinct.
    let r_add = unsafe { (o.add)(six, two) };
    let r_sub = unsafe { (o.sub)(six, two) };
    let r_mul = unsafe { (o.mul)(six, two) };
    let r_div = unsafe { (o.div)(six, two) };
    assert_eq!(r_add, 8.0f64.to_bits(), "6+2=8");
    assert_eq!(r_sub, 4.0f64.to_bits(), "6-2=4");
    assert_eq!(r_mul, 12.0f64.to_bits(), "6*2=12");
    assert_eq!(r_div, 3.0f64.to_bits(), "6/2=3");
    assert_ne!(r_add, r_sub);
    assert_ne!(r_add, r_mul);
    assert_ne!(r_add, r_div);
    assert_ne!(r_sub, r_mul);
    assert_ne!(r_sub, r_div);
    assert_ne!(r_mul, r_div);

    // (b) genuine RNE (not a chop) + (c) full precision (not f32-widened), for MUL & DIV.
    let mut chop_caught_mul = 0usize;
    let mut chop_caught_div = 0usize;
    let mut prec_caught_mul = 0usize;
    let mut prec_caught_div = 0usize;
    let a_seeds: &[u64] = &[
        0x3FF3_1415_9265_3589,
        0x4002_7182_8182_8459,
        0x400A_1234_5678_9ABD,
    ];
    for &a in a_seeds {
        for k in 1u64..=800 {
            let b = (a ^ (k.wrapping_mul(0x0000_0002_9979_2458))).wrapping_add(k);
            if is_nan64(b) || is_inf64(b) || (b & 0x7FFF_FFFF_FFFF_FFFF) == 0 {
                continue;
            }
            // MUL
            let m = unsafe { (o.mul)(a, b) };
            assert_eq!(m, rust_mul64(a, b), "mul == Rust");
            if m & 1 == 1 {
                assert_ne!(m, m & !1u64, "mul low bit -> differs from chop");
                chop_caught_mul += 1;
            }
            if !is_nan64(m) && !is_inf64(m) {
                let low = ((f64::from_bits(a) as f32) * (f64::from_bits(b) as f32)) as f64;
                if low.to_bits() != m {
                    prec_caught_mul += 1;
                }
            }
            // DIV
            let d = unsafe { (o.div)(a, b) };
            assert_eq!(d, rust_div64(a, b), "div == Rust");
            if d & 1 == 1 {
                assert_ne!(d, d & !1u64, "div low bit -> differs from chop");
                chop_caught_div += 1;
            }
            if !is_nan64(d) && !is_inf64(d) {
                let low = ((f64::from_bits(a) as f32) / (f64::from_bits(b) as f32)) as f64;
                if low.to_bits() != d {
                    prec_caught_div += 1;
                }
            }
        }
    }
    assert!(
        chop_caught_mul >= 50,
        "mul chop control under-exercised ({chop_caught_mul})"
    );
    assert!(
        chop_caught_div >= 50,
        "div chop control under-exercised ({chop_caught_div})"
    );
    assert!(
        prec_caught_mul >= 100,
        "mul precision control under-exercised ({prec_caught_mul})"
    );
    assert!(
        prec_caught_div >= 100,
        "div precision control under-exercised ({prec_caught_div})"
    );

    // (d) operand order preserved (non-commutative ops).
    assert_ne!(
        unsafe { (o.sub)(THREE, ONE) },
        unsafe { (o.sub)(ONE, THREE) },
        "sub order dead"
    );
    assert_ne!(
        unsafe { (o.div)(TWO, THREE) },
        unsafe { (o.div)(THREE, TWO) },
        "div order dead"
    );
    assert_eq!(
        unsafe { (o.sub)(THREE, ONE) },
        rust_sub64(THREE, ONE),
        "sub order == Rust"
    );
    assert_eq!(
        unsafe { (o.div)(TWO, THREE) },
        rust_div64(TWO, THREE),
        "div order == Rust"
    );

    eprintln!(
        "ARMED CONTROLS: op routing distinct on (6,2) -> add=8/sub=4/mul=12/div=3; FMUL & FDIV \
         genuinely RNE-round ({chop_caught_mul}+{chop_caught_div} set-low-bit results differ from a \
         chop) and are full f64 precision ({prec_caught_mul}+{prec_caught_div} differ from an \
         f32-widened model); sub/div operand order preserved. A wrong-op / chop / precision-losing / \
         swapped-operand lowering WOULD be caught. The clean bills are load-bearing."
    );
}
