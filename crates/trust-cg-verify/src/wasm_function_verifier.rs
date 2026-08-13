// trust-cg-verify/wasm_function_verifier.rs - WebAssembly function-level verify
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Mirror of [`crate::riscv_function_verifier`] for the STACK-MACHINE wasm
// backend. The register backends (AArch64 / x86-64 / RISC-V) reconstruct a
// lowering obligation's machine side from the REAL emitted opcode + its REGISTER
// operands. wasm has no register operands: an instruction consumes its operands
// from the VALUE STACK. The reconstruction therefore models the stack operands
// as the shared symbol table — fresh typed symbolic values standing for "the top
// of the value stack" at the point the op executes — and decodes the REAL emitted
// opcode BYTE (via `wasm_semantics::decode_int_binop` etc.) to choose the machine
// side. The source side is built from the INTENDED trust-ir op over the SAME
// symbols. The two agree IFF the backend emitted a semantically correct opcode
// with correct stack-operand order:
//
//   * a WRONG opcode byte (e.g. `i32.sub` 0x6b for an intended add) ⇒ machine =
//     bvsub, source = bvadd ⇒ REFUTE;
//   * a non-commutative op (sub / shift / comparison) with SWAPPED stack operands
//     ⇒ REFUTE.
//
// That non-vacuous refutability is the content the credit rule counts, EXACTLY as
// for the register backends — even though a correct commutative lowering
// reconstructs to `bvadd == bvadd`.
//
// ANTI-substring (anti-f81e45b): the opcode->source binding is a TYPED EXHAUSTIVE
// match ([`opcode_to_source_op`]); the machine side is decoded from the typed
// opcode byte. There is NO `name.contains` lookup anywhere on this path. Asserted
// by `tests/reconstruction_wasm.rs`.

//! WebAssembly function-level verification — stack-machine operand
//! reconstruction (task #71).
//!
//! [`reconstruct_alu_obligation`] rebuilds the machine side of a wasm scalar
//! lowering FROM THE REAL EMITTED OPCODE over fresh symbolic value-stack
//! operands; [`reconstruction_discharges_valid`] is the coverage-gate credit
//! hook (mirrors [`crate::riscv_function_verifier::reconstruction_discharges_valid`]).

use trust_cg_ir::WasmOpcode;

use crate::lowering_proof::{
    MachineSideProvenance, ProofObligation, VerificationConfig, verify_by_evaluation_with_config,
};
use crate::smt::SmtExpr;
use crate::verify::VerificationResult;

// ---------------------------------------------------------------------------
// Verifier-side wasm ISel instruction shape (stack-machine)
// ---------------------------------------------------------------------------

/// A single wasm ISel instruction as the verifier sees it: a typed
/// [`WasmOpcode`] plus the operand WIDTH(s) it consumes from the value stack.
///
/// wasm has no register operands, so unlike the register-backend ISel shapes
/// this carries no operand list — the opcode fixes the operand count and types,
/// and reconstruction binds fresh symbolic stack values at the operand width. The
/// `operand_width_bits` records the value-stack operand width the opcode operates
/// at (32 for i32/f32, 64 for i64/f64); it disambiguates the i32-vs-i64 (and
/// f32-vs-f64) share of the typed source-op family.
#[derive(Debug, Clone)]
pub struct WasmISelInst {
    /// The typed wasm opcode this instruction emits.
    pub opcode: WasmOpcode,
    /// The value-stack operand width in bits (32 or 64). For casts this is the
    /// width of the (single) SOURCE stack operand.
    pub operand_width_bits: u32,
}

impl WasmISelInst {
    /// Construct a verifier-side wasm ISel instruction.
    pub fn new(opcode: WasmOpcode, operand_width_bits: u32) -> Self {
        Self {
            opcode,
            operand_width_bits,
        }
    }
}

/// A wasm ISel function as the verifier sees it: an ordered instruction stream.
#[derive(Debug, Clone)]
pub struct WasmISelFunction {
    /// Function name (carried through into any report).
    pub name: String,
    /// Instructions in deterministic emission order.
    pub insts: Vec<WasmISelInst>,
}

impl WasmISelFunction {
    /// Construct an empty verifier-side wasm ISel function.
    pub fn new(name: String) -> Self {
        Self {
            name,
            insts: Vec::new(),
        }
    }
}

// ===========================================================================
// Typed exhaustive opcode -> intended source op (NO substring) — task #71
// ===========================================================================

/// The intended trust-ir SOURCE op family for a reconstructable wasm opcode,
/// resolved by a TYPED EXHAUSTIVE match (NOT a string lookup). Mirrors
/// `riscv_function_verifier::RiscVSourceOp`.
#[derive(Debug, Clone, PartialEq)]
enum WasmSourceOp {
    /// Integer arithmetic (`encode_trust_ir_binop`): Iadd/Isub/Imul. Machine side
    /// is the matching wasm `iN.add/sub/mul` encoder.
    IntBinary(trust_cg_lower::instructions::Opcode),
    /// Integer division/remainder (`encode_trust_ir_binop`): Sdiv/Udiv/Srem/Urem,
    /// with the matching trap precondition(s). Machine side is the wasm
    /// `iN.div_s/div_u/rem_s/rem_u` encoder.
    IntDivRem(trust_cg_lower::instructions::Opcode),
    /// Integer bitwise (`encode_trust_ir_bitwise_binop`): Band/Bor/Bxor. Machine
    /// side is the wasm `iN.and/or/xor` encoder.
    Bitwise(trust_cg_lower::instructions::Opcode),
    /// Integer shift (`encode_trust_ir_shift`): Ishl/Sshr/Ushr. Machine side is
    /// the FAITHFUL amount-MASKED wasm `iN.shl/shr_s/shr_u` encoder, paired with a
    /// LOAD-BEARING `amount < width` precondition (#57). In range the mask is the
    /// identity; out of range the masked machine side and the clamp-to-0 trust-ir
    /// side DIVERGE, so the precondition is genuinely required for Valid.
    Shift(trust_cg_lower::instructions::Opcode),
    /// Integer comparison value op (`encode_trust_ir_icmp`, lifted i1->i32 to
    /// match the wasm i32 0/1 result). Machine side is the wasm `iN.<cmp>` encoder.
    IntCompare(trust_cg_lower::instructions::IntCC),
    /// FP arithmetic (`encode_trust_ir_fp_binop`): Fadd/Fsub/Fmul/Fdiv. Machine
    /// side is the wasm `fN.add/sub/mul/div` encoder.
    FpBinary(trust_cg_lower::instructions::Opcode),
    /// FP unary value op (`try_encode_trust_ir_fp_unaryop` for Fneg/Fabs/Fsqrt;
    /// `encode_trust_ir_fceil/ffloor/ftrunc` for the round-to-integral forms).
    /// Machine side is the wasm `fN.<unop>` encoder.
    FpUnary(trust_cg_lower::instructions::Opcode),
    /// FP comparison value op (`encode_trust_ir_fcmp`, lifted i1->i32). Machine
    /// side is the wasm `fN.<cmp>` encoder. Only the ORDERED predicates that wasm
    /// emits directly (eq/ne/lt/gt/le/ge — wasm `ne` is unordered, the rest
    /// ordered) are reconstructable; the trust-ir FloatCC chosen matches the wasm
    /// opcode's exact ordered/unordered behaviour.
    FpCompare(trust_cg_lower::instructions::FloatCC),
    /// Integer-width cast: `i32.wrap_i64` (trunc 64->32),
    /// `i64.extend_i32_s`/`_u` (sign/zero-extend 32->64). Machine side is the wasm
    /// cast encoder; source side is the trust-ir trunc/sext/uext.
    IntCast(WasmIntCastKind),
    /// FP-FORMAT cast: `f32.demote_f64` (narrow) / `f64.promote_f32` (widen).
    /// Machine side is the wasm format-cast; source side is the trust-ir
    /// `Fdemote`/`Fpromote` (`encode_trust_ir_fp_format_convert` at the dest
    /// format).
    FpFormatCast(WasmFpFormatKind),
    /// Population count: `i32.popcnt` / `i64.popcnt`. Machine side is the wasm
    /// `popcnt` bit-count encoder (`wasm_semantics::encode_popcnt`); source side
    /// is the trust-ir `Ctpop` (`encode_trust_ir_ctpop`). A wrong bit-count op
    /// (popcnt-for-some-other-bitop) diverges for almost every input ⇒ REFUTE.
    Popcnt,
    /// Bit-reinterpret (bitcast): `i32.reinterpret_f32` / `i64.reinterpret_f64` /
    /// `f32.reinterpret_i32` / `f64.reinterpret_i64`. A pure, width-preserving bit
    /// copy. Machine side is `wasm_semantics::encode_reinterpret` (identity over
    /// the operand bitvector decoded at the byte's width); source side is the
    /// trust-ir `Bitcast` (`encode_trust_ir_bitcast`, also the identity). The
    /// reconstruction content is the WIDTH: a wrong-WIDTH reinterpret byte decodes
    /// to a different bitvector width ⇒ structurally distinct ⇒ REFUTE.
    Reinterpret,
    /// int->FP CONVERT: `f{32,64}.convert_i{32,64}_{s,u}`. The single SOURCE stack
    /// operand is an integer bitvector (`recon_src`); the machine side DECODES the
    /// real opcode byte to (src_width, fp_width, signed) and rebuilds the convert
    /// via `wasm_semantics::encode_convert_s`/`_u`; the source side is the trust-ir
    /// `encode_trust_ir_fcvt_from_sint`/`_uint` at the SAME signedness. A signed-
    /// for-unsigned lowering DIVERGES for a high-bit-set input ⇒ REFUTE (the
    /// evaluator now models the source signedness — `BvToFP` over a zero-extended
    /// operand for `_u`).
    Convert,
    /// SATURATING FP->int TRUNC: `i{32,64}.trunc_sat_f{32,64}_{s,u}` (0xfc prefix).
    /// The single SOURCE stack operand is an FP leaf (`recon_a`); the machine side
    /// DECODES the (0xfc prefix, sub-index) to (fp_width, int_width, signed) and
    /// rebuilds the SATURATING truncation via `wasm_semantics::encode_trunc_sat_s`/
    /// `_u`; the source side is the trust-ir `encode_trust_ir_fcvt_to_sint`/`_uint`.
    /// The evaluator now SATURATES + maps NaN->0, so a wrapping (mask-only) machine
    /// DIVERGES for an out-of-range input, and a signed-for-unsigned sub-index
    /// DIVERGES too ⇒ REFUTE.
    TruncSat,

    /// LANE-WISE INTEGER SIMD value op (`i32x4.add`/`i32x4.mul`). The two stack
    /// operands are 128-bit vectors (`recon_a`/`recon_b`, carried as two 64-bit
    /// halves each); the machine side DECODES the real 0xfd sub-opcode to the lane
    /// op + lane shape and rebuilds the FULL-VECTOR lane-wise op
    /// (`wasm_semantics::encode_i32x4_add`/`_mul`); the source side is the trust-ir
    /// scalar op `map_lanes`-applied at the SAME `i32x4` arrangement
    /// (`encode_trust_ir_lanewise_binop`). A WRONG sub-opcode (mul-for-add) or a
    /// WRONG lane width (i16x8 vs i32x4) yields a structurally different 128-bit
    /// value ⇒ REFUTE.
    SimdIntLane(trust_cg_lower::instructions::Opcode),
    /// LANE-WISE FP SIMD value op (`f32x4.add`/`f32x4.mul`). The packed op is four
    /// independent identical binary32 ops, so one representative FP lane
    /// (`recon_a`/`recon_b`, FP-typed) witnesses the full-vector value equivalence
    /// (mirrors the x86 packed-FP per-lane reconstruction). The machine side is
    /// `wasm_semantics::encode_f32x4_add_lane`/`_mul_lane`; the source side is the
    /// trust-ir `encode_trust_ir_fp_binop` at the SAME f32 width. A wrong op
    /// (mul-for-add) DIVERGES under the FP evaluator ⇒ REFUTE.
    SimdFpLane(trust_cg_lower::instructions::Opcode),
}

/// The integer-width cast shape a reconstructable wasm cast opcode performs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WasmIntCastKind {
    /// `i32.wrap_i64` — 64->32 truncation.
    Wrap,
    /// `i64.extend_i32_s` — 32->64 sign extension.
    SExt,
    /// `i64.extend_i32_u` — 32->64 zero extension.
    UExt,
}

/// The FP-format cast shape a reconstructable wasm cast opcode performs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WasmFpFormatKind {
    /// `f32.demote_f64` — narrow f64->f32.
    Demote,
    /// `f64.promote_f32` — widen f32->f64.
    Promote,
}

/// Resolve the INTENDED trust-ir source op for a reconstructable wasm opcode via
/// a TYPED, EXHAUSTIVE match — NOT a string lookup (anti-f81e45b). Mirrors
/// `riscv_function_verifier::opcode_to_source_op`.
///
/// Returns `None` for every NON-reconstructable opcode (structural control flow /
/// memory / locals / calls / constants / float<->int conversions / SIMD), so the
/// caller leaves those out of the value-equivalence credit. Wildcard-free over
/// the reconstructable arms; falls through to `None` for the rest.
fn opcode_to_source_op(opcode: WasmOpcode) -> Option<WasmSourceOp> {
    use WasmOpcode as O;
    use WasmSourceOp as S;
    use trust_cg_lower::instructions::{FloatCC, IntCC, Opcode};
    Some(match opcode {
        // ---- Integer arithmetic ----
        O::I32Add | O::I64Add => S::IntBinary(Opcode::Iadd),
        O::I32Sub | O::I64Sub => S::IntBinary(Opcode::Isub),
        O::I32Mul | O::I64Mul => S::IntBinary(Opcode::Imul),
        // ---- Integer division / remainder (trap-guarded) ----
        O::I32DivS | O::I64DivS => S::IntDivRem(Opcode::Sdiv),
        O::I32DivU | O::I64DivU => S::IntDivRem(Opcode::Udiv),
        O::I32RemS | O::I64RemS => S::IntDivRem(Opcode::Srem),
        O::I32RemU | O::I64RemU => S::IntDivRem(Opcode::Urem),
        // ---- Integer bitwise (commutative) ----
        O::I32And | O::I64And => S::Bitwise(Opcode::Band),
        O::I32Or | O::I64Or => S::Bitwise(Opcode::Bor),
        O::I32Xor | O::I64Xor => S::Bitwise(Opcode::Bxor),
        // ---- Integer shifts (non-commutative; amount<width precond) ----
        O::I32Shl | O::I64Shl => S::Shift(Opcode::Ishl),
        O::I32ShrS | O::I64ShrS => S::Shift(Opcode::Sshr),
        O::I32ShrU | O::I64ShrU => S::Shift(Opcode::Ushr),
        // ---- Integer comparisons (non-commutative value ops, result i32) ----
        O::I32Eq | O::I64Eq => S::IntCompare(IntCC::Equal),
        O::I32Ne | O::I64Ne => S::IntCompare(IntCC::NotEqual),
        O::I32LtS | O::I64LtS => S::IntCompare(IntCC::SignedLessThan),
        O::I32LtU | O::I64LtU => S::IntCompare(IntCC::UnsignedLessThan),
        O::I32GtS | O::I64GtS => S::IntCompare(IntCC::SignedGreaterThan),
        O::I32GtU | O::I64GtU => S::IntCompare(IntCC::UnsignedGreaterThan),
        O::I32LeS | O::I64LeS => S::IntCompare(IntCC::SignedLessThanOrEqual),
        O::I32LeU | O::I64LeU => S::IntCompare(IntCC::UnsignedLessThanOrEqual),
        O::I32GeS | O::I64GeS => S::IntCompare(IntCC::SignedGreaterThanOrEqual),
        O::I32GeU | O::I64GeU => S::IntCompare(IntCC::UnsignedGreaterThanOrEqual),
        // ---- FP arithmetic ----
        O::F32Add | O::F64Add => S::FpBinary(Opcode::Fadd),
        O::F32Sub | O::F64Sub => S::FpBinary(Opcode::Fsub),
        O::F32Mul | O::F64Mul => S::FpBinary(Opcode::Fmul),
        O::F32Div | O::F64Div => S::FpBinary(Opcode::Fdiv),
        // ---- FP unary ----
        O::F32Abs | O::F64Abs => S::FpUnary(Opcode::Fabs),
        O::F32Neg | O::F64Neg => S::FpUnary(Opcode::Fneg),
        O::F32Sqrt | O::F64Sqrt => S::FpUnary(Opcode::Fsqrt),
        O::F32Ceil | O::F64Ceil => S::FpUnary(Opcode::Fceil),
        O::F32Floor | O::F64Floor => S::FpUnary(Opcode::Ffloor),
        O::F32Trunc | O::F64Trunc => S::FpUnary(Opcode::Ftrunc),
        // ---- FP comparisons (wasm ordered eq/lt/gt/le/ge; ne is unordered) ----
        O::F32Eq | O::F64Eq => S::FpCompare(FloatCC::Equal),
        O::F32Ne | O::F64Ne => S::FpCompare(FloatCC::UnorderedNotEqual),
        O::F32Lt | O::F64Lt => S::FpCompare(FloatCC::LessThan),
        O::F32Gt | O::F64Gt => S::FpCompare(FloatCC::GreaterThan),
        O::F32Le | O::F64Le => S::FpCompare(FloatCC::LessThanOrEqual),
        O::F32Ge | O::F64Ge => S::FpCompare(FloatCC::GreaterThanOrEqual),
        // ---- Integer-width casts ----
        O::I32WrapI64 => S::IntCast(WasmIntCastKind::Wrap),
        O::I64ExtendI32S => S::IntCast(WasmIntCastKind::SExt),
        O::I64ExtendI32U => S::IntCast(WasmIntCastKind::UExt),
        // ---- FP-format casts ----
        O::F32DemoteF64 => S::FpFormatCast(WasmFpFormatKind::Demote),
        O::F64PromoteF32 => S::FpFormatCast(WasmFpFormatKind::Promote),
        // ---- Population count (faithful bit-count; popcnt-for-other refutes) ----
        O::I32Popcnt | O::I64Popcnt => S::Popcnt,
        // ---- Bit-reinterpret (width-preserving bit-identity; wrong width refutes)
        O::I32ReinterpretF32
        | O::I64ReinterpretF64
        | O::F32ReinterpretI32
        | O::F64ReinterpretI64 => S::Reinterpret,

        // ---- int->FP CONVERT (signed/unsigned-sensitive, RNE) ----
        // Now FAITHFULLY reconstructable: the evaluator models the source
        // signedness (`BvToFP` over a zero-extended operand for the `_u` forms), so
        // a signed-for-unsigned convert DIVERGES for a high-bit-set input ⇒ REFUTE.
        O::F32ConvertI32S
        | O::F32ConvertI32U
        | O::F32ConvertI64S
        | O::F32ConvertI64U
        | O::F64ConvertI32S
        | O::F64ConvertI32U
        | O::F64ConvertI64S
        | O::F64ConvertI64U => S::Convert,
        // ---- SATURATING FP->int TRUNC (0xfc prefix, RTZ + saturate + NaN->0) ----
        // Now FAITHFULLY reconstructable: the evaluator SATURATES to the int range
        // and maps NaN->0, so a wrapping (mask-only) machine or a signed-for-unsigned
        // sub-index DIVERGES for an out-of-range input ⇒ REFUTE.
        O::I32TruncSatF32S
        | O::I32TruncSatF32U
        | O::I32TruncSatF64S
        | O::I32TruncSatF64U
        | O::I64TruncSatF32S
        | O::I64TruncSatF32U
        | O::I64TruncSatF64S
        | O::I64TruncSatF64U => S::TruncSat,

        // ---- LANE-WISE SIMD value ops (v128) ----
        // i32x4.add/mul: lane-wise integer over the full 128-bit vector.
        O::I32x4Add => S::SimdIntLane(Opcode::Iadd),
        O::I32x4Mul => S::SimdIntLane(Opcode::Imul),
        // f32x4.add/mul: lane-wise IEEE binary32 (one representative FP lane).
        O::F32x4Add => S::SimdFpLane(Opcode::Fadd),
        O::F32x4Mul => S::SimdFpLane(Opcode::Fmul),

        // All remaining non-reconstructable opcodes get no source-op credit here:
        // constants, locals/globals, memory, control flow, calls, fmin/fmax, and
        // the STRUCTURAL v128 forms (v128.load/store/const).
        _ => return None,
    })
}

/// FP `(exponent_bits, significand_bits)` for a value-stack width (32->f32,
/// 64->f64). `None` for an unsupported width (fails closed).
fn fp_format_from_width(width: u32) -> Option<(u32, u32)> {
    match width {
        32 => Some((8, 24)),
        64 => Some((11, 53)),
        _ => None,
    }
}

/// Map a width in bits to a trust-ir [`Type`]. The integer ALU/bitwise/shift/
/// icmp/fp encoders carry width in the operand `SmtExpr` sorts and ignore the
/// `Type` (`_ty`), so this is a faithful descriptor. `None` for an unsupported
/// width (fails the reconstruction closed).
fn width_to_type(width: u32) -> Option<trust_cg_lower::types::Type> {
    use trust_cg_lower::types::Type;
    match width {
        32 => Some(Type::I32),
        64 => Some(Type::I64),
        _ => None,
    }
}

/// `b != 0` precondition at the given operand width (div/rem trap guard).
fn nonzero(width: u32) -> SmtExpr {
    SmtExpr::var("recon_b", width)
        .eq_expr(SmtExpr::bv_const(0, width))
        .not_expr()
}

/// `¬(a == INT_MIN ∧ b == -1)` — the signed-division overflow wasm `div_s` traps
/// on (and SMT `bvsdiv` wraps on), at the given width.
fn no_sdiv_overflow(width: u32) -> SmtExpr {
    let int_min = SmtExpr::bv_const(1u64 << (width - 1), width);
    let minus_one = SmtExpr::bv_const(u64::MAX >> (64 - width), width); // all ones
    let a_is_min = SmtExpr::var("recon_a", width).eq_expr(int_min);
    let b_is_m1 = SmtExpr::var("recon_b", width).eq_expr(minus_one);
    a_is_min.and_expr(b_is_m1).not_expr()
}

/// Reconstruct a lowering [`ProofObligation`] for a reconstructable wasm scalar
/// instruction directly FROM THE REAL EMITTED OPCODE over fresh symbolic
/// value-stack operands (task #71). Stack-machine analogue of
/// `riscv_function_verifier::reconstruct_alu_obligation`.
///
/// Returns `None` (no credit) for any non-reconstructable opcode, any
/// unsupported operand width, or any opcode byte that does not decode to the
/// expected typed op via the `wasm_semantics` decoders (fail-closed: a malformed
/// or mis-typed instruction is NOT silently credited).
///
/// # What it does
///
/// 1. Resolves the INTENDED source op via the TYPED exhaustive
///    [`opcode_to_source_op`] (no string lookup).
/// 2. Binds fresh symbolic value-stack operands at the operand width — `recon_a`
///    (and `recon_b` for binary ops) — standing for the top-of-stack values the
///    op consumes, in stack order (deeper operand first).
/// 3. Builds `trust_ir_expr` from the INTENDED source op over the shared syms and
///    the machine side by DECODING the REAL emitted opcode byte
///    (`decode_int_binop`/`decode_int_cmp`/`decode_fp_binop`/...) and applying the
///    decoded op to the SAME syms, wired in stack order. A wrong opcode byte
///    decodes to a different op ⇒ structurally distinct ⇒ REFUTE; a swapped
///    non-commutative wiring ⇒ REFUTE.
/// 4. Tags the obligation [`MachineSideProvenance::Reconstructed`].
///
/// SHIFTS additionally carry a LOAD-BEARING `amount < width` precondition (#57);
/// DIV/REM carry the matching trap precondition(s).
pub fn reconstruct_alu_obligation(inst: &WasmISelInst) -> Option<ProofObligation> {
    let source_op = opcode_to_source_op(inst.opcode)?;
    let from_opcode = format!("{:?}", inst.opcode);
    let byte = inst.opcode.opcode_byte();

    match source_op {
        WasmSourceOp::IntBinary(op) => reconstruct_int_binary(inst, op, byte, from_opcode, false),
        WasmSourceOp::IntDivRem(op) => reconstruct_int_binary(inst, op, byte, from_opcode, true),
        WasmSourceOp::Bitwise(op) => reconstruct_bitwise(inst, op, byte, from_opcode),
        WasmSourceOp::Shift(op) => reconstruct_shift(inst, op, byte, from_opcode),
        WasmSourceOp::IntCompare(cc) => reconstruct_int_compare(inst, cc, byte, from_opcode),
        WasmSourceOp::FpBinary(op) => reconstruct_fp_binary(inst, op, byte, from_opcode),
        WasmSourceOp::FpUnary(op) => reconstruct_fp_unary(inst, op, byte, from_opcode),
        WasmSourceOp::FpCompare(cc) => reconstruct_fp_compare(inst, cc, byte, from_opcode),
        WasmSourceOp::IntCast(kind) => reconstruct_int_cast(inst, kind, byte, from_opcode),
        WasmSourceOp::FpFormatCast(kind) => {
            reconstruct_fp_format_cast(inst, kind, byte, from_opcode)
        }
        WasmSourceOp::Popcnt => reconstruct_popcnt(inst, byte, from_opcode),
        WasmSourceOp::Reinterpret => reconstruct_reinterpret(inst, byte, from_opcode),
        WasmSourceOp::Convert => reconstruct_convert(inst, byte, from_opcode),
        WasmSourceOp::TruncSat => reconstruct_trunc_sat(inst, from_opcode),
        WasmSourceOp::SimdIntLane(op) => reconstruct_simd_int_lane(inst, op, from_opcode),
        WasmSourceOp::SimdFpLane(op) => reconstruct_simd_fp_lane(inst, op, from_opcode),
    }
}

/// Reconstruct a LANE-WISE INTEGER v128 op (`i32x4.add`/`i32x4.mul`) over the full
/// 128-bit vector. The two stack operands are 128-bit vectors carried as two
/// 64-bit halves each (`recon_a_lo`/`recon_a_hi`, `recon_b_lo`/`recon_b_hi`),
/// concatenated. The machine side DECODES the real 0xfd SUB-opcode to the lane op
/// + lane shape and rebuilds the full-vector op; the source side is the trust-ir
///   scalar op `map_lanes`-applied at the SAME `i32x4` arrangement. A wrong sub-
///   opcode (mul-for-add) or wrong lane width (i16x8) diverges over the 128-bit
///   value ⇒ REFUTE.
fn reconstruct_simd_int_lane(
    inst: &WasmISelInst,
    op: trust_cg_lower::instructions::Opcode,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::smt::VectorArrangement;
    use crate::trust_ir_semantics::encode_trust_ir_lanewise_binop;
    use crate::wasm_semantics::{
        WasmSimdLaneOp, decode_simd_lane_op, encode_i32x4_add, encode_i32x4_mul,
    };

    // The real machine encoding is the (0xfd prefix, sub-opcode) pair; decode the
    // sub-opcode to the lane op + shape. A wrong sub-opcode decodes differently.
    let sub = inst.opcode.simd_sub_opcode()?;
    let decoded = decode_simd_lane_op(sub)?;

    // 128-bit operands as two 64-bit halves each (the env values are u64).
    let a = SmtExpr::var("recon_a_hi", 64).concat(SmtExpr::var("recon_a_lo", 64));
    let b = SmtExpr::var("recon_b_hi", 64).concat(SmtExpr::var("recon_b_lo", 64));

    let (machine_expr, arrangement) = match decoded {
        WasmSimdLaneOp::I32x4Add => (
            encode_i32x4_add(a.clone(), b.clone()),
            VectorArrangement::S4,
        ),
        WasmSimdLaneOp::I32x4Mul => (
            encode_i32x4_mul(a.clone(), b.clone()),
            VectorArrangement::S4,
        ),
        // FP lane sub-opcodes are not integer ops; fail closed here.
        WasmSimdLaneOp::F32x4Add | WasmSimdLaneOp::F32x4Mul => return None,
    };

    let trust_ir_expr = encode_trust_ir_lanewise_binop(&op, arrangement, a, b);

    Some(ProofObligation {
        name: format!("RECONSTRUCTED wasm {op:?}_i32x4 -> {from_opcode} (v128 lane-wise)"),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![
            ("recon_a_lo".to_string(), 64),
            ("recon_a_hi".to_string(), 64),
            ("recon_b_lo".to_string(), 64),
            ("recon_b_hi".to_string(), 64),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 2,
        },
    })
}

/// Reconstruct a LANE-WISE FP v128 op (`f32x4.add`/`f32x4.mul`). The packed op is
/// four independent identical binary32 ops, so one representative FP lane (FP-typed
/// `recon_a`/`recon_b`) witnesses the full-vector value equivalence (mirrors the
/// x86 packed-FP per-lane reconstruction). The machine side decodes the real 0xfd
/// sub-opcode to the lane op; the source side is the trust-ir scalar FP op at f32.
/// A wrong sub-opcode (mul-for-add) DIVERGES under the FP evaluator ⇒ REFUTE.
fn reconstruct_simd_fp_lane(
    inst: &WasmISelInst,
    op: trust_cg_lower::instructions::Opcode,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use crate::wasm_semantics::{
        WasmSimdLaneOp, decode_simd_lane_op, encode_f32x4_add_lane, encode_f32x4_mul_lane,
    };
    use trust_cg_lower::types::Type;

    let sub = inst.opcode.simd_sub_opcode()?;
    let decoded = decode_simd_lane_op(sub)?;

    // f32 lane: width 32, IEEE binary32 format (exponent 8, significand 24). The
    // operands are width-32 BV leaves interpreted as FP via `fp_inputs` (exactly
    // the existing scalar-FP reconstruction convention).
    let (eb, sb) = (8u32, 24u32);
    let a = SmtExpr::var("recon_a", 32);
    let b = SmtExpr::var("recon_b", 32);

    let machine_expr = match decoded {
        WasmSimdLaneOp::F32x4Add => encode_f32x4_add_lane(a.clone(), b.clone()),
        WasmSimdLaneOp::F32x4Mul => encode_f32x4_mul_lane(a.clone(), b.clone()),
        // Integer lane sub-opcodes are not FP ops; fail closed here.
        WasmSimdLaneOp::I32x4Add | WasmSimdLaneOp::I32x4Mul => return None,
    };

    let trust_ir_expr = encode_trust_ir_fp_binop(&op, Type::F32, a, b);

    Some(fp_binary_obligation(
        format!("RECONSTRUCTED wasm {op:?}_f32x4 -> {from_opcode} (v128 lane, f32)"),
        trust_ir_expr,
        machine_expr,
        eb,
        sb,
        from_opcode,
    ))
}

/// Build a binary-op `ProofObligation` from shared symbols.
fn binary_obligation(
    name: String,
    trust_ir_expr: SmtExpr,
    machine_expr: SmtExpr,
    width: u32,
    preconditions: Vec<SmtExpr>,
    from_opcode: String,
) -> ProofObligation {
    ProofObligation {
        name,
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![
            ("recon_a".to_string(), width),
            ("recon_b".to_string(), width),
        ],
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 2,
        },
    }
}

fn reconstruct_int_binary(
    inst: &WasmISelInst,
    op: trust_cg_lower::instructions::Opcode,
    byte: u8,
    from_opcode: String,
    divrem: bool,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use crate::wasm_semantics::{
        WasmAluOp, decode_int_binop, encode_add, encode_div_s, encode_div_u, encode_mul,
        encode_rem_s, encode_rem_u, encode_sub,
    };

    let width = inst.operand_width_bits;
    let ty = width_to_type(width)?;
    let a = SmtExpr::var("recon_a", width);
    let b = SmtExpr::var("recon_b", width);

    // Decode the REAL emitted opcode byte to the machine ALU op.
    let decoded = decode_int_binop(byte)?;
    let machine_expr = match decoded {
        WasmAluOp::Add => encode_add(a.clone(), b.clone()),
        WasmAluOp::Sub => encode_sub(a.clone(), b.clone()),
        WasmAluOp::Mul => encode_mul(a.clone(), b.clone()),
        WasmAluOp::DivS => encode_div_s(a.clone(), b.clone()),
        WasmAluOp::DivU => encode_div_u(a.clone(), b.clone()),
        WasmAluOp::RemS => encode_rem_s(a.clone(), b.clone()),
        WasmAluOp::RemU => encode_rem_u(a.clone(), b.clone()),
        // Shifts/bitwise are decoded by decode_int_binop too, but those source
        // ops route through the dedicated reconstructors; fail closed here.
        WasmAluOp::And
        | WasmAluOp::Or
        | WasmAluOp::Xor
        | WasmAluOp::Shl
        | WasmAluOp::ShrS
        | WasmAluOp::ShrU => return None,
    };

    let trust_ir_expr = encode_trust_ir_binop(&op, ty, a, b);

    let mut preconditions = vec![];
    if divrem {
        preconditions.push(nonzero(width));
        if matches!(op, trust_cg_lower::instructions::Opcode::Sdiv) {
            preconditions.push(no_sdiv_overflow(width));
        }
    }

    Some(binary_obligation(
        format!("RECONSTRUCTED wasm {op:?}_i{width} -> {from_opcode} (stack-operand)"),
        trust_ir_expr,
        machine_expr,
        width,
        preconditions,
        from_opcode,
    ))
}

fn reconstruct_bitwise(
    inst: &WasmISelInst,
    op: trust_cg_lower::instructions::Opcode,
    byte: u8,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use crate::wasm_semantics::{WasmAluOp, decode_int_binop, encode_and, encode_or, encode_xor};

    let width = inst.operand_width_bits;
    let ty = width_to_type(width)?;
    let a = SmtExpr::var("recon_a", width);
    let b = SmtExpr::var("recon_b", width);

    let decoded = decode_int_binop(byte)?;
    let machine_expr = match decoded {
        WasmAluOp::And => encode_and(a.clone(), b.clone()),
        WasmAluOp::Or => encode_or(a.clone(), b.clone()),
        WasmAluOp::Xor => encode_xor(a.clone(), b.clone()),
        _ => return None,
    };

    let trust_ir_expr = encode_trust_ir_bitwise_binop(&op, ty, a, b);

    Some(binary_obligation(
        format!("RECONSTRUCTED wasm {op:?}_i{width} -> {from_opcode} (stack-operand)"),
        trust_ir_expr,
        machine_expr,
        width,
        vec![],
        from_opcode,
    ))
}

fn reconstruct_shift(
    inst: &WasmISelInst,
    op: trust_cg_lower::instructions::Opcode,
    byte: u8,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_shift;
    use crate::wasm_semantics::{
        WasmAluOp, decode_int_binop, encode_shl, encode_shr_s, encode_shr_u,
    };

    let width = inst.operand_width_bits;
    let ty = width_to_type(width)?;
    let a = SmtExpr::var("recon_a", width);
    let b = SmtExpr::var("recon_b", width);

    let decoded = decode_int_binop(byte)?;
    // wasm shifts MASK the amount mod width; the trust-ir source side is the
    // plain (unmasked) shift, well-defined for amount < width. The masked machine
    // side equals it IN RANGE; out of range they DIVERGE — so the precondition is
    // load-bearing (#57): strip it and a shift by exactly `width` refutes.
    let machine_expr = match decoded {
        WasmAluOp::Shl => encode_shl(a.clone(), b.clone(), width),
        WasmAluOp::ShrS => encode_shr_s(a.clone(), b.clone(), width),
        WasmAluOp::ShrU => encode_shr_u(a.clone(), b.clone(), width),
        _ => return None,
    };

    let trust_ir_expr = encode_trust_ir_shift(&op, ty, a, b.clone());
    let precond = b.bvult(SmtExpr::bv_const(u64::from(width), width));

    Some(binary_obligation(
        format!("RECONSTRUCTED wasm {op:?}_i{width} -> {from_opcode} (stack-operand)"),
        trust_ir_expr,
        machine_expr,
        width,
        vec![precond],
        from_opcode,
    ))
}

fn reconstruct_int_compare(
    inst: &WasmISelInst,
    cc: trust_cg_lower::instructions::IntCC,
    byte: u8,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_icmp;
    use crate::wasm_semantics::{
        WasmIntCmpOp, decode_int_cmp, encode_eq, encode_ge_s, encode_ge_u, encode_gt_s,
        encode_gt_u, encode_le_s, encode_le_u, encode_lt_s, encode_lt_u, encode_ne,
    };

    let width = inst.operand_width_bits;
    let ty = width_to_type(width)?;
    let a = SmtExpr::var("recon_a", width);
    let b = SmtExpr::var("recon_b", width);

    let decoded = decode_int_cmp(byte)?;
    // wasm comparisons yield an i32 0/1. The machine side IS that i32 result.
    let machine_expr = match decoded {
        WasmIntCmpOp::Eq => encode_eq(a.clone(), b.clone()),
        WasmIntCmpOp::Ne => encode_ne(a.clone(), b.clone()),
        WasmIntCmpOp::LtS => encode_lt_s(a.clone(), b.clone()),
        WasmIntCmpOp::LtU => encode_lt_u(a.clone(), b.clone()),
        WasmIntCmpOp::GtS => encode_gt_s(a.clone(), b.clone()),
        WasmIntCmpOp::GtU => encode_gt_u(a.clone(), b.clone()),
        WasmIntCmpOp::LeS => encode_le_s(a.clone(), b.clone()),
        WasmIntCmpOp::LeU => encode_le_u(a.clone(), b.clone()),
        WasmIntCmpOp::GeS => encode_ge_s(a.clone(), b.clone()),
        WasmIntCmpOp::GeU => encode_ge_u(a.clone(), b.clone()),
    };

    // trust-ir icmp yields a 1-bit result; zero-extend to i32 to match wasm.
    let trust_ir_expr = encode_trust_ir_icmp(&cc, ty, a, b).zero_ext(31);

    Some(binary_obligation(
        format!("RECONSTRUCTED wasm Icmp_{cc:?}_i{width} -> {from_opcode} (stack-operand)"),
        trust_ir_expr,
        machine_expr,
        width,
        vec![],
        from_opcode,
    ))
}

/// Build a binary FP-op `ProofObligation` from shared FP-typed symbols.
fn fp_binary_obligation(
    name: String,
    trust_ir_expr: SmtExpr,
    machine_expr: SmtExpr,
    eb: u32,
    sb: u32,
    from_opcode: String,
) -> ProofObligation {
    ProofObligation {
        name,
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![
            ("recon_a".to_string(), eb, sb),
            ("recon_b".to_string(), eb, sb),
        ],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 2,
        },
    }
}

fn reconstruct_fp_binary(
    inst: &WasmISelInst,
    op: trust_cg_lower::instructions::Opcode,
    byte: u8,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;
    use crate::wasm_semantics::{
        WasmFpBinOp, decode_fp_binop, encode_fadd, encode_fdiv, encode_fmul, encode_fsub,
    };

    let width = inst.operand_width_bits;
    let (eb, sb) = fp_format_from_width(width)?;
    let ty = if width == 32 {
        trust_cg_lower::types::Type::F32
    } else {
        trust_cg_lower::types::Type::F64
    };
    let a = SmtExpr::var("recon_a", width);
    let b = SmtExpr::var("recon_b", width);

    let decoded = decode_fp_binop(byte)?;
    let machine_expr = match decoded {
        WasmFpBinOp::Add => encode_fadd(a.clone(), b.clone()),
        WasmFpBinOp::Sub => encode_fsub(a.clone(), b.clone()),
        WasmFpBinOp::Mul => encode_fmul(a.clone(), b.clone()),
        WasmFpBinOp::Div => encode_fdiv(a.clone(), b.clone()),
    };

    let trust_ir_expr = encode_trust_ir_fp_binop(&op, ty, a, b);

    Some(fp_binary_obligation(
        format!("RECONSTRUCTED wasm {op:?}_f{width} -> {from_opcode} (stack-operand)"),
        trust_ir_expr,
        machine_expr,
        eb,
        sb,
        from_opcode,
    ))
}

fn reconstruct_fp_unary(
    inst: &WasmISelInst,
    op: trust_cg_lower::instructions::Opcode,
    byte: u8,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::{
        encode_trust_ir_fceil, encode_trust_ir_ffloor, encode_trust_ir_ftrunc,
        try_encode_trust_ir_fp_unaryop,
    };
    use crate::wasm_semantics::{
        WasmFpUnOp, decode_fp_unop, encode_fabs, encode_fceil, encode_ffloor, encode_fneg,
        encode_fsqrt, encode_ftrunc,
    };
    use trust_cg_lower::instructions::Opcode;

    let width = inst.operand_width_bits;
    let (eb, sb) = fp_format_from_width(width)?;
    let ty = if width == 32 {
        trust_cg_lower::types::Type::F32
    } else {
        trust_cg_lower::types::Type::F64
    };
    let a = SmtExpr::var("recon_a", width);

    let decoded = decode_fp_unop(byte)?;
    let machine_expr = match decoded {
        WasmFpUnOp::Abs => encode_fabs(a.clone()),
        WasmFpUnOp::Neg => encode_fneg(a.clone()),
        WasmFpUnOp::Sqrt => encode_fsqrt(a.clone()),
        WasmFpUnOp::Ceil => encode_fceil(a.clone()),
        WasmFpUnOp::Floor => encode_ffloor(a.clone()),
        WasmFpUnOp::Trunc => encode_ftrunc(a.clone()),
    };

    // Source side: Fneg/Fabs/Fsqrt via the shared unaryop encoder; the
    // round-to-integral forms via their dedicated trust-ir encoders.
    let trust_ir_expr = match op {
        Opcode::Fneg | Opcode::Fabs | Opcode::Fsqrt => {
            try_encode_trust_ir_fp_unaryop(&op, ty, a.clone()).ok()?
        }
        Opcode::Fceil => encode_trust_ir_fceil(ty, a.clone()),
        Opcode::Ffloor => encode_trust_ir_ffloor(ty, a.clone()),
        Opcode::Ftrunc => encode_trust_ir_ftrunc(ty, a.clone()),
        _ => return None,
    };

    Some(ProofObligation {
        name: format!("RECONSTRUCTED wasm {op:?}_f{width} -> {from_opcode} (stack-operand)"),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("recon_a".to_string(), eb, sb)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 1,
        },
    })
}

fn reconstruct_fp_compare(
    inst: &WasmISelInst,
    cc: trust_cg_lower::instructions::FloatCC,
    byte: u8,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_fcmp;
    use crate::wasm_semantics::{WasmFpCmpOp, bool_to_i32, decode_fp_cmp};

    let width = inst.operand_width_bits;
    let (eb, sb) = fp_format_from_width(width)?;
    let ty = if width == 32 {
        trust_cg_lower::types::Type::F32
    } else {
        trust_cg_lower::types::Type::F64
    };
    let a = SmtExpr::var("recon_a", width);
    let b = SmtExpr::var("recon_b", width);

    // The machine side IS the wasm comparison's i32 0/1 result. wasm `eq/lt/gt/
    // le/ge` are ORDERED (false on NaN); `ne` is UNORDERED (true on NaN). We
    // build the wasm predicate directly from these primitives so a wrong compare
    // byte (decode mismatch) or wrong (NaN-)behaviour DIVERGES from the source.
    let decoded = decode_fp_cmp(byte)?;
    // wasm `eq/lt/gt/le/ge` are ORDERED (false if either operand is NaN — exactly
    // SMT-LIB `fp.eq/lt/gt/le/ge`), and wasm `ne` is the UNORDERED negated-eq
    // (true if either is NaN, i.e. `NOT fp.eq`). Built directly from these
    // primitives so a wrong compare byte (decode mismatch) or NaN-behaviour
    // mismatch DIVERGES from the trust-ir source predicate.
    let machine_pred = match decoded {
        WasmFpCmpOp::Eq => a.clone().fp_eq(b.clone()),
        WasmFpCmpOp::Ne => a.clone().fp_eq(b.clone()).not_expr(),
        WasmFpCmpOp::Lt => a.clone().fp_lt(b.clone()),
        WasmFpCmpOp::Gt => a.clone().fp_gt(b.clone()),
        WasmFpCmpOp::Le => a.clone().fp_le(b.clone()),
        WasmFpCmpOp::Ge => a.clone().fp_ge(b.clone()),
    };
    let machine_expr = bool_to_i32(machine_pred);

    // trust-ir fcmp yields a 1-bit result; zero-extend to i32 to match wasm.
    let trust_ir_expr = encode_trust_ir_fcmp(&cc, ty, a, b).zero_ext(31);

    Some(ProofObligation {
        name: format!("RECONSTRUCTED wasm Fcmp_{cc:?}_f{width} -> {from_opcode} (stack-operand)"),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![
            ("recon_a".to_string(), eb, sb),
            ("recon_b".to_string(), eb, sb),
        ],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 2,
        },
    })
}

fn reconstruct_int_cast(
    _inst: &WasmISelInst,
    kind: WasmIntCastKind,
    byte: u8,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::{encode_trust_ir_sextend, encode_trust_ir_uextend};
    use crate::wasm_semantics::{
        WasmIntCastOp, decode_int_cast, encode_sext_i32_i64, encode_wrap, encode_zext_i32_i64,
    };

    let decoded = decode_int_cast(byte)?;
    // The single SOURCE stack operand width is fixed by the cast kind.
    let (src_width, dst_width, src_name): (u32, u32, &str) = match kind {
        WasmIntCastKind::Wrap => (64, 32, "i64->i32"),
        WasmIntCastKind::SExt => (32, 64, "i32->i64s"),
        WasmIntCastKind::UExt => (32, 64, "i32->i64u"),
    };
    let a = SmtExpr::var("recon_a", src_width);

    let machine_expr = match decoded {
        WasmIntCastOp::WrapI64 => encode_wrap(a.clone()),
        WasmIntCastOp::ExtendI32S => encode_sext_i32_i64(a.clone()),
        WasmIntCastOp::ExtendI32U => encode_zext_i32_i64(a.clone()),
    };

    let trust_ir_expr = match kind {
        WasmIntCastKind::Wrap => a.clone().extract(31, 0),
        WasmIntCastKind::SExt => encode_trust_ir_sextend(src_width, dst_width, a.clone()),
        WasmIntCastKind::UExt => encode_trust_ir_uextend(src_width, dst_width, a.clone()),
    };

    Some(ProofObligation {
        name: format!("RECONSTRUCTED wasm cast {src_name} -> {from_opcode} (stack-operand)"),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![("recon_a".to_string(), src_width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 1,
        },
    })
}

fn reconstruct_fp_format_cast(
    _inst: &WasmISelInst,
    kind: WasmFpFormatKind,
    byte: u8,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_fp_format_convert;
    use crate::wasm_semantics::{WasmFpFormatCastOp, decode_fp_format_cast};

    let decoded = decode_fp_format_cast(byte)?;
    // Source/destination FP format fixed by the cast direction.
    let (src_w, dst_eb, dst_sb): (u32, u32, u32) = match kind {
        WasmFpFormatKind::Demote => (64, 8, 24),   // f64 -> f32
        WasmFpFormatKind::Promote => (32, 11, 53), // f32 -> f64
    };
    let (src_eb, src_sb) = fp_format_from_width(src_w)?;
    let a = SmtExpr::var("recon_a", src_w);

    // Machine side: the wasm format cast — built to the destination format. A
    // wrong direction byte decodes to the other variant ⇒ different dest format
    // ⇒ structurally distinct ⇒ REFUTE.
    let machine_expr = match decoded {
        WasmFpFormatCastOp::DemoteF64 => {
            SmtExpr::fp_to_fp(crate::smt::RoundingMode::RNE, a.clone(), 8, 24)
        }
        WasmFpFormatCastOp::PromoteF32 => {
            SmtExpr::fp_to_fp(crate::smt::RoundingMode::RNE, a.clone(), 11, 53)
        }
    };

    // Source side: the trust-ir FP-format convert to the SAME destination format.
    let trust_ir_expr = encode_trust_ir_fp_format_convert(dst_eb, dst_sb, a.clone());

    Some(ProofObligation {
        name: format!("RECONSTRUCTED wasm fp-format-cast -> {from_opcode} (stack-operand)"),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("recon_a".to_string(), src_eb, src_sb)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 1,
        },
    })
}

/// Reconstruct an `i32.popcnt`/`i64.popcnt` (population count). The single SOURCE
/// stack operand is a BV leaf (`recon_a`) at the operand width; the machine side
/// DECODES the real opcode byte to a popcnt width and rebuilds the bit-count via
/// `wasm_semantics::encode_popcnt`; the source side is the trust-ir `Ctpop`
/// reference (`encode_trust_ir_ctpop`). A byte that does NOT decode to popcnt
/// fails closed (no credit); a popcnt-for-other-bitop machine encoder diverges
/// from `Ctpop` for almost every input ⇒ REFUTE. The bit-count is FAITHFULLY
/// modeled (pure bitvector) by the native evaluator.
fn reconstruct_popcnt(
    inst: &WasmISelInst,
    byte: u8,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_ctpop;
    use crate::wasm_semantics::{WasmPopcntOp, decode_popcnt, encode_popcnt};

    // Decode the REAL emitted opcode byte to the popcnt width; a non-popcnt byte
    // fails closed (no credit).
    let decoded_width = match decode_popcnt(byte)? {
        WasmPopcntOp::I32 => 32,
        WasmPopcntOp::I64 => 64,
    };
    // The decoded width must match the operand width this instruction operates at
    // (the opcode fixes both); a mismatch fails closed.
    let width = inst.operand_width_bits;
    if decoded_width != width {
        return None;
    }
    let a = SmtExpr::var("recon_a", width);

    let machine_expr = encode_popcnt(a.clone());
    let trust_ir_expr = encode_trust_ir_ctpop(a.clone());

    Some(ProofObligation {
        name: format!("RECONSTRUCTED wasm Ctpop_i{width} -> {from_opcode} (stack-operand)"),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![("recon_a".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 1,
        },
    })
}

/// Reconstruct a bit-reinterpret (`iN.reinterpret_fN` / `fN.reinterpret_iN`). A
/// pure, width-preserving bit copy: the operand bits ARE the result bits, so both
/// the trust-ir source (`encode_trust_ir_bitcast`, the identity) and the machine
/// side (`wasm_semantics::encode_reinterpret`, also the identity) operate over the
/// SAME `recon_a` bitvector at the width DECODED from the real opcode byte.
///
/// The reconstruction content is the WIDTH (like x86's cross-domain `MovdToXmm`/
/// `MovdFromXmm` "preserves bits"): a wrong-WIDTH reinterpret byte (e.g.
/// `i64.reinterpret_f64` 0xbd where `i32.reinterpret_f32` 0xbc was intended)
/// decodes to a 64-bit width, which mismatches the 32-bit operand width this
/// instruction operates at ⇒ FAIL CLOSED (no credit) ⇒ REFUTE. A byte that does
/// not decode to a reinterpret at all also fails closed. Within a width both
/// directions are genuinely bit-identity, so a same-width direction swap is itself
/// a correct no-op bit copy (the width is the discriminator).
fn reconstruct_reinterpret(
    inst: &WasmISelInst,
    byte: u8,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::encode_trust_ir_bitcast;
    use crate::wasm_semantics::{decode_reinterpret, encode_reinterpret};
    use trust_cg_lower::types::Type;

    // Decode the REAL emitted opcode byte to the reinterpret width; a non-
    // reinterpret byte fails closed.
    let decoded = decode_reinterpret(byte)?;
    let width = decoded.width();
    // The decoded width must match the operand width this instruction operates at
    // (the opcode fixes the width); a wrong-width byte fails closed ⇒ REFUTE.
    if width != inst.operand_width_bits {
        return None;
    }
    let a = SmtExpr::var("recon_a", width);

    // Machine side: the wasm bit-reinterpret (identity on the operand bitvector).
    let machine_expr = encode_reinterpret(a.clone());
    // Source side: the trust-ir Bitcast (also the identity). The trust-ir
    // bitcast's from/to types carry no SMT content (it is the identity at the
    // bitvector level); descriptors at the decoded width suffice.
    let ty = if width == 32 { Type::I32 } else { Type::I64 };
    let trust_ir_expr = encode_trust_ir_bitcast(ty.clone(), ty, a.clone());

    Some(ProofObligation {
        name: format!("RECONSTRUCTED wasm Bitcast_w{width} -> {from_opcode} (stack-operand)"),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![("recon_a".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 1,
        },
    })
}

/// Reconstruct an int->FP CONVERT (`f{32,64}.convert_i{32,64}_{s,u}`). The single
/// SOURCE stack operand is an integer bitvector (`recon_src`); the machine side
/// DECODES the real opcode byte to (src_width, fp_width, signed) and rebuilds the
/// convert via the wasm `encode_convert_s`/`_u`; the source side is the trust-ir
/// `encode_trust_ir_fcvt_from_sint`/`_uint` at the SAME signedness.
///
/// FAITHFULNESS: the evaluator now models the SOURCE SIGNEDNESS — `BvToFP`
/// interprets its operand as a signed bitvector, and the `_u` path zero-extends
/// first to give the correct unsigned magnitude. A signed-for-unsigned lowering
/// feeds a different operand magnitude ⇒ a different f64 ⇒ REFUTE for a high-bit-
/// set input. A wrong width byte fails closed (operand-width mismatch).
fn reconstruct_convert(
    inst: &WasmISelInst,
    byte: u8,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::{
        encode_trust_ir_fcvt_from_sint, encode_trust_ir_fcvt_from_uint,
    };
    use crate::wasm_semantics::{decode_convert, encode_convert_s, encode_convert_u};

    // Decode the REAL emitted opcode byte; a non-convert byte fails closed.
    let decoded = decode_convert(byte)?;
    // The decoded source integer width must match the consumed stack operand width
    // (the opcode fixes both); a mismatch fails closed.
    if decoded.src_width != inst.operand_width_bits {
        return None;
    }
    let (eb, sb) = fp_format_from_width(decoded.fp_width)?;
    let src = SmtExpr::var("recon_src", decoded.src_width);

    // Machine side: the wasm signed/unsigned int->FP convert.
    let machine_expr = if decoded.signed {
        encode_convert_s(src.clone(), decoded.fp_width)
    } else {
        encode_convert_u(src.clone(), decoded.src_width, decoded.fp_width)
    };
    // Source side: the trust-ir convert at the SAME signedness.
    let trust_ir_expr = if decoded.signed {
        encode_trust_ir_fcvt_from_sint(eb, sb, src.clone())
    } else {
        encode_trust_ir_fcvt_from_uint(eb, sb, src.clone(), decoded.src_width)
    };

    let sign = if decoded.signed { "s" } else { "u" };
    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED wasm FcvtFromInt_f{}_i{}_{sign} -> {from_opcode} (stack-operand)",
            decoded.fp_width, decoded.src_width
        ),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        // The source is an integer BITVECTOR leaf (verified by the BV evaluator).
        inputs: vec![("recon_src".to_string(), decoded.src_width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 1,
        },
    })
}

/// Reconstruct a SATURATING FP->int TRUNC (`i{32,64}.trunc_sat_f{32,64}_{s,u}`,
/// 0xfc prefix). The single SOURCE stack operand is an FP leaf (`recon_a`); the
/// machine side DECODES the (0xfc prefix, sub-index) to (fp_width, int_width,
/// signed) and rebuilds the SATURATING truncation via the wasm `encode_trunc_sat_s`/
/// `_u`; the source side is the trust-ir `encode_trust_ir_fcvt_to_sint`/`_uint`.
///
/// FAITHFULNESS: the evaluator now SATURATES to the int range and maps NaN->0, so
/// a wrapping (mask-only) machine DIVERGES for an out-of-range input, and a
/// signed-for-unsigned sub-index DIVERGES too ⇒ REFUTE. The sub-index comes from
/// the REAL opcode (`WasmOpcode::trunc_sat_sub_opcode`), so the (prefix, sub-index)
/// pair is the complete machine encoding.
fn reconstruct_trunc_sat(inst: &WasmISelInst, from_opcode: String) -> Option<ProofObligation> {
    use crate::trust_ir_semantics::{encode_trust_ir_fcvt_to_sint, encode_trust_ir_fcvt_to_uint};
    use crate::wasm_semantics::{decode_trunc_sat, encode_trunc_sat_s, encode_trunc_sat_u};

    // Decode the REAL emitted (0xfc prefix, sub-index) pair; anything else fails
    // closed. The sub-index distinguishes the 8 saturating forms.
    let prefix = inst.opcode.opcode_byte();
    let sub = inst.opcode.trunc_sat_sub_opcode()?;
    let decoded = decode_trunc_sat(prefix, sub)?;
    // The decoded source FP width must match the consumed stack operand width.
    if decoded.fp_width != inst.operand_width_bits {
        return None;
    }
    let (eb, sb) = fp_format_from_width(decoded.fp_width)?;
    let a = SmtExpr::var("recon_a", decoded.fp_width);

    // Machine side: the wasm saturating FP->int truncation.
    let machine_expr = if decoded.signed {
        encode_trunc_sat_s(a.clone(), decoded.int_width)
    } else {
        encode_trunc_sat_u(a.clone(), decoded.int_width)
    };
    // Source side: the trust-ir FP->int convert (round-toward-zero, saturating +
    // NaN->0 under the faithful evaluator) at the SAME signedness.
    let trust_ir_expr = if decoded.signed {
        encode_trust_ir_fcvt_to_sint(decoded.int_width, a.clone())
    } else {
        encode_trust_ir_fcvt_to_uint(decoded.int_width, a.clone())
    };

    let sign = if decoded.signed { "s" } else { "u" };
    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED wasm TruncSat_i{}_f{}_{sign} -> {from_opcode} (stack-operand)",
            decoded.int_width, decoded.fp_width
        ),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs: vec![],
        // The source is an FP leaf (verified by the reconstruction FP evaluator,
        // which substitutes the IEEE-754 edge-case battery — including out-of-range
        // and NaN — into both sides).
        fp_inputs: vec![("recon_a".to_string(), eb, sb)],
        preconditions: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: 1,
        },
    })
}

/// Build a REPRESENTATIVE [`WasmISelInst`] for a reconstructable wasm opcode at a
/// canonical operand width (the gate has only an opcode, so it synthesizes a
/// representative instance and credits the opcode COVERED iff the reconstructed
/// obligation discharges `Valid`). Returns `None` for any non-reconstructable
/// opcode. Mirrors `riscv_function_verifier::representative_reconstructable_inst`.
///
/// The canonical width is fixed per opcode (i32/f32 ops -> 32; i64/f64 ops -> 64;
/// casts -> the source operand width). Since reconstruction is width-uniform for
/// each opcode (the opcode itself fixes whether it is the 32- or 64-bit form),
/// one representative instance witnesses the opcode's value equivalence.
pub fn representative_reconstructable_inst(opcode: WasmOpcode) -> Option<WasmISelInst> {
    opcode_to_source_op(opcode)?;
    let width = representative_operand_width(opcode);
    Some(WasmISelInst::new(opcode, width))
}

/// The canonical value-stack operand width for a reconstructable wasm opcode.
fn representative_operand_width(opcode: WasmOpcode) -> u32 {
    use WasmOpcode as O;
    match opcode {
        // 64-bit-operand integer/FP forms.
        O::I64Add
        | O::I64Sub
        | O::I64Mul
        | O::I64DivS
        | O::I64DivU
        | O::I64RemS
        | O::I64RemU
        | O::I64And
        | O::I64Or
        | O::I64Xor
        | O::I64Shl
        | O::I64ShrS
        | O::I64ShrU
        | O::I64Eq
        | O::I64Ne
        | O::I64LtS
        | O::I64LtU
        | O::I64GtS
        | O::I64GtU
        | O::I64LeS
        | O::I64LeU
        | O::I64GeS
        | O::I64GeU
        | O::F64Add
        | O::F64Sub
        | O::F64Mul
        | O::F64Div
        | O::F64Abs
        | O::F64Neg
        | O::F64Sqrt
        | O::F64Ceil
        | O::F64Floor
        | O::F64Trunc
        | O::F64Eq
        | O::F64Ne
        | O::F64Lt
        | O::F64Gt
        | O::F64Le
        | O::F64Ge => 64,
        // 64-bit popcnt / reinterpret operate on a 64-bit operand.
        O::I64Popcnt | O::I64ReinterpretF64 | O::F64ReinterpretI64 => 64,
        // i32.wrap_i64 consumes a 64-bit source operand.
        O::I32WrapI64 => 64,
        // f32.demote_f64 consumes a 64-bit (f64) source operand.
        O::F32DemoteF64 => 64,
        // int->FP CONVERT: the consumed stack operand is the INTEGER source, so its
        // width is the source integer width (i32 forms -> 32, i64 forms -> 64).
        O::F32ConvertI64S | O::F32ConvertI64U | O::F64ConvertI64S | O::F64ConvertI64U => 64,
        O::F32ConvertI32S | O::F32ConvertI32U | O::F64ConvertI32S | O::F64ConvertI32U => 32,
        // SATURATING FP->int TRUNC: the consumed stack operand is the FP source, so
        // its width is the source FP width (..._f64_.. -> 64, ..._f32_.. -> 32).
        O::I32TruncSatF64S | O::I32TruncSatF64U | O::I64TruncSatF64S | O::I64TruncSatF64U => 64,
        O::I32TruncSatF32S | O::I32TruncSatF32U | O::I64TruncSatF32S | O::I64TruncSatF32U => 32,
        // Everything else reconstructable is a 32-bit-operand form (i32/f32; the
        // i64.extend_i32_* / f64.promote_f32 casts consume a 32-bit source).
        _ => 32,
    }
}

/// Does a representative reconstructed obligation for `opcode` discharge `Valid`
/// under `config`? The coverage-gate credit hook (mirrors
/// `riscv_function_verifier::reconstruction_discharges_valid`).
///
/// Returns `false` (NOT covered) for any opcode that is not reconstructable, has
/// no representative instance, fails to reconstruct, is not tagged Reconstructed,
/// or whose reconstructed obligation does not discharge `Valid`.
pub fn reconstruction_discharges_valid(opcode: WasmOpcode, config: &VerificationConfig) -> bool {
    let Some(inst) = representative_reconstructable_inst(opcode) else {
        return false;
    };
    let Some(obligation) = reconstruct_alu_obligation(&inst) else {
        return false;
    };
    if !obligation.is_reconstructed() {
        return false;
    }
    matches!(
        verify_by_evaluation_with_config(&obligation, config),
        VerificationResult::Valid
    )
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn cfg() -> VerificationConfig {
        VerificationConfig::default()
    }

    /// Every reconstructable scalar opcode discharges Valid via its representative
    /// instance (the honest credit basis the gate uses).
    #[test]
    fn representative_reconstructions_discharge_valid() {
        let cfg = cfg();
        // A representative slice across families.
        for op in [
            WasmOpcode::I32Add,
            WasmOpcode::I64Sub,
            WasmOpcode::I32Mul,
            WasmOpcode::I32DivS,
            WasmOpcode::I32DivU,
            WasmOpcode::I32RemS,
            WasmOpcode::I64And,
            WasmOpcode::I32Or,
            WasmOpcode::I32Xor,
            WasmOpcode::I32Shl,
            WasmOpcode::I32ShrS,
            WasmOpcode::I32ShrU,
            WasmOpcode::I32Eq,
            WasmOpcode::I32LtS,
            WasmOpcode::I64GtU,
            WasmOpcode::F32Add,
            WasmOpcode::F64Mul,
            WasmOpcode::F32Neg,
            WasmOpcode::F64Sqrt,
            WasmOpcode::F32Eq,
            WasmOpcode::F64Lt,
            WasmOpcode::I32WrapI64,
            WasmOpcode::I64ExtendI32S,
            WasmOpcode::I64ExtendI32U,
            WasmOpcode::F32DemoteF64,
            WasmOpcode::F64PromoteF32,
            // v128 lane-wise value ops.
            WasmOpcode::I32x4Add,
            WasmOpcode::I32x4Mul,
            WasmOpcode::F32x4Add,
            WasmOpcode::F32x4Mul,
        ] {
            assert!(
                reconstruction_discharges_valid(op, &cfg),
                "{op:?} representative reconstruction must discharge Valid"
            );
        }
    }

    /// Structural opcodes are NOT reconstructable (no value-equivalence credit).
    #[test]
    fn structural_opcodes_are_not_reconstructable() {
        for op in [
            WasmOpcode::Block,
            WasmOpcode::Loop,
            WasmOpcode::Br,
            WasmOpcode::If,
            WasmOpcode::I32Load,
            WasmOpcode::I32Store,
            WasmOpcode::LocalGet,
            WasmOpcode::LocalSet,
            WasmOpcode::Call,
            WasmOpcode::CallIndirect,
            WasmOpcode::I32Const,
            // Structural v128 forms: memory (load/store) + materialization (const).
            WasmOpcode::V128Load,
            WasmOpcode::V128Store,
            WasmOpcode::V128Const,
        ] {
            assert!(
                representative_reconstructable_inst(op).is_none(),
                "{op:?} must NOT be reconstructable"
            );
            assert!(!reconstruction_discharges_valid(op, &cfg()));
        }
    }
}
