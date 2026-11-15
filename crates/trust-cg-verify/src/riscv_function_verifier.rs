// trust-cg-verify/riscv_function_verifier.rs - RISC-V (RV64) function-level verification
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Provides verify_riscv_function(): given a RiscVISelFunction, walk every
// instruction, discharge the obligation reconstructed from that instruction's
// opcode and operands, and produce a FunctionVerificationReport with
// per-instruction results. Registry theorems selected by name are never
// instruction credit.
//
// Mirror of [`crate::x86_64_function_verifier`]. The three paths (AArch64,
// x86-64, RISC-V) share the same [`InstructionVerificationResult`] cert shape
// so downstream proof-certificate emission stays target-agnostic.
//
// # Why the ISel types are defined HERE (not imported from codegen)
//
// The x86-64 verifier imports `X86ISelFunction` from `trust-cg-lower`, which
// `trust-cg-verify` depends on. The RISC-V ISel types (`RiscVISelFunction`,
// `RiscVISelInst`) live in `trust-cg-codegen::riscv::pipeline`, and
// `trust-cg-codegen` ALREADY depends on `trust-cg-verify` — so a verify->codegen
// dependency would be a build CYCLE. The verifier therefore carries its own
// self-contained, minimal RISC-V ISel function/instruction shape (opcode +
// operands). `trust-cg-codegen` (which has both crates) converts its
// `RiscVISelFunction` into this type at the verification call site — exactly the
// dependency direction the workspace already permits.

//! RISC-V (RV64) function-level verification pipeline.
//!
//! [`verify_riscv_function`] walks a [`RiscVISelFunction`] and credits an
//! instruction only with an obligation reconstructed from its emitted opcode
//! and operands and discharged completely; a sampled discharge is reported but
//! never credited. There is no registry-name arm on this backend:
//! [`RiscVFunctionVerifier::opcode_to_proof_query`] has named no theorem for any
//! opcode since the #62 retraction. Produces a
//! [`FunctionVerificationReport`] (shared with the AArch64 / x86-64 paths) so
//! the public proof-certificate API stays target-agnostic.

use trust_cg_ir::{RegClass, RiscVOpcode, VReg};

use crate::function_verifier::{
    FunctionVerificationReport, InstructionOpcode, InstructionReport, InstructionVerificationResult,
};
use crate::lowering_proof::{
    MachineSideProvenance, ProofObligation, VerificationConfig, verify_by_evaluation_with_config,
};
use crate::proof_database::ProofCategory;
use crate::riscv_semantics::RiscVOperandSize;
use crate::smt::SmtExpr;
use crate::verify::{VerificationResult, VerificationStrength};

// ---------------------------------------------------------------------------
// Minimal RISC-V ISel function/instruction shape (see module note on the cycle)
// ---------------------------------------------------------------------------

/// An operand of a verifier-side RISC-V ISel instruction.
///
/// Minimal mirror of `trust_cg_codegen::riscv::pipeline::RiscVISelOperand`,
/// carrying exactly what operand reconstruction (task #63, RISC-V) reads
/// positionally: a register source (always RV64 width here) or an integer
/// immediate. Branch targets, symbols and stack slots never reach a
/// reconstructable ALU opcode, so they are intentionally absent (a malformed
/// shape simply fails the reconstruction CLOSED — it is not silently credited).
#[derive(Debug, Clone, PartialEq)]
pub enum RiscVISelOperand {
    /// A virtual register (RV64 `x`-register; 64-bit value sort).
    VReg(VReg),
    /// An integer immediate (the I-type `imm12` value role, or a shift `shamt`).
    Imm(i64),
}

/// A single RISC-V ISel instruction as seen by the verifier: opcode + the
/// positional operands operand reconstruction reads. Parallel to
/// `trust_cg_codegen::riscv::pipeline::RiscVISelInst`.
///
/// The operands carry the typed positional schema reconstruction binds against
/// (`[rd, rs1, rs2]` for R-type, `[rd, rs1, imm]` for I-type). The opcode-level
/// DB-substring walk (the legacy non-reconstructed path) ignores them.
#[derive(Debug, Clone)]
pub struct RiscVISelInst {
    /// The RISC-V opcode of this instruction.
    pub opcode: RiscVOpcode,
    /// Positional operands `[rd, rs1, rs2|imm]` (empty for opcode-only stubs).
    pub operands: Vec<RiscVISelOperand>,
}

impl RiscVISelInst {
    /// Construct an opcode-only verifier-side RISC-V ISel instruction.
    ///
    /// Operand reconstruction (which reads operands positionally) will return
    /// `None` for such a stub — it falls back to the DB-substring path. Use
    /// [`Self::with_operands`] to build a reconstructable instruction.
    pub fn new(opcode: RiscVOpcode) -> Self {
        Self {
            opcode,
            operands: Vec::new(),
        }
    }

    /// Construct a verifier-side RISC-V ISel instruction with positional operands.
    pub fn with_operands(opcode: RiscVOpcode, operands: Vec<RiscVISelOperand>) -> Self {
        Self { opcode, operands }
    }
}

/// A RISC-V ISel function as seen by the verifier: an ordered instruction
/// stream. Parallel to `trust_cg_codegen::riscv::pipeline::RiscVISelFunction`;
/// `trust-cg-codegen` converts its richer type into this one at the call site.
#[derive(Debug, Clone)]
pub struct RiscVISelFunction {
    /// Function name (carried through into the report).
    pub name: String,
    /// Instructions in deterministic emission order.
    pub insts: Vec<RiscVISelInst>,
}

impl RiscVISelFunction {
    /// Construct an empty verifier-side RISC-V ISel function.
    pub fn new(name: String) -> Self {
        Self {
            name,
            insts: Vec::new(),
        }
    }

    /// Append an instruction (by opcode) to the function's stream.
    pub fn push_opcode(&mut self, opcode: RiscVOpcode) {
        self.insts.push(RiscVISelInst::new(opcode));
    }
}

// ===========================================================================
// Phase-2 operand reconstruction (RISC-V ALU) — task #63 (mirror of AArch64)
// ===========================================================================
//
// The static RISC-V ALU lowering proofs (riscv_lowering_proofs.rs) build BOTH
// sides of an obligation from the SAME symbolic vars (proof "riscv: Iadd_I64 ->
// ADD": trust_ir = encode_trust_ir_binop(Iadd) = a.bvadd(b); the "machine" side
// is the SAME a.bvadd(b)). Those are STRUCTURALLY equal X==X, so the strict gate
// (#61) correctly counts them ZERO — a wrong isel opcode could never refute them.
// RISC-V emittable coverage is therefore honestly 0 under the strict gate.
//
// This RECONSTRUCTS the machine side FROM THE REAL EMITTED INSTRUCTION at verify
// time, EXACTLY mirroring the proven AArch64 pattern
// (`function_verifier::reconstruct_alu_obligation`). The source side is built
// from the INTENDED source op over shared symbols; the machine side is built from
// the REAL opcode's RISC-V semantics encoder wired to the REAL positional
// operands. The two agree IFF isel emitted a semantically correct instruction. If
// isel emitted SUB for an Iadd, the machine side is bvsub and the source side is
// bvadd => REFUTE. A non-commutative op (SUB/shifts/SLT) wired with swapped
// inputs => REFUTE. THAT is the content the credit rule counts.
//
// ANTI-f81e45b: this path performs NO `name.contains` lookup. The opcode->source
// binding is a TYPED, EXHAUSTIVE match ([`opcode_to_source_op`]); the operand
// binding uses a TYPED per-opcode positional schema. Asserted by
// `tests/reconstruction_riscv.rs`.
//
// TCB note (identical to AArch64): the "intended source op" binding stays TRUSTED
// (we trust that isel intended `Iadd` when it emitted `Add`). This SHRINKS the
// TCB (operand wiring + machine semantics are now checked against the real
// instruction) without ELIMINATING it; the wiring is the soundness crux, which is
// why the inject-wrong-wiring refutation tests exist.

/// SOURCE operand-schema arity of a reconstructed RISC-V ALU instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RiscVAluArity {
    /// `[rd, rs1, rs2]` / `[rd, rs1, imm]` — two value-producing source slots.
    Binary,
}

impl RiscVAluArity {
    fn as_u8(self) -> u8 {
        match self {
            RiscVAluArity::Binary => 2,
        }
    }
}

/// The intended trust_ir SOURCE op family for a reconstructable RISC-V opcode,
/// resolved by a TYPED EXHAUSTIVE match (NOT a string lookup). Mirrors
/// `function_verifier::SourceOp`.
#[derive(Debug, Clone, PartialEq)]
enum RiscVSourceOp {
    /// Binary arithmetic (`encode_trust_ir_binop`): Iadd/Isub/Imul. Machine side
    /// is the matching RISC-V ADD/SUB/MUL encoder.
    Binary(trust_cg_lower::instructions::Opcode),
    /// Binary bitwise (`encode_trust_ir_bitwise_binop`): Band/Bor/Bxor. Machine
    /// side is the RISC-V AND/OR/XOR encoder.
    Bitwise(trust_cg_lower::instructions::Opcode),
    /// Binary shift (`encode_trust_ir_shift`): Ishl/Ushr/Sshr. Machine side is the
    /// FAITHFUL (amount-masked) RISC-V SLL/SRL/SRA encoder, paired with a
    /// LOAD-BEARING `amount < width` precondition (#57). Covers both the
    /// register-amount (Sll/Srl/Sra) and immediate-amount (Slli/Srli) forms.
    Shift(trust_cg_lower::instructions::Opcode),
    /// Integer comparison value op (`encode_trust_ir_icmp`): SLT (signed-lt) /
    /// SLTU (unsigned-lt). Result is the 1-bit comparison bit. Machine side is the
    /// RISC-V SLT/SLTU encoder.
    Compare(trust_cg_lower::instructions::IntCC),
}

/// Resolve the INTENDED trust_ir source op + operand schema for a reconstructable
/// RISC-V opcode via a TYPED, EXHAUSTIVE match — NOT a string lookup
/// (anti-f81e45b). Mirrors `function_verifier::opcode_to_source_op`.
///
/// Reconstructable set (the 14 emittable ALU/shift/compare opcodes):
/// - ALU:     `Add`->Iadd, `Sub`->Isub, `Mul`->Imul, `Addi`->Iadd (imm)
/// - BITWISE: `And`->Band, `Or`->Bor, `Xor`->Bxor
/// - SHIFTS:  `Sll`->Ishl, `Srl`->Ushr, `Sra`->Sshr (register amount);
///   `Slli`->Ishl, `Srli`->Ushr (immediate amount)
/// - COMPARE: `Slt`->Icmp(SignedLessThan), `Sltu`->Icmp(UnsignedLessThan)
///
/// Returns `None` for every NON-reconstructable opcode, so the caller leaves
/// those on their existing path unchanged. Wildcard-free over the reconstructable
/// arms; falls through to `None` for the rest.
fn opcode_to_source_op(opcode: RiscVOpcode) -> Option<(RiscVSourceOp, RiscVAluArity)> {
    use RiscVOpcode as O;
    use trust_cg_lower::instructions::{IntCC, Opcode};
    match opcode {
        // ---- Integer ALU ----
        O::Add => Some((RiscVSourceOp::Binary(Opcode::Iadd), RiscVAluArity::Binary)),
        O::Sub => Some((RiscVSourceOp::Binary(Opcode::Isub), RiscVAluArity::Binary)),
        O::Mul => Some((RiscVSourceOp::Binary(Opcode::Imul), RiscVAluArity::Binary)),
        // ADDI value role: `rd = rs1 + sext(imm)`. Its structural roles (LI/MV/
        // StructGep) are instances of this same `rs1 + imm` dataflow.
        O::Addi => Some((RiscVSourceOp::Binary(Opcode::Iadd), RiscVAluArity::Binary)),

        // ---- Bitwise (commutative) ----
        O::And => Some((RiscVSourceOp::Bitwise(Opcode::Band), RiscVAluArity::Binary)),
        O::Or => Some((RiscVSourceOp::Bitwise(Opcode::Bor), RiscVAluArity::Binary)),
        O::Xor => Some((RiscVSourceOp::Bitwise(Opcode::Bxor), RiscVAluArity::Binary)),

        // ---- Shifts (register amount) — load-bearing amount<width precond ----
        O::Sll => Some((RiscVSourceOp::Shift(Opcode::Ishl), RiscVAluArity::Binary)),
        O::Srl => Some((RiscVSourceOp::Shift(Opcode::Ushr), RiscVAluArity::Binary)),
        O::Sra => Some((RiscVSourceOp::Shift(Opcode::Sshr), RiscVAluArity::Binary)),
        // ---- Shifts (immediate amount) ----
        O::Slli => Some((RiscVSourceOp::Shift(Opcode::Ishl), RiscVAluArity::Binary)),
        O::Srli => Some((RiscVSourceOp::Shift(Opcode::Ushr), RiscVAluArity::Binary)),

        // ---- Comparisons (non-commutative value ops) ----
        O::Slt => Some((
            RiscVSourceOp::Compare(IntCC::SignedLessThan),
            RiscVAluArity::Binary,
        )),
        O::Sltu => Some((
            RiscVSourceOp::Compare(IntCC::UnsignedLessThan),
            RiscVAluArity::Binary,
        )),

        // All non-reconstructable opcodes keep their existing DB-substring path.
        _ => None,
    }
}

/// Width in bits of a register operand. RV64 `x`-registers are 64-bit; the
/// `RegClass` carries the value sort (the representative i8 path uses a narrow
/// class in the test only). Returns `None` for a non-register operand.
fn operand_reg_width_bits(op: &RiscVISelOperand) -> Option<u32> {
    match op {
        RiscVISelOperand::VReg(v) => Some(v.class.size_bits()),
        RiscVISelOperand::Imm(_) => None,
    }
}

/// Map a width in bits to a [`RiscVOperandSize`] (informational; width is carried
/// by the [`SmtExpr`] sorts). Anything other than 32/64 is treated as S64-domain
/// for labeling — the actual encoders read the operand width, so this is purely a
/// descriptor.
fn width_to_operand_size(width: u32) -> RiscVOperandSize {
    match width {
        32 => RiscVOperandSize::S32,
        _ => RiscVOperandSize::S64,
    }
}

/// Map a width in bits to a trust_ir [`Type`]. The trust_ir ALU/bitwise/shift/
/// icmp encoders this module uses carry width in the operand `SmtExpr` sorts and
/// ignore the `Type` parameter (it is `_ty`), so this is a faithful descriptor.
/// `None` for an unsupported width (fails the reconstruction closed).
fn width_to_type(width: u32) -> Option<trust_cg_lower::types::Type> {
    use trust_cg_lower::types::Type;
    match width {
        8 => Some(Type::I8),
        16 => Some(Type::I16),
        32 => Some(Type::I32),
        64 => Some(Type::I64),
        _ => None,
    }
}

/// Reconstruct a lowering [`ProofObligation`] for a reconstructable RISC-V
/// instruction directly FROM THE REAL EMITTED INSTRUCTION (task #63, RISC-V).
/// Mirrors `function_verifier::reconstruct_alu_obligation`.
///
/// Returns `None` (caller falls back to the existing path) for any
/// non-reconstructable opcode or any instruction whose operand shape does not
/// match the typed per-opcode schema (fail-closed: a malformed instruction is NOT
/// silently credited).
///
/// # What it does
///
/// 1. Resolves the INTENDED source op + arity via the TYPED exhaustive
///    [`opcode_to_source_op`] (no string lookup).
/// 2. Reads `inst.operands` POSITIONALLY using the typed schema `[rd, rs1,
///    rs2|imm]`. The `rs1`/`rs2` register slots bind to fresh symbolic vars at
///    the operand width; an immediate slot binds to a `bv_const` (the I-type
///    value-role immediate, sign-extended bit pattern, at the op width; the
///    Slli/Srli shamt as the shift amount).
/// 3. Builds `trust_ir_expr` from the INTENDED source op over the shared syms and
///    the machine side from the REAL opcode's RISC-V encoder, wired EXACTLY as
///    emitted (`rs1` first, `rs2`/imm second).
/// 4. Tags the obligation [`MachineSideProvenance::Reconstructed`].
///
/// SHIFTS additionally carry a LOAD-BEARING `amount < width` precondition (#57):
/// the machine side is the FAITHFUL hardware-amount-masked encoder
/// (`encode_sll_masked` etc.) and the source side is the plain-`bvshl` trust_ir
/// encoder. In range the mask is the identity so they agree; out of range the
/// masked machine side and the clamp-to-0 source side DIVERGE, so the
/// precondition is genuinely required (strip it and a shift by `width` refutes).
/// RV64 shifts >= XLEN are themselves UB/impl-defined, so scoping them out is
/// faithful.
pub fn reconstruct_alu_obligation(inst: &RiscVISelInst) -> Option<ProofObligation> {
    use crate::riscv_semantics::{
        encode_add, encode_addi, encode_and, encode_mul, encode_or, encode_sll_masked, encode_slt,
        encode_sltu, encode_sra_masked, encode_srl_masked, encode_sub, encode_xor,
    };
    use crate::trust_ir_semantics::{
        encode_trust_ir_binop, encode_trust_ir_bitwise_binop, encode_trust_ir_icmp,
        encode_trust_ir_shift,
    };

    let (source_op, arity) = opcode_to_source_op(inst.opcode)?;

    // Typed positional schema: [rd, rs1, rs2|imm].
    if inst.operands.len() != 3 {
        return None;
    }
    let rd = &inst.operands[0];
    let rs1 = &inst.operands[1];
    let rs2 = &inst.operands[2];

    // The destination register fixes the operation width.
    let dst_width = operand_reg_width_bits(rd)?;
    let size = width_to_operand_size(dst_width);
    let ty = width_to_type(dst_width)?;
    let from_opcode = format!("{:?}", inst.opcode);

    // rs1 must be a register at the destination width; bind to a fresh sym.
    if operand_reg_width_bits(rs1)? != dst_width {
        return None;
    }
    let sym1 = SmtExpr::var("recon_rs1", dst_width);

    // rs2 is a register (R-type) or an immediate (I-type ADDI / shift SLLI/SRLI).
    let sym2 = match rs2 {
        RiscVISelOperand::Imm(imm) => {
            let raw = (*imm as i128) as u128;
            let masked = (raw as u64) & crate::smt::mask(u64::MAX, dst_width);
            SmtExpr::bv_const(masked, dst_width)
        }
        reg => {
            if operand_reg_width_bits(reg)? != dst_width {
                return None;
            }
            SmtExpr::var("recon_rs2", dst_width)
        }
    };

    // SOURCE side: the INTENDED trust_ir op over shared syms. Shifts add a
    // LOAD-BEARING amount<width precondition (#57).
    let mut preconditions: Vec<SmtExpr> = vec![];
    let (trust_ir_expr, source_label): (SmtExpr, String) = match &source_op {
        RiscVSourceOp::Binary(op) => (
            encode_trust_ir_binop(op, ty, sym1.clone(), sym2.clone()),
            format!("{op:?}"),
        ),
        RiscVSourceOp::Bitwise(op) => (
            encode_trust_ir_bitwise_binop(op, ty, sym1.clone(), sym2.clone()),
            format!("{op:?}"),
        ),
        RiscVSourceOp::Shift(op) => {
            // LOAD-BEARING precondition (#57): amount (rs2/shamt) < width. In
            // range the hardware mask is the identity; out of range the faithful
            // masked machine side diverges from the clamp-to-0 trust_ir side, so
            // this precondition is genuinely required for the obligation to
            // discharge Valid (not cosmetic). RV64 shifts >= XLEN are UB.
            preconditions.push(
                sym2.clone()
                    .bvult(SmtExpr::bv_const(dst_width as u64, dst_width)),
            );
            (
                encode_trust_ir_shift(op, ty, sym1.clone(), sym2.clone()),
                format!("{op:?}"),
            )
        }
        RiscVSourceOp::Compare(cc) => (
            encode_trust_ir_icmp(cc, ty, sym1.clone(), sym2.clone()),
            format!("Icmp_{cc:?}"),
        ),
    };

    // MACHINE side: the REAL opcode's RISC-V encoder, wired EXACTLY as emitted
    // (rs1 first, rs2/imm second). For a non-commutative op (Sub/shifts/Slt/Sltu)
    // a swap of the source slots changes the result => refutes. Shifts use the
    // FAITHFUL amount-masked encoder.
    let machine_expr = match inst.opcode {
        RiscVOpcode::Add | RiscVOpcode::Addi => {
            // ADD and the ADDI value role are both `rs1 + rs2|imm`.
            if matches!(inst.opcode, RiscVOpcode::Addi) {
                encode_addi(size, sym1.clone(), sym2.clone())
            } else {
                encode_add(size, sym1.clone(), sym2.clone())
            }
        }
        RiscVOpcode::Sub => encode_sub(size, sym1.clone(), sym2.clone()),
        RiscVOpcode::Mul => encode_mul(size, sym1.clone(), sym2.clone()),
        RiscVOpcode::And => encode_and(size, sym1.clone(), sym2.clone()),
        RiscVOpcode::Or => encode_or(size, sym1.clone(), sym2.clone()),
        RiscVOpcode::Xor => encode_xor(size, sym1.clone(), sym2.clone()),
        RiscVOpcode::Sll | RiscVOpcode::Slli => encode_sll_masked(size, sym1.clone(), sym2.clone()),
        RiscVOpcode::Srl | RiscVOpcode::Srli => encode_srl_masked(size, sym1.clone(), sym2.clone()),
        RiscVOpcode::Sra => encode_sra_masked(size, sym1.clone(), sym2.clone()),
        RiscVOpcode::Slt => encode_slt(size, sym1.clone(), sym2.clone()),
        RiscVOpcode::Sltu => encode_sltu(size, sym1.clone(), sym2.clone()),
        // Unreachable: opcode_to_source_op only returned for the arms above. Fail
        // closed rather than panic.
        _ => return None,
    };

    // Only register sources become declared SMT inputs; an immediate is constant.
    let mut inputs = vec![("recon_rs1".to_string(), dst_width)];
    if matches!(rs2, RiscVISelOperand::VReg(_)) {
        inputs.push(("recon_rs2".to_string(), dst_width));
    }

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED riscv {}_{} -> {:?} (real-operand)",
            source_label, dst_width, inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr: machine_expr,
        inputs,
        preconditions,
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: arity.as_u8(),
        },
    })
}

/// Build a REPRESENTATIVE [`RiscVISelInst`] for a reconstructable RISC-V opcode,
/// with fresh register operands in the typed positional schema the reconstructor
/// expects. Returns `None` for any opcode not in [`opcode_to_source_op`]. Mirrors
/// `function_verifier::representative_reconstructable_inst`.
///
/// This is the opcode-complete entry point the COVERAGE GATE uses: the gate has
/// only an opcode, so it synthesizes a representative instance (the generic RV64
/// register form `[rd, rs1, rs2]`, all 64-bit), reconstructs the obligation, and
/// marks the opcode covered in its inventory iff that obligation discharges
/// `Valid` (inventory only, never instruction credit).
pub fn representative_reconstructable_inst(opcode: RiscVOpcode) -> Option<RiscVISelInst> {
    // Only opcodes the reconstructor handles get a representative instance.
    opcode_to_source_op(opcode)?;
    let x = |id: u32| RiscVISelOperand::VReg(VReg::new(id, RegClass::Gpr64));
    Some(RiscVISelInst::with_operands(opcode, vec![x(0), x(1), x(2)]))
}

/// Does a representative reconstructed obligation for `opcode` discharge `Valid`
/// under `config`? Used by the COVERAGE GATE to mark a reconstructable RISC-V
/// opcode as covered in its inventory. Mirrors
/// `function_verifier::reconstruction_discharges_valid`.
///
/// Returns `false` (NOT covered) for any opcode that is not reconstructable, has
/// no representative instance, fails to reconstruct, is not tagged Reconstructed,
/// or whose reconstructed obligation does not discharge `Valid` for its
/// synthesized representative instance, where a sampled sweep counts as
/// `Valid`. That is NOT the per-instruction walk's credit rule: since E0.2 the
/// walk credits an emitted instruction only from its own obligation with a
/// complete (exhaustive) discharge and reports a sampled one as unverified. A
/// `true` here is never instruction credit.
pub fn reconstruction_discharges_valid(opcode: RiscVOpcode, config: &VerificationConfig) -> bool {
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
// RiscVFunctionVerifier
// ---------------------------------------------------------------------------

/// Verifier that maps RiscVISelFunction instructions to proof obligations.
pub struct RiscVFunctionVerifier {
    config: VerificationConfig,
}

impl RiscVFunctionVerifier {
    /// Create a new RISC-V function verifier with default configuration.
    pub fn new() -> Self {
        Self {
            config: VerificationConfig::default(),
        }
    }

    /// Create a new RISC-V function verifier with a custom configuration.
    pub fn with_config(config: VerificationConfig) -> Self {
        Self { config }
    }

    /// Map a RISC-V opcode to a registry search substring.
    ///
    /// Returns `None` for EVERY opcode, and has since the #62 retraction: the
    /// static `"riscv: <op> -> <INSN>"` theorems were degenerate X==X and were
    /// retracted, so no RISC-V opcode names a registry theorem. It survives as
    /// the (empty) mapping the coverage gate audits against, so that a future
    /// mapping has one place to land and the gate reports `NoProofMapping`
    /// rather than inventing one.
    ///
    /// [`Self::verify`] does not consult it: a registry theorem selected by
    /// name is never per-instruction credit (E0.2), so the walk has no registry
    /// arm on this backend at all. Structural and dead opcodes are classified
    /// `FailClosedAllowlisted` in `coverage_gate::classify_riscv`.
    pub fn opcode_to_proof_query(_opcode: RiscVOpcode) -> Option<&'static str> {
        // #62 retraction (group b): the 1:1 dataflow ALU/shift/imm/cmp opcodes
        // (Add/Sub/Mul/And/Or/Xor/Sll/Srl/Sra/Slli/Srli/Addi/Slt/Sltu) previously
        // bound to the static "riscv: <op> -> <INSN>" proofs, which were degenerate
        // X==X and have been RETRACTED. Coverage for these opcodes is now the
        // GENUINE operand-reconstruction credit (audit_riscv
        // reconstruction_discharges_valid via opcode_to_source_op — the machine
        // side is rebuilt from the REAL opcode+operands, so a wrong isel choice
        // refutes), NOT a static DB lookup.
        //
        // Everything else has no registered RISC-V lowering value proof: structural
        // forms (branches/jumps/loads/stores/Ebreak/address+frame roles) and dead
        // never-emitted variants (W-forms, MULH*, DIV/REM, FP-D) are
        // FailClosedAllowlisted in classify_riscv; pseudos are PseudoOrTrap. The
        // comparison IDIOMS (Eq/Ne/Sge/Sgt/Sle/Uge/Ugt/Ule) are emitted as
        // MULTI-instruction sequences (SUB+SLTIU, SLT+XORI, ...) rather than a
        // single dedicated opcode, so they are not opcode-keyed here.
        None
    }

    /// Reason an opcode is skipped as a real trap instruction (not a pseudo).
    ///
    /// `Ebreak` is the RISC-V analogue of x86 `Ud2` / AArch64 `Brk`: a real trap
    /// instruction with no value-equivalence proof obligation.
    fn trap_skip_reason(opcode: RiscVOpcode) -> Option<&'static str> {
        match opcode {
            RiscVOpcode::Ebreak => Some("RISC-V trap instruction (EBREAK)"),
            _ => None,
        }
    }

    /// PHASE-2 OPERAND RECONSTRUCTION (RISC-V, task #63). Try to verify `inst` by
    /// reconstructing its obligation from the REAL emitted opcode+operands.
    /// Mirrors `FunctionVerifier::try_reconstruct_pilot` exactly.
    ///
    /// - `Some(Verified { degenerate: false, .. })` when the opcode is
    ///   reconstructable AND the reconstructed obligation discharges `Valid`
    ///   with complete (`Exhaustive`) evidence. Credited (`degenerate: false`)
    ///   because its provenance is `Reconstructed` — the machine side came from
    ///   the REAL instruction, so a wrong opcode/wiring would have refuted, even
    ///   though a *correct* commutative lowering reconstructs to
    ///   `bvadd == bvadd`.
    /// - `Some(Unverified { .. })` when it discharges only by sampling:
    ///   statistical evidence is reported, never credited.
    /// - `Some(Failed { .. })` when the reconstructed obligation REFUTES (wrong
    ///   isel opcode/wiring). This is the content of the mechanism.
    /// - `None` when the opcode is NOT reconstructable, or the instruction has no
    ///   reconstructable operand shape (e.g. an opcode-only stub). Such an
    ///   instruction has no instruction-built obligation and is never credited.
    ///
    /// The credit rule keys on [`ProofObligation::is_reconstructed`], never on a
    /// `name.contains` lookup — the binding is a typed exhaustive opcode match
    /// plus a typed positional operand schema (anti-f81e45b; asserted by
    /// `tests/reconstruction_riscv.rs`).
    fn try_reconstruct(&self, inst: &RiscVISelInst) -> Option<InstructionVerificationResult> {
        // Not a reconstructable opcode at all -> leave on the existing path.
        opcode_to_source_op(inst.opcode)?;
        // Reconstructable opcode but no reconstructable operand shape -> fall through.
        let obligation = reconstruct_alu_obligation(inst)?;

        let strength = VerificationStrength::for_obligation_with_config(&obligation, &self.config);
        let vresult = verify_by_evaluation_with_config(&obligation, &self.config);
        debug_assert!(
            obligation.is_reconstructed(),
            "reconstruct_alu_obligation must tag Reconstructed provenance"
        );
        Some(InstructionVerificationResult::from_discharge(
            &obligation.name,
            ProofCategory::RiscVLowering,
            vresult,
            strength,
            // Credited: a reconstructed obligation is the genuine
            // (non-degenerate) credit even when structurally X==X.
            !obligation.is_reconstructed(),
        ))
    }

    /// Verify every instruction in a RISC-V ISel function.
    ///
    /// Walks the instruction stream in order. Pseudo-ops (Phi, StackAlloc, Nop,
    /// TrapBoundsCheckExact) are reported as `Skipped`, as is the EBREAK trap.
    pub fn verify(&self, func: &RiscVISelFunction) -> FunctionVerificationReport {
        let mut instructions: Vec<InstructionReport> = Vec::new();

        for (inst_idx, inst) in func.insts.iter().enumerate() {
            let result = if let Some(reason) = Self::trap_skip_reason(inst.opcode) {
                InstructionVerificationResult::Skipped {
                    reason: reason.to_string(),
                }
            } else if inst.opcode.is_pseudo() {
                InstructionVerificationResult::Skipped {
                    reason: format!("{:?} is a pseudo-instruction", inst.opcode),
                }
            } else if let Some(recon_result) = self.try_reconstruct(inst) {
                // PHASE-2 OPERAND RECONSTRUCTION (RISC-V, task #63).
                //
                // The 14 reconstructable ALU/shift/compare opcodes with a real
                // operand shape are routed through reconstruction. The machine
                // side is rebuilt from the REAL emitted opcode+operands, so a
                // wrong isel choice (e.g. SUB for Iadd, SLL for Ushr) or wrong
                // operand wiring on a non-commutative op (SUB/shifts/SLT)
                // REFUTES. Credited Verified IFF `is_reconstructed() && Valid`
                // with complete evidence.
                recon_result
            } else {
                // No registry arm: `opcode_to_proof_query` names no theorem for
                // any RISC-V opcode (#62), and a theorem found by name would not
                // be credit anyway (E0.2).
                InstructionVerificationResult::Unverified {
                    reason: format!("no proof mapping for RISC-V opcode {:?}", inst.opcode),
                }
            };

            instructions.push(InstructionReport {
                inst_index: inst_idx,
                opcode: InstructionOpcode::RiscV(inst.opcode),
                result,
            });
        }

        FunctionVerificationReport {
            function_name: func.name.clone(),
            precondition_failure: None,
            instructions,
        }
    }
}

impl Default for RiscVFunctionVerifier {
    fn default() -> Self {
        Self::new()
    }
}

/// Convenience: verify a [`RiscVISelFunction`] using default configuration.
///
/// The primary entry point for RISC-V function-level verification. Mirrors
/// [`crate::x86_64_function_verifier::verify_x86_64_function`].
pub fn verify_riscv_function(func: &RiscVISelFunction) -> FunctionVerificationReport {
    RiscVFunctionVerifier::new().verify(func)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn func_with(opcodes: &[RiscVOpcode]) -> RiscVISelFunction {
        let mut f = RiscVISelFunction::new("test".to_string());
        for &op in opcodes {
            f.push_opcode(op);
        }
        f
    }

    /// All 14 reconstructable ALU/shift/compare opcodes, each wired with a
    /// representative real operand shape (the generic RV64 register form).
    fn all_alu_reconstructable() -> [RiscVOpcode; 14] {
        [
            RiscVOpcode::Add,
            RiscVOpcode::Sub,
            RiscVOpcode::Mul,
            RiscVOpcode::And,
            RiscVOpcode::Or,
            RiscVOpcode::Xor,
            RiscVOpcode::Sll,
            RiscVOpcode::Srl,
            RiscVOpcode::Sra,
            RiscVOpcode::Slli,
            RiscVOpcode::Srli,
            RiscVOpcode::Addi,
            RiscVOpcode::Slt,
            RiscVOpcode::Sltu,
        ]
    }

    fn func_with_operands(opcodes: &[RiscVOpcode]) -> RiscVISelFunction {
        let mut f = RiscVISelFunction::new("test".to_string());
        for &op in opcodes {
            let inst = representative_reconstructable_inst(op)
                .unwrap_or_else(|| panic!("{op:?} must have a representative"));
            f.insts.push(inst);
        }
        f
    }

    /// The walk has no registry-name arm on RISC-V, and no opcode could reach
    /// one: `opcode_to_proof_query` names no theorem for ANY opcode (#62), so
    /// every opcode-only instruction is either skipped (pseudo/trap) or refused
    /// with "no proof mapping", never a registry lookup and never `Verified`.
    /// A future mapping must turn this red and be decided explicitly.
    #[test]
    fn no_riscv_opcode_reaches_a_registry_name_lookup() {
        let all = crate::coverage_gate::ALL_RISCV_OPCODES;
        assert!(all.len() > 50, "the exhaustive opcode list must be real");
        for &op in all {
            assert_eq!(
                RiscVFunctionVerifier::opcode_to_proof_query(op),
                None,
                "{op:?}"
            );
        }
        let report = verify_riscv_function(&func_with(all));
        assert_eq!(report.instructions.len(), all.len());
        assert_eq!(report.verified_count(), 0, "{report:?}");
        assert_eq!(report.registry_name_lookup_count(), 0, "{report:?}");
        let mut refused = 0;
        for r in &report.instructions {
            match &r.result {
                InstructionVerificationResult::Skipped { .. } => {}
                InstructionVerificationResult::Unverified { reason } => {
                    assert!(
                        reason.starts_with("no proof mapping for RISC-V opcode"),
                        "{}: {reason}",
                        r.opcode
                    );
                    refused += 1;
                }
                other => panic!("{}: opcode-only row must not be {other:?}", r.opcode),
            }
        }
        assert!(refused > 0, "{report:?}");
    }

    #[test]
    fn clean_alu_opcodes_unverified_without_operands_after_static_proof_retraction() {
        // #62: the degenerate static-DB "riscv: <op> -> <INSN>" X==X proofs were
        // RETRACTED. Opcode-only stubs (no operands) DO NOT reconstruct and now have
        // no static fallback, so they are Unverified. (With REAL operands they route
        // through reconstruction, whose sampled RV64 discharge is reported but not
        // credited — see `clean_alu_opcodes_reconstruct_but_sampling_is_not_credited`.)
        let report = verify_riscv_function(&func_with(&all_alu_reconstructable()));
        for r in &report.instructions {
            assert!(
                r.result.is_unverified(),
                "{} should be Unverified without operands after #62 retraction: {:?}",
                r.opcode,
                r.result
            );
        }
    }

    /// E0.2 (statistical credit withdrawn) on RISC-V: with REAL operands every
    /// one of the 14 ALU/shift/compare opcodes still routes through
    /// reconstruction, but each RV64 instance discharges only by sampling, so
    /// all 14 are reported with their sample counts and none is credited.
    #[test]
    fn clean_alu_opcodes_reconstruct_but_sampling_is_not_credited() {
        let report = verify_riscv_function(&func_with_operands(&all_alu_reconstructable()));
        assert_eq!(report.genuinely_verified_count(), 0, "{report:?}");
        assert_eq!(report.verified_count(), 0, "{report:?}");
        assert_eq!(report.sampled_uncredited_count(), 14, "{report:?}");
        for r in &report.instructions {
            match &r.result {
                InstructionVerificationResult::Unverified { reason } => {
                    assert!(
                        reason.starts_with(
                            crate::function_verifier::STATISTICAL_EVIDENCE_IS_NOT_CREDIT
                        ),
                        "{}: {reason}",
                        r.opcode
                    );
                    assert!(reason.contains("RECONSTRUCTED"), "{}: {reason}", r.opcode);
                }
                other => panic!(
                    "{} expected uncredited sampled reconstruction, got {other:?}",
                    r.opcode
                ),
            }
        }
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }

    #[test]
    fn pseudos_and_ebreak_are_skipped() {
        let report = verify_riscv_function(&func_with(&[
            RiscVOpcode::Phi,
            RiscVOpcode::StackAlloc,
            RiscVOpcode::Nop,
            RiscVOpcode::TrapBoundsCheckExact,
            RiscVOpcode::Ebreak,
        ]));
        for r in &report.instructions {
            assert!(
                r.result.is_skipped(),
                "{} should be skipped: {:?}",
                r.opcode,
                r.result
            );
        }
    }

    #[test]
    fn structural_and_dead_opcodes_are_unverified_not_mapped() {
        // Branches/loads/stores and dead variants have no value proof mapping.
        for op in [
            RiscVOpcode::Bne,
            RiscVOpcode::Jal,
            RiscVOpcode::Ld,
            RiscVOpcode::Sd,
            RiscVOpcode::Addw,  // dead W-form
            RiscVOpcode::Mulh,  // dead M high-half
            RiscVOpcode::Div,   // dead division
            RiscVOpcode::FaddD, // dead FP-D
        ] {
            assert!(
                RiscVFunctionVerifier::opcode_to_proof_query(op).is_none(),
                "{op:?} should have no RISC-V value-proof mapping"
            );
        }
    }

    #[test]
    fn alu_opcodes_have_no_static_query_and_are_reconstruction_credited() {
        // #62: the 14 dataflow ALU/shift/imm/cmp opcodes' static "riscv: <op> ->
        // <INSN>" proofs were degenerate X==X and were RETRACTED. They now have NO
        // opcode_to_proof_query mapping (None) — their only route is operand
        // reconstruction, credited only with complete evidence (see
        // `clean_alu_opcodes_reconstruct_but_sampling_is_not_credited`). The only
        // registered RiscVLowering proofs are the 8
        // GENUINE multi-instruction comparison idioms.
        for op in [
            RiscVOpcode::Add,
            RiscVOpcode::Sub,
            RiscVOpcode::Mul,
            RiscVOpcode::And,
            RiscVOpcode::Or,
            RiscVOpcode::Xor,
            RiscVOpcode::Sll,
            RiscVOpcode::Srl,
            RiscVOpcode::Sra,
            RiscVOpcode::Slli,
            RiscVOpcode::Srli,
            RiscVOpcode::Addi,
            RiscVOpcode::Slt,
            RiscVOpcode::Sltu,
        ] {
            assert!(
                RiscVFunctionVerifier::opcode_to_proof_query(op).is_none(),
                "{op:?}: static degenerate proof retracted in #62 -> None (reconstruction-credited)"
            );
        }

        let db = crate::proof_database::ProofDatabase::new();
        let proofs = db.by_category(ProofCategory::RiscVLowering);
        assert_eq!(
            proofs.len(),
            8,
            "only the 8 genuine RISC-V comparison idioms remain after #62, got {}",
            proofs.len()
        );
        for p in &proofs {
            assert!(
                p.obligation.trust_ir_expr != p.obligation.aarch64_expr,
                "registered RISC-V proof {:?} must be non-degenerate (genuine idiom)",
                p.obligation.name
            );
        }
    }
}
