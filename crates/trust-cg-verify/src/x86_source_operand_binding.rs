// trust-cg-verify/x86_source_operand_binding.rs — TV-1 EXTENDED operand binding
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! TV-1 EXTENDED: bind a RECONSTRUCTED x86-64 obligation's symbolic inputs to
//! the EXACT operands of the identified source instruction.
//!
//! # The gap this closes
//!
//! `lowering_proof::discharge_reconstructed_obligation` refuses to grant a
//! reconstruction any `Formal` credit, and says exactly why: the reconstructors
//! infer the nominal source operation FROM the emitted opcode and do not bind
//! the obligation's symbolic inputs to the exact source operands, so a bad
//! source `Iadd` lowered to a machine `SUB` self-reconstructs as
//! `bvsub == bvsub`. A solver can prove that represented equality; it is not
//! evidence about THIS lowering.
//!
//! TV-2 ([`crate::provenance_xcheck`]) already supplies two of the three
//! ingredients a complete per-instruction lowering claim needs:
//!
//! 1. ATTRIBUTION INTEGRITY — the TV-1 stamp's `(block, index)` names a real
//!    instruction in the replayed LIR function ISel consumed, and the stamped
//!    digest equals that instruction's recomputed `lowering_digest`.
//! 2. OP-CLASS CONSISTENCY — the emitted opcode's definite semantic class is a
//!    plausible constituent of a lowering of that source instruction.
//!
//! The third — binding the obligation's symbolic INPUTS to that instruction's
//! exact OPERANDS — has nothing to check against in TV-1 as stamped:
//! `SourceInstDigest` is FNV-1a/64 over the opcode's `Debug` rendering plus the
//! argument/result ARITIES, so it is opcode and shape, never operand identity.
//! `X86ISelFunction::source_operand_bindings` (TV-1 EXTENDED) records the
//! missing correspondence at the two selection chokepoints that resolve SSA
//! values, and this module is the check that consumes it.
//!
//! # What a returned [`ExactSourceOperandBinding`] establishes
//!
//! Let `M` be the emitted machine instruction, `S` the replayed LIR instruction
//! at `M`'s stamped coordinates, and `σ` ISel's recorded resolution of `S`'s SSA
//! values to machine operands. A witness is returned only when ALL of:
//!
//! * `S` exists and its recomputed digest equals the stamp (TV-2). TV-2's
//!   op-class check ALSO runs, but it is not load-bearing for every family and
//!   contributes NOTHING for the copy family: `x86_emitted_op_class` answers
//!   `None` for `CopyGpr`/`CopyXmm`, so there is no class to compare and a move
//!   passes that check beside any source instruction whatever;
//! * the SOURCE OPERATION is checked by EQUALITY against `S.opcode`, in every
//!   family without exception, and BEFORE any property of the emission is
//!   consulted. The reconstruction infers its source operation FROM `M.opcode`,
//!   so this equality is what turns the obligation into `⟦S.opcode⟧ ==
//!   ⟦M.opcode⟧`: an `Iadd` lowered to `SUB` reads `bvadd == bvsub` and REFUTES,
//!   and a `MOV` stamped from an `Isub` is refused outright by [`bind_copy`]
//!   rather than credited for the `X == X` it would otherwise prove;
//! * the emitted opcode is one of the forms that source operation's own
//!   permitted-form table admits, at the width that form fixes where it fixes
//!   one (the copy family's table is [`copy_form_bits`]);
//! * every operand slot the reconstruction reads is EXACTLY the machine operand
//!   `σ` recorded for the corresponding operand of `S`, per the family's
//!   positional schema below — including the result slot where the family has
//!   one, and no family binds one end only;
//! * every bound operand's ISel-recorded source width equals the width the
//!   reconstruction built the obligation at.
//!
//! So the theorem the discharge then proves is, for the operands `σ` names,
//! `⟦S⟧(operands) = ⟦M⟧(operands)` — a claim about this source instruction and
//! this emission, not about a family the emitted opcode nominated for itself.
//!
//! ## THE COPY FAMILY'S REAL GUARANTEE, stated separately because it is the one
//! whose obligation proves nothing
//!
//! A register copy's obligation is `X == X`. It is true of every emission, so
//! the discharge contributes ZERO refutation power and TV-2 contributes zero
//! (no op class). The credit therefore rests ENTIRELY on four decidable
//! syntactic facts about recorded data, and this is the complete list:
//!
//! 1. the replayed instruction's opcode IS `Opcode::Copy` — so the emitted move
//!    RENAMES a value rather than REPLACING a computation;
//! 2. that `Copy` has one operand and one result, and the emission has two
//!    operands;
//! 3. the emitted opcode is an identity move ([`copy_form_bits`]) and both
//!    carriers have the width that form fixes, so a 32-bit move cannot be
//!    credited for a 64-bit copy;
//! 4. the destination is `σ(result)`, the source is `σ(arg)`, both at that
//!    width, and the two differ.
//!
//! Nothing weaker is a copy credit. In particular a copy with only ONE end
//! bound — an ABI return, argument or call-result move, whose other end is a
//! physical register no operand of the source instruction names — earns nothing
//! here, because the unbound end is exactly where such a move's claim lives: a
//! `MOV` of the right value into the wrong ABI register is a miscompilation that
//! `X == X` cannot see. See [`X86OperandBindingSchema::BoundSourceOperandCopy`]
//! and [`X86OperandBindingSchema::BoundResultOperandCopy`], which are reserved
//! and unreachable for that reason.
//!
//! # What it does NOT establish (the evidence boundary)
//!
//! * NOT that `σ` is a correct DATAFLOW assignment — that the named machine
//!   operand actually holds `S`'s value at that program point. That is register
//!   allocation / post-RA dataflow evidence
//!   ([`crate::post_regalloc_recheck`], TV-5's post-RA reaching-def work,
//!   [`crate::carrier_hygiene`]) and the ISel dataflow-integrity gate. The
//!   binding says WHICH operand the reconstruction's symbols stand for, not
//!   that the operand's contents are right.
//! * NOT anything about flags, memory ordering, or bits outside the modeled
//!   width. Those are the flag-consumer, volatile-trace and carrier-hygiene
//!   obligations.
//! * NOT that the instruction STREAM is a complete lowering of the LIR: a
//!   dropped source instruction is TV-3's fail-closed gate, not this one.
//! * NOT anything about a copy whose other end is an ABI location. Rather than
//!   credit half of it, [`bind_copy`] refuses the shape outright; the outgoing
//!   ARGUMENT half is refused on purpose even when the argument values' own
//!   types would "determine" the register, because that assumes the callee's
//!   declared parameter types are the ones the caller lowered against. Where a
//!   value had to go remains the call/return ABI evidence
//!   ([`crate::call_lowering_proofs`], the SysV ABI canaries).
//! * Nothing about the emitted BYTES: this verifier runs on the pre-register-
//!   allocation ISel function, exactly as the statistical credit it replaces
//!   did. Register allocation and encoding are separately checked.
//!
//! # WHAT THIS MODULE REACHES ON THIS TREE, before any claim below is read
//!
//! Every `Formal` sentence in this module is a statement about the MECHANISM:
//! what the binding makes reachable and what it refuses. It is not a claim that
//! anything is credited today. Upstream's E0.2/E0.5 withdrawal deleted
//! `lowering_proof::try_formal_on_miss`, the arm that ran one live checked solve
//! on a tier-0 miss, and that arm is what a bound reconstruction discharged
//! through: a freshly reconstructed obligation has neither a committed portable
//! DRAT certificate nor a tier-0 row, so the two lanes that survive both miss.
//! MEASURED on the Linux x86-64 floor
//! (`reports/perf/2026-09-27-linux-x86-64-xd01-on-current-upstream/`), no bound
//! row is credited and no certificate names a schema.
//!
//! What the binding therefore contributes on this tree is REFUTATION and
//! REFUSAL — a wrong source opcode, swapped operands, a wrong width or a wrong
//! result register is rejected rather than self-attested — plus the gate that
//! keeps an unbound reconstruction out of the `Formal` arm entirely. Restoring
//! the credit needs an x86-64 analogue of the source-bound live lanes upstream
//! kept for `SourceBoundFrame`/`SourceBoundAlu`, gated on the admitted AY's
//! binary identity. That lane does not exist yet, and nothing here should be
//! read as if it did.
//!
//! # What an adversary must break
//!
//! To obtain a `Formal` credit for a wrong lowering an adversary must either
//! (a) forge a TV-1 stamp that names a different LIR instruction whose
//! recomputed digest still matches — a second-preimage on the digest over
//! `(opcode Debug, arg arity, result arity)`; or (b) make ISel record a `σ`
//! entry that names an operand the emitted instruction does not read, which
//! cannot help, because the check compares the EMITTED operand against the
//! recorded one and a disagreement withholds the binding; or (c) defeat the
//! solver/portable-certificate discharge of `⟦S.opcode⟧ == ⟦M.opcode⟧`.
//!
//! The digest is the weakest of the three and it is TV-2's pre-existing
//! strength, not something this module adds or weakens: an adversary who can
//! forge it already defeats the enforced cross-check. For the COPY family
//! route (c) is empty — `X == X` needs no defeating — so a copy credit rests on
//! (a) and (b) alone, and that is the whole reason its four checks are listed
//! exhaustively above rather than summarised.
//!
//! WHERE THE REFUTATION POWER ACTUALLY LIVES, per family, because it is not
//! uniform and a single word ("Formal") would hide that:
//!
//! * For the ALU, extend and FP families the obligation is STRUCTURALLY
//!   DISTINCT (`bvadd` vs the x86 ADD encoder), so the solver half has real
//!   content AND the binding decides which operands it is about. Both halves
//!   bite.
//! * For a register COPY the obligation is `X == X`: the solver half is
//!   trivially true and contributes nothing, and TV-2 contributes nothing
//!   either — a move has NO definite op class, so the op-class cross-check has
//!   nothing to compare and passes beside any source instruction whatever. (An
//!   earlier revision of this module claimed that check as part of the copy
//!   credit. It was vacuous, and while it stood, `bind_copy` checked no source
//!   operation at all: a `MOV` stamped from an `Isub` bound and was credited.)
//!   EVERY bit of the copy credit is therefore the four syntactic facts listed
//!   under "THE COPY FAMILY'S REAL GUARANTEE" above — replayed opcode, arity,
//!   permitted form and width, and both operand ends. What makes it honest is
//!   not that a solver ran but that nothing in the chain is sampled: each of
//!   the four is a decidable check on recorded data. The published certificate
//!   names the schema for exactly this reason, so a reader is never left
//!   inferring which half did the work.
//! * For the memory and GEP families the solver half checks the two independent
//!   effective-address encoders against each other, and the binding decides the
//!   base/index/value operands, the displacement and the scale.

use trust_cg_ir::provenance::SourceInstId;
use trust_cg_lower::instructions::{Opcode as LirOpcode, Value};
use trust_cg_lower::x86_64_isel::{
    X86ISelInst, X86ISelOperand, X86SourceOperandBinding, X86SourceOperandBindings,
};

use crate::provenance_xcheck::LirSourceInst;

/// Which positional operand schema was checked to produce a witness.
///
/// Carried in the discharge key so a BOUND and an UNBOUND instruction with
/// byte-identical obligation content can never share a deduped verdict, and so
/// a certificate's strength names the schema that earned it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum X86OperandBindingSchema {
    /// `[dst, src]` copy of a replayed `Opcode::Copy`'s single operand into its
    /// single result: BOTH slots bound (`σ(arg)`, `σ(result)`), the replayed
    /// source opcode is `Opcode::Copy` itself, and the emitted form is one of
    /// the identity moves a `Copy` may lower to, at the width that form fixes.
    ///
    /// This is the ONLY copy schema from which a witness can be built.
    ResultDefiningCopy,
    /// RESERVED and DELIBERATELY UNREACHABLE: a `[dst, src]` copy whose SOURCE
    /// slot is a bound operand of a non-`Copy` source instruction and whose
    /// DESTINATION is an ABI location (an outgoing argument, or a return
    /// register).
    ///
    /// [`bind_copy`] returns `None` for this shape, so no witness carries it.
    /// Binding only the copied VALUE says nothing about WHERE the value had to
    /// go, and for a return or argument move the destination is the whole
    /// content of the claim: a `MOV` of the right value into the WRONG register
    /// is a miscompilation, and the obligation is `X == X`, which cannot refute
    /// it. Re-enabling this schema means BINDING the ABI end — re-deriving the
    /// destination register from the replayed signature and declared
    /// convention, as [`derived_formal_argument_register`] already does for the
    /// entry half — never loosening the source side.
    BoundSourceOperandCopy,
    /// RESERVED and DELIBERATELY UNREACHABLE, symmetrically: a `[dst, src]`
    /// copy OUT of an ABI location into `σ(result)` (a call's result move).
    ///
    /// The register the value ARRIVED in is exactly where this claim's content
    /// lives, and binding it needs the CALLEE's declared return convention,
    /// which this module is not given. `None` until it is.
    BoundResultOperandCopy,
    /// `[dst, src1, src2]` integer/bitwise ALU: all three slots bound, and the
    /// replayed source opcode equals the reconstruction's source operation.
    BinaryAlu,
    /// `[dst, src]` integer unary (`Ineg`/`Bnot`): both slots bound.
    UnaryAlu,
    /// `[dst, src]` width-changing extend: both slots bound, and the replayed
    /// `Sextend`/`Uextend` widths equal the emitted opcode's.
    Extend,
    /// `[dst, src1, src2]` scalar floating-point binary: all three slots bound.
    FpBinary,
    /// `[dst, PReg]` formal-argument ABI move: the read register is the one an
    /// independent re-derivation of the declared convention assigns to the
    /// declared signature parameter this move materializes.
    FormalArgumentRegisterCopy,
    /// `[PReg, src]` RETURN ABI move: the WRITTEN register is the one an
    /// independent re-derivation of the declared convention assigns to the
    /// declared signature return value at this index, and the read operand is
    /// `σ` of the replayed `Return`'s operand at that same index.
    ///
    /// The mirror of [`Self::FormalArgumentRegisterCopy`], and the schema that
    /// makes a return move's UNBOUND end bound — which is why
    /// [`Self::BoundSourceOperandCopy`] does not need to exist for returns.
    /// Deliberately NOT extended to an outgoing CALL ARGUMENT or a call RESULT:
    /// an outgoing argument's register would have to be derived from the
    /// CALLEE's declared parameter types, and a call result's from the callee's
    /// declared return types, neither of which this function's own replayed
    /// signature contains. Deriving them from the argument or result VALUES'
    /// types instead would silently assume the callee's declaration agrees with
    /// what this caller lowered against.
    ReturnAbiRegisterCopy,
    /// `[dst, MemAddr { base, 0 }]` scalar load: the destination is the source
    /// `Load`'s result operand, the base is its address operand, and the
    /// displacement is zero — exactly the shape `select_memory_load` emits.
    ScalarLoadAtBoundAddress,
    /// `[MemAddr { base, 0 }, value]` scalar store: the base is the source
    /// `Store`'s address operand and the stored register is its value operand.
    ScalarStoreAtBoundAddress,
    /// `[dst, MemAddr { base, disp }]` struct/array field address: the base is
    /// the source `StructGep`'s address operand and the displacement is the
    /// field offset an INDEPENDENT layout computation over the declared struct
    /// type yields.
    FieldAddress,
    /// `[dst, SibMemAddr { base, index, scale, 0 }]` element address: base and
    /// index are the source `ArrayGep`'s two operands and the scale is the
    /// element size an INDEPENDENT layout computation over the declared element
    /// type yields.
    ElementAddress,
}

impl X86OperandBindingSchema {
    /// Short stable token for certificate/strength text.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::ResultDefiningCopy => "result-defining-copy",
            Self::BoundSourceOperandCopy => "bound-source-operand-copy",
            Self::BoundResultOperandCopy => "bound-result-operand-copy",
            Self::BinaryAlu => "binary-alu",
            Self::UnaryAlu => "unary-alu",
            Self::Extend => "extend",
            Self::FpBinary => "fp-binary",
            Self::FormalArgumentRegisterCopy => "formal-argument-register-copy",
            Self::ReturnAbiRegisterCopy => "return-abi-register-copy",
            Self::ScalarLoadAtBoundAddress => "scalar-load-at-bound-address",
            Self::ScalarStoreAtBoundAddress => "scalar-store-at-bound-address",
            Self::FieldAddress => "field-address",
            Self::ElementAddress => "element-address",
        }
    }
}

/// Unforgeable witness that one emitted instruction's reconstructed obligation
/// has an EXACT source/operand binding.
///
/// The field is private to this module, so the only way to obtain one is to pass
/// [`bind_exact_source_operands`] — the "when, and only when" of the strength
/// decision is therefore enforced by the type system, not by a convention.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExactSourceOperandBinding {
    schema: X86OperandBindingSchema,
}

impl ExactSourceOperandBinding {
    /// The positional schema this witness was checked against.
    pub fn schema(&self) -> X86OperandBindingSchema {
        self.schema
    }
}

/// The machine operand and ISel-recorded source WIDTH `σ` names for `value`
/// under `source`, or `None` when nothing was recorded, the pair is ambiguous,
/// or no source width was recorded (width exactness is not optional).
fn bound_operand(
    bindings: &X86SourceOperandBindings,
    source: SourceInstId,
    value: Value,
) -> Option<(&X86ISelOperand, u32)> {
    match bindings.get(source, value)? {
        X86SourceOperandBinding::Exact {
            operand,
            bits: Some(bits),
        } => Some((operand, *bits)),
        // An ambiguous pair resolved to more than one operand while this one
        // source instruction was lowered: which one a given emission read is
        // exactly what is not recorded. A pair with no recorded width cannot
        // establish width exactness. Both refuse.
        X86SourceOperandBinding::Exact { bits: None, .. } | X86SourceOperandBinding::Ambiguous => {
            None
        }
    }
}

/// `σ(value)` must be exactly `operand`, at a recorded source type of exactly
/// `width` bits.
///
/// The exact-width requirement is LOAD-BEARING for the same-width ALU families,
/// where callers pass the EMITTED REGISTER's width: a reconstruction builds its
/// obligation at the emitted carrier width, so an `Iadd` over `i8` values living
/// in `Gpr32` carriers yields the 32-bit theorem `bvadd32 == ADD r32,r32` while
/// the source semantics are `(a+b) mod 2^8`. Those differ exactly in the high
/// carrier bits — the carrier-hygiene hazard — so a narrow operand must NOT earn
/// a Formal credit from the wide theorem, and this refuses it.
///
/// The memory families pass the ACCESS width instead (the opcode fixes it
/// independently of the carrier), which is why they are checked against the
/// source's declared access type rather than against the register.
fn operand_matches(
    bindings: &X86SourceOperandBindings,
    source: SourceInstId,
    value: Value,
    operand: &X86ISelOperand,
    width: u32,
) -> bool {
    match bound_operand(bindings, source, value) {
        Some((bound, bits)) => bound == operand && bits == width,
        None => false,
    }
}

/// Bind `inst`'s reconstructed obligation to `source`'s exact operands, or
/// return `None` — in which case the instruction keeps its existing
/// `Exhaustive`/`Statistical` reconstruction strength unchanged.
///
/// PRECONDITION (the caller's, not re-checked here): `source` is the replayed
/// LIR instruction at `inst`'s stamped coordinates AND
/// [`crate::provenance_xcheck::cross_check_inst`] returned `None` for `inst`
/// under `ProvenanceXCheckMode::Enforce`. Without that, attribution integrity
/// is not established and no binding this module could compute would mean
/// anything.
pub(crate) fn bind_exact_source_operands(
    inst: &X86ISelInst,
    source_id: SourceInstId,
    source: &LirSourceInst,
    bindings: &X86SourceOperandBindings,
) -> Option<ExactSourceOperandBinding> {
    use crate::x86_64_function_verifier::{X86SourceOp, x86_opcode_to_source_op};

    // A function built outside the selector records nothing: fail closed rather
    // than treat "no recorded correspondence" as "the correspondence holds".
    if bindings.is_empty() {
        return None;
    }
    let (source_op, _arity) = x86_opcode_to_source_op(inst.opcode)?;
    let schema = match &source_op {
        X86SourceOp::CopyGpr | X86SourceOp::CopyXmm => bind_copy(inst, source_id, source, bindings),
        X86SourceOp::Binary(op) | X86SourceOp::Bitwise(op) => {
            bind_binary(inst, source_id, source, bindings, op)
        }
        X86SourceOp::FpBinary(op) => bind_fp_binary(inst, source_id, source, bindings, op),
        X86SourceOp::Neg => bind_unary(inst, source_id, source, bindings, &LirOpcode::Ineg),
        X86SourceOp::Not => bind_unary(inst, source_id, source, bindings, &LirOpcode::Bnot),
        X86SourceOp::Sextend { from_bits } => {
            bind_extend(inst, source_id, source, bindings, *from_bits, true)
        }
        X86SourceOp::Uextend { from_bits } => {
            bind_extend(inst, source_id, source, bindings, *from_bits, false)
        }
        X86SourceOp::MemLoad { load_bits } => {
            bind_mem_load(inst, source_id, source, bindings, *load_bits)
        }
        X86SourceOp::MemStore { store_bits } => {
            bind_mem_store(inst, source_id, source, bindings, *store_bits)
        }
        X86SourceOp::EffectiveAddress { has_index } => {
            bind_effective_address(inst, source_id, source, bindings, *has_index)
        }
        // Every other reconstructable family (shifts with an implicit CL count,
        // division, conditional moves, packed/vector forms, memory-source and
        // memory-destination ALU, the cross int/fp conversions, the V128 memory
        // moves) has no operand schema here yet, so it keeps its existing
        // strength and the promotion gate keeps refusing it. Adding a family
        // means adding its schema, never relaxing this fallthrough.
        _ => None,
    }?;
    Some(ExactSourceOperandBinding { schema })
}

/// Register width of an emitted GPR/XMM-scalar operand, whichever applies.
fn operand_width(operand: &X86ISelOperand) -> Option<u32> {
    crate::x86_64_function_verifier::x86_operand_reg_width_bits(operand)
        .or_else(|| crate::x86_64_function_verifier::x86_fp_scalar_width(operand))
}

/// The emitted moves a replayed `Opcode::Copy` may lower to, and the width each
/// form FIXES.
///
/// This is the copy family's permitted-form table, and it is read SOURCE-OPCODE
/// FIRST: [`bind_copy`] is entered only once the replayed opcode is known to be
/// `Copy`, and this table then says which emissions may implement one. Nothing
/// here lets the EMITTED opcode decide what the source operation was — that
/// inference is precisely the degeneracy the reconstructed route refuses
/// `Formal` for.
///
/// The form fixing the width is load-bearing: a `MovRR32` emitted for a 64-bit
/// copy transports only the low half, and comparing the emitted REGISTER's class
/// against itself would not notice.
fn copy_form_bits(opcode: trust_cg_ir::x86_64_ops::X86Opcode) -> Option<u32> {
    use trust_cg_ir::x86_64_ops::X86Opcode as X;
    match opcode {
        X::MovRR => Some(64),
        X::MovRR32 => Some(32),
        X::MovssRR => Some(32),
        X::MovsdRR => Some(64),
        // Every other move form (memory, immediate, sign/zero-extending,
        // packed, RIP-relative) is a different family with a different
        // obligation, and none of them is this schema's shape.
        _ => None,
    }
}

/// `[dst, src]` register copy of a replayed `Opcode::Copy`.
///
/// SOURCE-OPCODE FIRST, and that ordering is the whole fix. The reconstruction
/// hands this module a `CopyGpr`/`CopyXmm` source operation it read OFF THE
/// EMITTED OPCODE, and the resulting obligation is `X == X` — true of every
/// emission, so the solver half contributes nothing. If the schema then binds
/// only OPERANDS, a machine `MOV` that REPLACES its source instruction's
/// computation earns `Formal`: a `MOV dst, a` stamped from `Isub a, b -> dst`
/// has `σ(a)` in its source slot and `σ(dst)` in its destination slot, so every
/// operand slot it reads is exactly the recorded one, and TV-2 cannot object
/// because a move has no definite op class (`x86_emitted_op_class` answers
/// `None` for `CopyGpr`/`CopyXmm`, so there is nothing to compare). The
/// subtraction is simply gone, and the credit says the lowering was proved.
///
/// So the replayed opcode must BE `Opcode::Copy`. What the schema then
/// guarantees is stated in full on the module: a `Copy` renames one value, the
/// emitted form is an identity move that may implement one, and both ends are
/// the operands `σ` recorded for that `Copy`'s own operand and result.
fn bind_copy(
    inst: &X86ISelInst,
    source_id: SourceInstId,
    source: &LirSourceInst,
    bindings: &X86SourceOperandBindings,
) -> Option<X86OperandBindingSchema> {
    // SOURCE OPERATION. Checked by EQUALITY against the replayed opcode, exactly
    // as every other family in this module checks its own, and BEFORE anything
    // about the emission is consulted. Pinned by
    // `a_mov_stamped_from_an_isub_never_binds` and, end to end through the real
    // selector and the real verifier, by
    // `x86_mov_stamped_from_an_isub_earns_no_source_binding`.
    if source.opcode != LirOpcode::Copy {
        return None;
    }
    // ARITY. A `Copy` takes one value and produces one. Any other shape is a
    // different instruction wearing the opcode, and its operands would not be
    // positionally determined.
    if source.args.len() != 1 || source.results.len() != 1 || inst.operands.len() != 2 {
        return None;
    }
    // PERMITTED FORM, which also fixes the width both carriers must have.
    let width = copy_form_bits(inst.opcode)?;
    if operand_width(&inst.operands[0])? != width || operand_width(&inst.operands[1])? != width {
        return None;
    }
    // FRESH DESTINATION. An SSA result is a fresh value, so a pre-regalloc copy
    // whose destination IS its source register is not the renaming this schema
    // describes.
    if inst.operands[0] == inst.operands[1] {
        return None;
    }
    // BOTH ENDS, POSITIONALLY. The emitted source operand is `σ` of the `Copy`'s
    // one operand and the emitted destination is `σ` of its one result — no
    // search over the source operand list, because with one operand there is
    // nothing to search and a match anywhere else would not identify a slot.
    if !operand_matches(
        bindings,
        source_id,
        source.args[0],
        &inst.operands[1],
        width,
    ) || !operand_matches(
        bindings,
        source_id,
        source.results[0],
        &inst.operands[0],
        width,
    ) {
        return None;
    }
    Some(X86OperandBindingSchema::ResultDefiningCopy)
}

/// `[dst, src1, src2]` integer or bitwise binary ALU, REGISTER form only.
fn bind_binary(
    inst: &X86ISelInst,
    source_id: SourceInstId,
    source: &LirSourceInst,
    bindings: &X86SourceOperandBindings,
    reconstructed_op: &LirOpcode,
) -> Option<X86OperandBindingSchema> {
    // SOURCE-OPERATION EXACTNESS. The reconstruction put `reconstructed_op` on
    // the trust-ir side by reading the EMITTED opcode; requiring it to equal the
    // REPLAYED source opcode is what makes the obligation a statement about this
    // lowering. Equivalent to rebuilding the source side from `source.opcode`,
    // and cheaper: under this equality the two are the same expression.
    if &source.opcode != reconstructed_op {
        return None;
    }
    if inst.operands.len() != 3 || source.args.len() != 2 || source.results.len() != 1 {
        return None;
    }
    let width = crate::x86_64_function_verifier::x86_operand_reg_width_bits(&inst.operands[0])?;
    if !operand_matches(
        bindings,
        source_id,
        source.results[0],
        &inst.operands[0],
        width,
    ) || !operand_matches(
        bindings,
        source_id,
        source.args[0],
        &inst.operands[1],
        width,
    ) {
        return None;
    }
    match &inst.operands[2] {
        // RR form: the second source is a register the recorded correspondence
        // must name for the source instruction's second operand.
        operand @ (X86ISelOperand::VReg(_) | X86ISelOperand::PReg(_)) => {
            if operand_matches(bindings, source_id, source.args[1], operand, width) {
                Some(X86OperandBindingSchema::BinaryAlu)
            } else {
                None
            }
        }
        // FOLDED-IMMEDIATE (RI) FORM: REFUSED, and the refusal is the point.
        //
        // The reconstruction bakes the EMITTED immediate into its trust-ir side
        // as a constant. Binding it would mean requiring the emitted `Imm` to
        // equal the operand `σ` recorded for the source instruction's second
        // argument — but what `σ` recorded there IS the immediate ISel chose when
        // it folded the constant. The check would compare selection's own
        // output against itself and could not disagree, so the obligation would
        // read `bvadd(a, k) == ADD r, k` for whatever `k` selection picked, and
        // a folded 7 in place of the source `Iconst`'s 5 would still bind.
        //
        // Crediting this needs a verify-side RE-DERIVATION of the constant from
        // the replayed LIR — the `Iconst` the source operand denotes, read out of
        // the replayed function and compared against the emitted `Imm` — which
        // is the same independent-re-derivation discipline the GEP families use
        // for a displacement and a scale. Until that exists the folded-immediate
        // forms keep their reconstructed `Exhaustive`/`Statistical` tier and the
        // promotion gate keeps refusing them.
        _ => None,
    }
}

/// `[dst, src1, src2]` scalar floating-point binary.
fn bind_fp_binary(
    inst: &X86ISelInst,
    source_id: SourceInstId,
    source: &LirSourceInst,
    bindings: &X86SourceOperandBindings,
    reconstructed_op: &LirOpcode,
) -> Option<X86OperandBindingSchema> {
    if &source.opcode != reconstructed_op {
        return None;
    }
    if inst.operands.len() != 3 || source.args.len() != 2 || source.results.len() != 1 {
        return None;
    }
    let width = crate::x86_64_function_verifier::x86_fp_scalar_width(&inst.operands[0])?;
    let bound = operand_matches(
        bindings,
        source_id,
        source.results[0],
        &inst.operands[0],
        width,
    ) && operand_matches(
        bindings,
        source_id,
        source.args[0],
        &inst.operands[1],
        width,
    ) && operand_matches(
        bindings,
        source_id,
        source.args[1],
        &inst.operands[2],
        width,
    );
    bound.then_some(X86OperandBindingSchema::FpBinary)
}

/// `[dst, src]` integer unary (`Ineg` / `Bnot`).
fn bind_unary(
    inst: &X86ISelInst,
    source_id: SourceInstId,
    source: &LirSourceInst,
    bindings: &X86SourceOperandBindings,
    reconstructed_op: &LirOpcode,
) -> Option<X86OperandBindingSchema> {
    if &source.opcode != reconstructed_op {
        return None;
    }
    if inst.operands.len() != 2 || source.args.len() != 1 || source.results.len() != 1 {
        return None;
    }
    let width = crate::x86_64_function_verifier::x86_operand_reg_width_bits(&inst.operands[0])?;
    let bound = operand_matches(
        bindings,
        source_id,
        source.results[0],
        &inst.operands[0],
        width,
    ) && operand_matches(
        bindings,
        source_id,
        source.args[0],
        &inst.operands[1],
        width,
    );
    bound.then_some(X86OperandBindingSchema::UnaryAlu)
}

/// `[dst, MemAddr { base, 0 }]` scalar load.
///
/// `select_memory_load` emits exactly `MemAddr { base: <the operand the address
/// value resolved to>, disp: 0 }`, so the whole address-mode operand is
/// structurally determined by `σ(address)`. Requiring the EMITTED operand to
/// equal that reconstruction leaves no room for a folded displacement or a
/// substituted base.
///
/// A folded effective address (`[base + field_offset]`, which the GEP families
/// below produce as their own instruction) is NOT this shape and is refused
/// here: the displacement would not be determined by any operand of this source
/// instruction.
fn bind_mem_load(
    inst: &X86ISelInst,
    source_id: SourceInstId,
    source: &LirSourceInst,
    bindings: &X86SourceOperandBindings,
    load_bits: u32,
) -> Option<X86OperandBindingSchema> {
    let ty = match &source.opcode {
        LirOpcode::Load { ty, .. } | LirOpcode::VolatileLoad { ty, .. } => ty,
        _ => return None,
    };
    if inst.operands.len() != 2 || source.args.len() != 1 || source.results.len() != 1 {
        return None;
    }
    // The opcode fixes the ACCESS width; the replayed load must declare it, so a
    // byte load cannot be credited for a word source access or the reverse.
    if ty.bits() != load_bits {
        return None;
    }
    // The loaded value's recorded type is the ACCESS type, which the check above
    // already tied to the opcode's `load_bits`. The destination REGISTER is a
    // carrier that may be wider (an `i8` load lands in a `Gpr32` carrier), and
    // the reconstruction models that zero-fill itself, so the carrier width is
    // not what the recorded type must match.
    if !operand_matches(
        bindings,
        source_id,
        source.results[0],
        &inst.operands[0],
        load_bits,
    ) {
        return None;
    }
    // A destination whose carrier cannot hold the access is malformed.
    if operand_width(&inst.operands[0])? < load_bits {
        return None;
    }
    let (address, _) = bound_operand(bindings, source_id, source.args[0])?;
    let expected = X86ISelOperand::MemAddr {
        base: Box::new(address.clone()),
        disp: 0,
    };
    (inst.operands[1] == expected).then_some(X86OperandBindingSchema::ScalarLoadAtBoundAddress)
}

/// `[MemAddr { base, 0 }, value]` scalar store. LIR `Store` args are
/// `[value, address]`.
fn bind_mem_store(
    inst: &X86ISelInst,
    source_id: SourceInstId,
    source: &LirSourceInst,
    bindings: &X86SourceOperandBindings,
    store_bits: u32,
) -> Option<X86OperandBindingSchema> {
    let ty = match &source.opcode {
        LirOpcode::Store { ty, .. } | LirOpcode::VolatileStore { ty, .. } => ty,
        _ => return None,
    };
    if inst.operands.len() != 2 || source.args.len() != 2 || !source.results.is_empty() {
        return None;
    }
    if ty.bits() != store_bits {
        return None;
    }
    let (address, _) = bound_operand(bindings, source_id, source.args[1])?;
    let expected = X86ISelOperand::MemAddr {
        base: Box::new(address.clone()),
        disp: 0,
    };
    if inst.operands[0] != expected {
        return None;
    }
    // The stored register must be the operand the VALUE operand resolved to, at
    // the ACCESS type (the carrier may be wider; the reconstruction truncates to
    // `store_bits` itself). A store whose value went through a width conversion
    // first emits a different register here and is refused.
    if operand_width(&inst.operands[1])? < store_bits {
        return None;
    }
    operand_matches(
        bindings,
        source_id,
        source.args[0],
        &inst.operands[1],
        store_bits,
    )
    .then_some(X86OperandBindingSchema::ScalarStoreAtBoundAddress)
}

/// `Lea`/`LeaSib` address computation for the two GEP source families.
///
/// This is the one place where a DISPLACEMENT or a SCALE is bound, and it is
/// bound by re-deriving it INDEPENDENTLY from the declared aggregate type that
/// the replayed source opcode carries (`Type::offset_of` for a field,
/// `Type::bytes` for an element), never by accepting the emitted constant. A
/// wrong field offset or a wrong element scale therefore withholds the binding
/// exactly as a wrong register would.
///
/// Every other `Lea` is refused, and the largest group of those is deliberate:
/// `allocate_stack_slot_addr` emits `Lea dst, [StackSlot(n) + 0]` for a slot
/// ISel itself allocated, which no operand of any source instruction determines.
/// Binding it would mean accepting the selector's own choice as its own
/// evidence.
fn bind_effective_address(
    inst: &X86ISelInst,
    source_id: SourceInstId,
    source: &LirSourceInst,
    bindings: &X86SourceOperandBindings,
    has_index: bool,
) -> Option<X86OperandBindingSchema> {
    if inst.operands.len() != 2 || source.results.len() != 1 {
        return None;
    }
    let dst_width = crate::x86_64_function_verifier::x86_operand_reg_width_bits(&inst.operands[0])?;
    if !operand_matches(
        bindings,
        source_id,
        source.results[0],
        &inst.operands[0],
        dst_width,
    ) {
        return None;
    }
    match (&source.opcode, has_index) {
        (
            LirOpcode::StructGep {
                struct_ty,
                field_index,
            },
            false,
        ) => {
            if source.args.len() != 1 {
                return None;
            }
            // INDEPENDENT layout re-derivation from the declared struct type.
            // `select_struct_gep` emits a plain `MovRR` when the offset is zero,
            // so a zero displacement here is not this family's shape.
            let offset = struct_ty.offset_of(*field_index as usize)?;
            let disp = i32::try_from(offset).ok()?;
            if disp == 0 {
                return None;
            }
            let (base, _) = bound_operand(bindings, source_id, source.args[0])?;
            let expected = X86ISelOperand::MemAddr {
                base: Box::new(base.clone()),
                disp,
            };
            (inst.operands[1] == expected).then_some(X86OperandBindingSchema::FieldAddress)
        }
        (LirOpcode::ArrayGep { elem_ty }, true) => {
            if source.args.len() != 2 {
                return None;
            }
            // INDEPENDENT element-size re-derivation. Only the directly
            // encodable scales are this family's shape: `select_array_gep`
            // decomposes 3/5/9 into a SIB plus a second add, which is a
            // multi-instruction sequence this per-instruction schema does not
            // describe.
            let scale = u8::try_from(elem_ty.bytes()).ok()?;
            if !matches!(scale, 1 | 2 | 4 | 8) {
                return None;
            }
            let (base, _) = bound_operand(bindings, source_id, source.args[0])?;
            let (index, _) = bound_operand(bindings, source_id, source.args[1])?;
            let expected = X86ISelOperand::SibMemAddr {
                base: Box::new(base.clone()),
                index: Box::new(index.clone()),
                scale,
                disp: 0,
            };
            (inst.operands[1] == expected).then_some(X86OperandBindingSchema::ElementAddress)
        }
        _ => None,
    }
}

/// `[dst, src]` width-CHANGING sign/zero extend. The emitted opcode fixes both
/// widths, so the replayed `Sextend`/`Uextend` must declare exactly those.
fn bind_extend(
    inst: &X86ISelInst,
    source_id: SourceInstId,
    source: &LirSourceInst,
    bindings: &X86SourceOperandBindings,
    from_bits: u32,
    signed: bool,
) -> Option<X86OperandBindingSchema> {
    let (source_from, source_to) = match (&source.opcode, signed) {
        (LirOpcode::Sextend { from_ty, to_ty }, true)
        | (LirOpcode::Uextend { from_ty, to_ty }, false) => (from_ty, to_ty),
        _ => return None,
    };
    if inst.operands.len() != 2 || source.args.len() != 1 || source.results.len() != 1 {
        return None;
    }
    let to_bits = crate::x86_64_function_verifier::x86_operand_reg_width_bits(&inst.operands[0])?;
    // The emitted opcode's from/to widths ARE the obligation's widths; requiring
    // the replayed extend to declare the same pair is what rules out a
    // byte-extend bound to a halfword source (or a widening that drops bits).
    if source_from.bits() != from_bits || source_to.bits() != to_bits {
        return None;
    }
    // The extend's SOURCE register carries the value in its low `from_bits`; its
    // carrier is the emitted register class, so the recorded source type is
    // checked at `from_bits`, not at the carrier width.
    let bound = operand_matches(
        bindings,
        source_id,
        source.results[0],
        &inst.operands[0],
        to_bits,
    ) && operand_matches(
        bindings,
        source_id,
        source.args[0],
        &inst.operands[1],
        from_bits,
    );
    bound.then_some(X86OperandBindingSchema::Extend)
}

// ---------------------------------------------------------------------------
// TV-1 EXTENDED, ABI half: formal-argument moves
// ---------------------------------------------------------------------------

// (continued) A formal-argument ABI move carries
// `SyntheticReason::FormalArguments`, so it has no source instruction whose
// operands could be named — and the measured residual shows that every x86-64
// function taking a register argument emits one, so the source-instruction
// binding above cannot by itself remove a function's last statistical row.
//
// Its operands are nevertheless fully determined by the DECLARED signature,
// the DECLARED calling convention, and the parameter index. The section below
// re-derives the parameter's ABI location verify-side from the replayed LIR
// function's signature and the shared `trust_cg_ir::x86_64_regs` argument
// tables, and requires the emitted move to read exactly that register.
//
// DECLARED INPUTS, stated plainly: the signature and the calling convention
// are inputs to the compilation, not things this check establishes — exactly
// as the replayed LIR function is a declared input to TV-2. What is checked is
// that, GIVEN them, the emitted move reads the register the convention assigns
// and writes the operand selection recorded for that formal value, and that
// the move is bit-preserving at the parameter's width. Whether the convention
// itself is the right one for the target, and whether the caller honoured it,
// are the call/return ABI obligations (`call_lowering_proofs`, the SysV ABI
// canaries), not this credit.

use trust_cg_ir::x86_64_regs::{X86_ARG_GPRS, X86_ARG_XMMS, X86PReg, x86_gpr64_to_gpr32};
use trust_cg_lower::function::Signature;
use trust_cg_lower::x86_64_isel::{
    X86CallAbi, X86FormalArgumentBindings, X86FormalArgumentLocation,
};

/// Windows x64 passes the first four arguments POSITIONALLY: argument `k` uses
/// integer register `k` or SSE register `k`, never a separate counter.
const WINDOWS_X64_ARG_GPRS: [X86PReg; 4] = [
    trust_cg_ir::x86_64_regs::RCX,
    trust_cg_ir::x86_64_regs::RDX,
    trust_cg_ir::x86_64_regs::R8,
    trust_cg_ir::x86_64_regs::R9,
];

/// The register class a SCALAR parameter type travels in, or `None` for every
/// type whose classification is not a single scalar register slot (aggregates,
/// `i128`, `f16`, SysV `V128` treated as a vector lane, anything else). `None`
/// makes the whole re-derivation refuse, because a type this function cannot
/// classify also consumes an unknown number of register slots.
fn scalar_param_class(ty: &trust_cg_lower::types::Type) -> Option<ScalarParamClass> {
    use trust_cg_lower::types::Type as T;
    match ty {
        T::B1 | T::I8 | T::I16 | T::I32 | T::I64 => Some(ScalarParamClass::Integer),
        T::F32 | T::F64 => Some(ScalarParamClass::Sse),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScalarParamClass {
    Integer,
    Sse,
}

/// The 32-bit alias of an argument GPR when the parameter travels in a 32-bit
/// carrier (`B1`/`I8`/`I16`/`I32` all do on x86-64), else the 64-bit register.
fn arg_gpr_for_type(gpr64: X86PReg, ty: &trust_cg_lower::types::Type) -> Option<X86PReg> {
    use trust_cg_lower::types::Type as T;
    match ty {
        T::B1 | T::I8 | T::I16 | T::I32 => x86_gpr64_to_gpr32(gpr64),
        T::I64 => Some(gpr64),
        _ => None,
    }
}

/// Re-derive, from the DECLARED signature and calling convention alone, the
/// register the convention assigns to scalar parameter `param_index`.
///
/// Returns `None` — refusing the binding — whenever the derivation is not
/// completely determined: any parameter at or before `param_index` that is not
/// a single-register scalar, an argument that lands on the stack instead, or a
/// parameter index past the end of the signature. Refusing is the safe answer:
/// it withholds a `Formal` credit, never grants one.
fn derived_formal_argument_register(
    params: &[trust_cg_lower::types::Type],
    param_index: usize,
    abi: X86CallAbi,
    sret_return: bool,
) -> Option<X86PReg> {
    let ty = params.get(param_index)?;
    let class = scalar_param_class(ty)?;
    match abi {
        X86CallAbi::WindowsX64 => {
            // POSITIONAL: every earlier parameter still consumes its own slot,
            // so only the index (plus the hidden sret pointer) matters — but an
            // earlier unclassifiable parameter could be passed by reference and
            // change nothing about the index, so they are still all required to
            // be scalars before this derivation is trusted.
            for earlier in &params[..param_index] {
                scalar_param_class(earlier)?;
            }
            let abi_index = param_index + usize::from(sret_return);
            if abi_index >= WINDOWS_X64_ARG_GPRS.len() {
                return None;
            }
            match class {
                ScalarParamClass::Integer => arg_gpr_for_type(WINDOWS_X64_ARG_GPRS[abi_index], ty),
                ScalarParamClass::Sse => X86_ARG_XMMS.get(abi_index).copied(),
            }
        }
        X86CallAbi::SystemV => {
            // SysV consumes the integer and SSE argument registers from two
            // INDEPENDENT counters, in parameter order. A parameter that does
            // not fit goes to the stack and its counter does not advance, so
            // there is no backfill.
            let mut gpr = usize::from(sret_return);
            let mut xmm = 0usize;
            for (index, earlier) in params.iter().enumerate() {
                let earlier_class = scalar_param_class(earlier)?;
                if index == param_index {
                    return match earlier_class {
                        ScalarParamClass::Integer => (gpr < X86_ARG_GPRS.len())
                            .then(|| arg_gpr_for_type(X86_ARG_GPRS[gpr], ty))?,
                        ScalarParamClass::Sse => X86_ARG_XMMS.get(xmm).copied(),
                    };
                }
                match earlier_class {
                    ScalarParamClass::Integer => {
                        if gpr < X86_ARG_GPRS.len() {
                            gpr += 1;
                        }
                    }
                    ScalarParamClass::Sse => {
                        if xmm < X86_ARG_XMMS.len() {
                            xmm += 1;
                        }
                    }
                }
            }
            None
        }
    }
}

/// Bind a `SyntheticReason::FormalArguments` register copy to the signature
/// parameter it materializes, or return `None` (leaving it Statistical).
///
/// The caller must already have established that `inst` is a reconstructable
/// register copy under an `X86SourceOp::CopyGpr`/`CopyXmm` reconstruction and
/// that `signature` is the replayed LIR function's declared signature.
pub(crate) fn bind_formal_argument_operands(
    inst: &X86ISelInst,
    signature: &Signature,
    bindings: &X86FormalArgumentBindings,
) -> Option<ExactSourceOperandBinding> {
    use crate::x86_64_function_verifier::{X86SourceOp, x86_opcode_to_source_op};

    if bindings.is_empty() || inst.operands.len() != 2 {
        return None;
    }
    // Only a register COPY. A stack-passed parameter is a memory LOAD whose
    // effective address has no operand schema here yet, so it keeps its
    // existing strength.
    match x86_opcode_to_source_op(inst.opcode)?.0 {
        X86SourceOp::CopyGpr | X86SourceOp::CopyXmm => {}
        _ => return None,
    }
    let X86ISelOperand::VReg(dst) = &inst.operands[0] else {
        return None;
    };
    let binding = bindings.get(*dst)?;
    let X86FormalArgumentLocation::Register(recorded) = binding.location else {
        return None;
    };

    // The emitted move must READ exactly the recorded register ...
    if inst.operands[1] != X86ISelOperand::PReg(recorded) {
        return None;
    }
    // ... the recorded parameter type must be the one the DECLARED signature
    // declares at that index ...
    if signature.params.get(binding.param_index as usize) != Some(&binding.ty) {
        return None;
    }
    // ... the register must be the one an INDEPENDENT re-derivation of the
    // convention assigns to that parameter ...
    if derived_formal_argument_register(
        &signature.params,
        binding.param_index as usize,
        binding.abi,
        binding.sret_return,
    ) != Some(recorded)
    {
        return None;
    }
    // ... and the move's width must be the parameter's carrier width, so a
    // narrow parameter cannot be credited by a wide move (or the reverse).
    let width = operand_width(&inst.operands[0])?;
    if operand_width(&inst.operands[1])? != width || binding.ty.bits() > width {
        return None;
    }
    Some(ExactSourceOperandBinding {
        schema: X86OperandBindingSchema::FormalArgumentRegisterCopy,
    })
}

// ---------------------------------------------------------------------------
// TV-1 EXTENDED, ABI half: return moves
// ---------------------------------------------------------------------------

// (continued) A RETURN move IS stamped with the LIR `Return` it lowers, so the
// value it copies is a recorded operand of that instruction and the source end
// binds. Its DESTINATION is a physical ABI register that no operand of the
// `Return` determines — and for a return move the destination is the whole
// claim: a `MOV` of the right value into the wrong register is a miscompilation
// that the `X == X` obligation cannot see. `bind_copy` therefore refuses the
// shape, and the section below binds the destination properly instead, by
// RE-DERIVING the return register from the replayed LIR function's DECLARED
// signature and the shared `trust_cg_ir::x86_64_regs` RETURN tables.
//
// This is the exact mirror of the formal-argument half above and carries the
// same declared-input boundary: the signature and the convention are inputs to
// the compilation, and what is checked is that GIVEN them the move writes the
// register the convention assigns to that return index and reads the operand
// selection recorded for that return value.
//
// WHY THE SYMMETRIC CASES ARE STILL REFUSED. An OUTGOING CALL ARGUMENT move
// would need the CALLEE's declared parameter types to derive its register, and a
// call RESULT move the callee's declared return types; this function's replayed
// signature contains neither. Deriving them from the argument or result values'
// own types — the only thing to hand — would assume the callee's declaration
// agrees with what this caller lowered against, which is the call ABI's
// obligation (`call_lowering_proofs`, the SysV canaries) and not a fact this
// module can check. They stay Statistical.

use trust_cg_ir::x86_64_regs::{
    X86_INTERNAL_RET_GPRS, X86_INTERNAL_RET_XMMS, X86_RET_GPRS, X86_RET_XMMS,
};
use trust_cg_lower::x86_64_isel::X86ReturnAbiBindings;

/// Re-derive, from the DECLARED return types and calling convention alone, the
/// register the convention assigns to scalar return value `return_index`.
///
/// Returns `None` — refusing the binding — whenever the derivation is not
/// completely determined: any return at or before `return_index` that is not a
/// single-register scalar (an aggregate, `i128`, `f16`, `V128`), a return index
/// past the end of the list, or a slot past the convention's return file.
/// Refusing withholds a `Formal` credit and never grants one.
///
/// Windows x64 returns a single value only (`X86_RET_GPRS[..1]` /
/// `X86_RET_XMMS[..1]`), which is why the file is sliced per convention rather
/// than shared. System V allocates from TrustCG's internal multi-result file
/// (`X86_INTERNAL_RET_GPRS` / `X86_INTERNAL_RET_XMMS`), whose first two
/// registers per class are the C file, so a C-shaped return derives exactly the
/// register it always did and a return past the C file derives its RCX..R9 /
/// XMM2..XMM7 slot from the same shared table the lowering reads.
fn derived_scalar_return_register(
    returns: &[trust_cg_lower::types::Type],
    return_index: usize,
    abi: X86CallAbi,
) -> Option<X86PReg> {
    let (ret_gprs, ret_xmms): (&[X86PReg], &[X86PReg]) = match abi {
        X86CallAbi::SystemV => (&X86_INTERNAL_RET_GPRS[..], &X86_INTERNAL_RET_XMMS[..]),
        X86CallAbi::WindowsX64 => (&X86_RET_GPRS[..1], &X86_RET_XMMS[..1]),
    };
    let ty = returns.get(return_index)?;
    let mut gpr = 0usize;
    let mut xmm = 0usize;
    for (index, earlier) in returns.iter().enumerate() {
        // An unclassifiable return anywhere at or before the index consumes an
        // unknown number of slots, so the derivation refuses rather than
        // guessing — exactly as `derived_formal_argument_register` does.
        let class = scalar_param_class(earlier)?;
        if index == return_index {
            return match class {
                ScalarParamClass::Integer => arg_gpr_for_type(*ret_gprs.get(gpr)?, ty),
                ScalarParamClass::Sse => ret_xmms.get(xmm).copied(),
            };
        }
        match class {
            ScalarParamClass::Integer => gpr += 1,
            ScalarParamClass::Sse => xmm += 1,
        }
    }
    None
}

/// Bind a RETURN ABI move to the signature return value it materializes, or
/// return `None` (leaving it Statistical).
///
/// The caller must already have established that `source` is the replayed LIR
/// instruction at `inst`'s stamped coordinates, that its TV-2 cross-check passed
/// under `Enforce`, and that `signature` is the replayed LIR function's declared
/// signature.
pub(crate) fn bind_return_abi_operands(
    inst: &X86ISelInst,
    source_id: SourceInstId,
    source: &LirSourceInst,
    signature: &Signature,
    bindings: &X86SourceOperandBindings,
    return_bindings: &X86ReturnAbiBindings,
) -> Option<ExactSourceOperandBinding> {
    use crate::x86_64_function_verifier::{X86SourceOp, x86_opcode_to_source_op};

    // A function built outside the selector records nothing: fail closed.
    if bindings.is_empty() || return_bindings.is_empty() {
        return None;
    }
    // SOURCE OPERATION, by equality and first, as everywhere else in this
    // module.
    if source.opcode != LirOpcode::Return {
        return None;
    }
    // Only a register COPY, and only in one of the identity forms a return move
    // is emitted as, which also fixes the width.
    match x86_opcode_to_source_op(inst.opcode)?.0 {
        X86SourceOp::CopyGpr | X86SourceOp::CopyXmm => {}
        _ => return None,
    }
    if inst.operands.len() != 2 {
        return None;
    }
    let width = copy_form_bits(inst.opcode)?;

    // The DESTINATION must be a physical register with a recorded return
    // binding.
    let X86ISelOperand::PReg(recorded) = &inst.operands[0] else {
        return None;
    };
    let binding = return_bindings.get(*recorded)?;
    let index = binding.return_index as usize;

    // The `Return` must carry one operand per declared return value, so the
    // index names a real operand of THIS instruction and not of some other
    // return shape.
    if source.args.len() != signature.returns.len() || !source.results.is_empty() {
        return None;
    }
    // The recorded return type must be the one the DECLARED signature declares
    // at that index — a disagreement about the very thing the width check and
    // the register derivation both read.
    if signature.returns.get(index) != Some(&binding.ty) {
        return None;
    }
    // The register must be the one an INDEPENDENT re-derivation of the
    // convention assigns to that return value. This is the check that makes a
    // return move refutable at all: a move of the right value into the wrong ABI
    // register refuses here, and the obligation could never have caught it.
    if derived_scalar_return_register(&signature.returns, index, binding.abi) != Some(*recorded) {
        return None;
    }
    // The emitted form's width must be the return value's carrier width, and
    // both operands must have it, so a narrow return cannot be credited by a
    // wide move or the reverse.
    if operand_width(&inst.operands[0])? != width
        || operand_width(&inst.operands[1])? != width
        || binding.ty.bits() > width
    {
        return None;
    }
    // SOURCE END: the read operand is `σ` of the `Return`'s operand at this same
    // index, at the declared return type's width. A move that returns the wrong
    // one of two return values refuses here.
    if !operand_matches(
        bindings,
        source_id,
        *source.args.get(index)?,
        &inst.operands[1],
        binding.ty.bits(),
    ) {
        return None;
    }
    Some(ExactSourceOperandBinding {
        schema: X86OperandBindingSchema::ReturnAbiRegisterCopy,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::provenance::SourceInstDigest;
    use trust_cg_ir::regs::{RegClass, VReg};
    use trust_cg_ir::x86_64_ops::X86Opcode;
    use trust_cg_ir::x86_64_regs::{RDI, RSI, XMM0, XMM1};
    use trust_cg_lower::instructions::Opcode as O;
    use trust_cg_lower::types::Type as T;
    use trust_cg_lower::x86_64_isel::{X86FormalArgumentBinding, X86ISelInst};

    use crate::provenance_xcheck::classify_lir_opcode;

    const SOURCE: SourceInstId = SourceInstId { block: 0, index: 3 };

    fn v32(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }

    fn source_inst(opcode: O, args: &[u32], results: &[u32]) -> LirSourceInst {
        LirSourceInst {
            digest: SourceInstDigest::compute(&format!("{opcode:?}"), args.len(), results.len()),
            class: classify_lir_opcode(&opcode),
            opcode_debug: format!("{opcode:?}"),
            opcode,
            cond_def_opcode: None,
            args: args.iter().map(|id| Value(*id)).collect(),
            results: results.iter().map(|id| Value(*id)).collect(),
            value_flow: Default::default(),
        }
    }

    /// `value -> (operand, I32)` pairs recorded under [`SOURCE`].
    fn bindings(pairs: &[(u32, X86ISelOperand)]) -> X86SourceOperandBindings {
        let mut table = X86SourceOperandBindings::default();
        for (value, operand) in pairs {
            table.record(SOURCE, Value(*value), operand, Some(&T::I32));
        }
        table
    }

    /// `dst = a + b`: LIR `Iadd` with args [10, 11] -> result 12, emitted
    /// `AddRR v2, v0, v1` with every slot bound.
    fn exact_iadd() -> (X86ISelInst, LirSourceInst, X86SourceOperandBindings) {
        let inst = X86ISelInst::new(X86Opcode::AddRR, vec![v32(2), v32(0), v32(1)]);
        let source = source_inst(O::Iadd, &[10, 11], &[12]);
        let table = bindings(&[(10, v32(0)), (11, v32(1)), (12, v32(2))]);
        (inst, source, table)
    }

    #[test]
    fn binary_alu_binds_when_every_operand_slot_is_the_recorded_one() {
        let (inst, source, table) = exact_iadd();
        let binding = bind_exact_source_operands(&inst, SOURCE, &source, &table)
            .expect("an exactly bound Iadd -> AddRR must bind");
        assert_eq!(binding.schema(), X86OperandBindingSchema::BinaryAlu);
    }

    /// THE degeneracy the reconstructed route refuses Formal for: the source
    /// side is inferred FROM the emitted opcode, so a wrong selection
    /// self-attests. Requiring the replayed opcode to EQUAL it is what closes
    /// that, so an `Isub` lowered to `AddRR` must not bind — no matter how
    /// perfectly its operands line up.
    #[test]
    fn binary_alu_refuses_a_source_opcode_the_emission_does_not_implement() {
        let (inst, _, table) = exact_iadd();
        let wrong_source = source_inst(O::Isub, &[10, 11], &[12]);
        assert!(bind_exact_source_operands(&inst, SOURCE, &wrong_source, &table).is_none());
    }

    #[test]
    fn binary_alu_refuses_swapped_source_operands() {
        // Emitted `SubRR v2, σ(b), σ(a)` — a swap that CHANGES the value of a
        // non-commutative op. Operand exactness is positional, so it refuses.
        let inst = X86ISelInst::new(X86Opcode::SubRR, vec![v32(2), v32(1), v32(0)]);
        let source = source_inst(O::Isub, &[10, 11], &[12]);
        let table = bindings(&[(10, v32(0)), (11, v32(1)), (12, v32(2))]);
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    #[test]
    fn binary_alu_refuses_a_destination_that_is_not_the_recorded_result() {
        let inst = X86ISelInst::new(X86Opcode::AddRR, vec![v32(9), v32(0), v32(1)]);
        let source = source_inst(O::Iadd, &[10, 11], &[12]);
        let table = bindings(&[(10, v32(0)), (11, v32(1)), (12, v32(2))]);
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    #[test]
    fn binary_alu_refuses_an_operand_with_no_recorded_correspondence() {
        let (inst, source, _) = exact_iadd();
        // `11` (the second source operand) was never recorded.
        let table = bindings(&[(10, v32(0)), (12, v32(2))]);
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    #[test]
    fn an_ambiguous_pair_is_never_bindable() {
        let (inst, source, _) = exact_iadd();
        let mut table = bindings(&[(10, v32(0)), (11, v32(1)), (12, v32(2))]);
        // The same value resolved to a SECOND, different operand while this one
        // source instruction was lowered.
        table.record(SOURCE, Value(11), &v32(7), Some(&T::I32));
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    #[test]
    fn binary_alu_refuses_a_width_the_recorded_source_type_does_not_have() {
        let (inst, source, _) = exact_iadd();
        let mut table = X86SourceOperandBindings::default();
        table.record(SOURCE, Value(10), &v32(0), Some(&T::I64));
        table.record(SOURCE, Value(11), &v32(1), Some(&T::I32));
        table.record(SOURCE, Value(12), &v32(2), Some(&T::I32));
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    #[test]
    fn a_result_defining_copy_binds_both_slots() {
        let inst = X86ISelInst::new(X86Opcode::MovRR32, vec![v32(1), v32(0)]);
        let source = source_inst(O::Copy, &[10], &[11]);
        let table = bindings(&[(10, v32(0)), (11, v32(1))]);
        let binding = bind_exact_source_operands(&inst, SOURCE, &source, &table)
            .expect("a result-defining copy must bind");
        assert_eq!(
            binding.schema(),
            X86OperandBindingSchema::ResultDefiningCopy
        );
    }

    /// THE HOLE FIX 1 CLOSES, at the unit level. The reconstruction reads its
    /// source operation off the EMITTED opcode, so a `MOV` arrives here claiming
    /// to be a copy whatever the replayed instruction is. Its operands line up
    /// perfectly — `σ(a)` in the source slot, `σ(dst)` in the destination — and
    /// TV-2 cannot object, because a move has no definite op class. If the schema
    /// did not check the replayed OPERATION, this machine `MOV` would earn
    /// `Formal` for an `Isub` it deleted.
    #[test]
    fn a_mov_stamped_from_an_isub_never_binds() {
        let inst = X86ISelInst::new(X86Opcode::MovRR32, vec![v32(2), v32(0)]);
        let source = source_inst(O::Isub, &[10, 11], &[12]);
        let table = bindings(&[(10, v32(0)), (11, v32(1)), (12, v32(2))]);
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    /// A RETURN-value move binds one end only, and the unbound end — the ABI
    /// register the value must land in — is the whole content of the claim. It
    /// earns nothing until that end is bound.
    #[test]
    fn a_return_value_copy_does_not_bind() {
        let inst = X86ISelInst::new(
            X86Opcode::MovRR32,
            vec![X86ISelOperand::PReg(trust_cg_ir::x86_64_regs::EAX), v32(0)],
        );
        let source = source_inst(O::Return, &[10], &[]);
        let table = bindings(&[(10, v32(0))]);
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    /// Symmetrically, a call's RESULT move: the register the value arrived in is
    /// unbound, and binding only the destination would credit a value read out
    /// of the wrong ABI register.
    #[test]
    fn a_call_result_copy_does_not_bind() {
        let inst = X86ISelInst::new(
            X86Opcode::MovRR32,
            vec![v32(3), X86ISelOperand::PReg(trust_cg_ir::x86_64_regs::EAX)],
        );
        let source = source_inst(O::Return, &[10], &[11]);
        let table = bindings(&[(10, v32(0)), (11, v32(3))]);
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    /// Even under a genuine `Copy`, a source slot that is not the recorded
    /// operand refuses — the positional check is over `σ`, not over "some
    /// operand of the instruction".
    #[test]
    fn a_copy_from_an_operand_sigma_did_not_record_does_not_bind() {
        let inst = X86ISelInst::new(X86Opcode::MovRR32, vec![v32(1), v32(5)]);
        let source = source_inst(O::Copy, &[10], &[11]);
        let table = bindings(&[(10, v32(0)), (11, v32(1))]);
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    /// The emitted form FIXES the width: a 32-bit move cannot be credited for a
    /// 64-bit copy, even though both of its carriers agree with each other.
    #[test]
    fn a_copy_refuses_an_emitted_form_whose_width_is_not_the_carriers() {
        let inst = X86ISelInst::new(X86Opcode::MovRR32, vec![gpr64(1), gpr64(0)]);
        let source = source_inst(O::Copy, &[10], &[11]);
        let mut table = X86SourceOperandBindings::default();
        table.record(SOURCE, Value(10), &gpr64(0), Some(&T::I64));
        table.record(SOURCE, Value(11), &gpr64(1), Some(&T::I64));
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
        // The 64-bit form of the same emission, with everything else identical,
        // binds — so the refusal above is the width and nothing else.
        let wide = X86ISelInst::new(X86Opcode::MovRR, vec![gpr64(1), gpr64(0)]);
        assert_eq!(
            bind_exact_source_operands(&wide, SOURCE, &source, &table)
                .expect("the 64-bit form of a 64-bit copy must bind")
                .schema(),
            X86OperandBindingSchema::ResultDefiningCopy
        );
    }

    /// An SSA result is a fresh value, so a copy into its own source register is
    /// not the renaming this schema describes.
    #[test]
    fn a_copy_into_its_own_source_register_does_not_bind() {
        let inst = X86ISelInst::new(X86Opcode::MovRR32, vec![v32(0), v32(0)]);
        let source = source_inst(O::Copy, &[10], &[11]);
        let table = bindings(&[(10, v32(0)), (11, v32(0))]);
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    /// A `Copy` renames ONE value. An arity the opcode does not have is a
    /// different instruction wearing it, and its operands are not positionally
    /// determined.
    #[test]
    fn a_copy_with_a_shape_the_opcode_does_not_have_does_not_bind() {
        let inst = X86ISelInst::new(X86Opcode::MovRR32, vec![v32(2), v32(0)]);
        let source = source_inst(O::Copy, &[10, 11], &[12]);
        let table = bindings(&[(10, v32(0)), (11, v32(1)), (12, v32(2))]);
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    /// FOLDED-IMMEDIATE ALU: refused, because the only thing an immediate check
    /// could compare the emitted `Imm` against is the immediate SELECTION itself
    /// recorded — selection's own output, which cannot disagree with it. The RR
    /// form of the same source instruction still binds, so this is the immediate
    /// slot and nothing else.
    #[test]
    fn a_folded_immediate_alu_form_does_not_bind() {
        let inst = X86ISelInst::new(
            X86Opcode::AddRI,
            vec![v32(2), v32(0), X86ISelOperand::Imm(7)],
        );
        let source = source_inst(O::Iadd, &[10, 11], &[12]);
        let mut table = bindings(&[(10, v32(0)), (12, v32(2))]);
        table.record(SOURCE, Value(11), &X86ISelOperand::Imm(7), Some(&T::I32));
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    #[test]
    fn an_extend_refuses_widths_the_replayed_extend_does_not_declare() {
        let inst = X86ISelInst::new(X86Opcode::Movsx, vec![gpr64(1), v32(0)]);
        // MOVSXD is always i32 -> i64; a replayed i16 -> i64 extend is a
        // different theorem.
        let source = source_inst(
            O::Sextend {
                from_ty: T::I16,
                to_ty: T::I64,
            },
            &[10],
            &[11],
        );
        let mut table = X86SourceOperandBindings::default();
        table.record(SOURCE, Value(10), &v32(0), Some(&T::I32));
        table.record(SOURCE, Value(11), &gpr64(1), Some(&T::I64));
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    fn gpr64(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    /// `σ` over GPR64 operands at `I64`, for the address-carrying families.
    fn addr_bindings(pairs: &[(u32, X86ISelOperand)]) -> X86SourceOperandBindings {
        let mut table = X86SourceOperandBindings::default();
        for (value, operand) in pairs {
            table.record(SOURCE, Value(*value), operand, Some(&T::I64));
        }
        table
    }

    fn mem(base: X86ISelOperand, disp: i32) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(base),
            disp,
        }
    }

    // -- memory --------------------------------------------------------------

    #[test]
    fn a_scalar_load_binds_its_address_and_result_operands() {
        let inst = X86ISelInst::new(X86Opcode::MovRM, vec![gpr64(1), mem(gpr64(0), 0)]);
        let source = source_inst(
            O::Load {
                ty: T::I64,
                align: None,
            },
            &[10],
            &[11],
        );
        let table = addr_bindings(&[(10, gpr64(0)), (11, gpr64(1))]);
        let binding = bind_exact_source_operands(&inst, SOURCE, &source, &table)
            .expect("a disp-0 load at the bound address must bind");
        assert_eq!(
            binding.schema(),
            X86OperandBindingSchema::ScalarLoadAtBoundAddress
        );
    }

    /// A FOLDED displacement is not determined by any operand of the load, so
    /// the binding is refused rather than accepting the emitted constant.
    #[test]
    fn a_scalar_load_refuses_a_folded_displacement() {
        let inst = X86ISelInst::new(X86Opcode::MovRM, vec![gpr64(1), mem(gpr64(0), 8)]);
        let source = source_inst(
            O::Load {
                ty: T::I64,
                align: None,
            },
            &[10],
            &[11],
        );
        let table = addr_bindings(&[(10, gpr64(0)), (11, gpr64(1))]);
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    /// The opcode fixes the access width; a source load of a different width is
    /// a different theorem.
    #[test]
    fn a_scalar_load_refuses_an_access_width_the_source_does_not_declare() {
        let inst = X86ISelInst::new(X86Opcode::MovRM32, vec![v32(1), mem(gpr64(0), 0)]);
        let source = source_inst(
            O::Load {
                ty: T::I64,
                align: None,
            },
            &[10],
            &[11],
        );
        let mut table = X86SourceOperandBindings::default();
        table.record(SOURCE, Value(10), &gpr64(0), Some(&T::I64));
        table.record(SOURCE, Value(11), &v32(1), Some(&T::I32));
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    /// LIR `Store` args are `[value, address]`; binding them in the emitted
    /// `[MemAddr, value]` order is the whole point of a positional schema.
    #[test]
    fn a_scalar_store_binds_its_address_and_value_operands() {
        let inst = X86ISelInst::new(X86Opcode::MovMR, vec![mem(gpr64(0), 0), gpr64(2)]);
        let source = source_inst(
            O::Store {
                ty: T::I64,
                align: None,
            },
            &[12, 10],
            &[],
        );
        let table = addr_bindings(&[(10, gpr64(0)), (12, gpr64(2))]);
        let binding = bind_exact_source_operands(&inst, SOURCE, &source, &table)
            .expect("a disp-0 store at the bound address must bind");
        assert_eq!(
            binding.schema(),
            X86OperandBindingSchema::ScalarStoreAtBoundAddress
        );
    }

    /// Swapping the store's value and address operands must refute, not bind.
    #[test]
    fn a_scalar_store_refuses_swapped_value_and_address() {
        let inst = X86ISelInst::new(X86Opcode::MovMR, vec![mem(gpr64(2), 0), gpr64(0)]);
        let source = source_inst(
            O::Store {
                ty: T::I64,
                align: None,
            },
            &[12, 10],
            &[],
        );
        let table = addr_bindings(&[(10, gpr64(0)), (12, gpr64(2))]);
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    /// A narrow access lands in a WIDER carrier, and the recorded type is the
    /// access type — so the schema must compare against the access width, not
    /// the destination register. The selector's zero-extending load
    /// (`movzx r32, m8`) binds exactly as the merging one does.
    #[test]
    fn a_narrow_load_binds_against_the_access_width_not_the_carrier() {
        for opcode in [X86Opcode::MovRM8, X86Opcode::MovzxRM8] {
            let inst = X86ISelInst::new(opcode, vec![v32(1), mem(gpr64(0), 0)]);
            let source = source_inst(
                O::Load {
                    ty: T::I8,
                    align: None,
                },
                &[10],
                &[11],
            );
            let mut table = X86SourceOperandBindings::default();
            table.record(SOURCE, Value(10), &gpr64(0), Some(&T::I64));
            table.record(SOURCE, Value(11), &v32(1), Some(&T::I8));
            let binding = bind_exact_source_operands(&inst, SOURCE, &source, &table)
                .unwrap_or_else(|| {
                    panic!(
                        "{opcode:?}: an i8 load into a Gpr32 carrier must bind at the access width"
                    )
                });
            assert_eq!(
                binding.schema(),
                X86OperandBindingSchema::ScalarLoadAtBoundAddress
            );
        }
    }

    /// The ALU families are the OPPOSITE case and must stay strict: a
    /// reconstruction of an `i8` add over `Gpr32` carriers is the 32-bit
    /// theorem, which does not establish the 8-bit source semantics. The
    /// carrier-hygiene hazard is exactly the high bits it leaves out.
    #[test]
    fn a_narrow_alu_operand_does_not_earn_the_wide_carrier_theorem() {
        let inst = X86ISelInst::new(X86Opcode::AddRR, vec![v32(2), v32(0), v32(1)]);
        let source = source_inst(O::Iadd, &[10, 11], &[12]);
        let mut table = X86SourceOperandBindings::default();
        for (value, operand) in [(10u32, v32(0)), (11, v32(1)), (12, v32(2))] {
            table.record(SOURCE, Value(value), &operand, Some(&T::I8));
        }
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    // -- effective addresses -------------------------------------------------

    fn two_i64_struct() -> T {
        T::Struct(vec![T::I64, T::I64])
    }

    #[test]
    fn a_field_address_binds_the_independently_derived_offset() {
        let inst = X86ISelInst::new(X86Opcode::Lea, vec![gpr64(1), mem(gpr64(0), 8)]);
        let source = source_inst(
            O::StructGep {
                struct_ty: two_i64_struct(),
                field_index: 1,
            },
            &[10],
            &[11],
        );
        let table = addr_bindings(&[(10, gpr64(0)), (11, gpr64(1))]);
        let binding = bind_exact_source_operands(&inst, SOURCE, &source, &table)
            .expect("field 1 of {i64,i64} is at offset 8");
        assert_eq!(binding.schema(), X86OperandBindingSchema::FieldAddress);
    }

    /// The displacement is RE-DERIVED from the declared struct type, never
    /// accepted from the emission: an offset that is not the field's refuses.
    #[test]
    fn a_field_address_refuses_a_displacement_the_layout_does_not_yield() {
        let inst = X86ISelInst::new(X86Opcode::Lea, vec![gpr64(1), mem(gpr64(0), 16)]);
        let source = source_inst(
            O::StructGep {
                struct_ty: two_i64_struct(),
                field_index: 1,
            },
            &[10],
            &[11],
        );
        let table = addr_bindings(&[(10, gpr64(0)), (11, gpr64(1))]);
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    #[test]
    fn an_element_address_binds_the_independently_derived_scale() {
        let inst = X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![
                gpr64(2),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(gpr64(0)),
                    index: Box::new(gpr64(1)),
                    scale: 8,
                    disp: 0,
                },
            ],
        );
        let source = source_inst(O::ArrayGep { elem_ty: T::I64 }, &[10, 11], &[12]);
        let table = addr_bindings(&[(10, gpr64(0)), (11, gpr64(1)), (12, gpr64(2))]);
        let binding = bind_exact_source_operands(&inst, SOURCE, &source, &table)
            .expect("an i64 element scale is 8");
        assert_eq!(binding.schema(), X86OperandBindingSchema::ElementAddress);
    }

    #[test]
    fn an_element_address_refuses_a_scale_the_element_type_does_not_yield() {
        let inst = X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![
                gpr64(2),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(gpr64(0)),
                    index: Box::new(gpr64(1)),
                    scale: 4,
                    disp: 0,
                },
            ],
        );
        let source = source_inst(O::ArrayGep { elem_ty: T::I64 }, &[10, 11], &[12]);
        let table = addr_bindings(&[(10, gpr64(0)), (11, gpr64(1)), (12, gpr64(2))]);
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    /// An ISel-allocated scratch slot address is determined by the selector's
    /// own slot choice, not by any operand of any source instruction, so it must
    /// never bind.
    #[test]
    fn a_stack_slot_scratch_address_never_binds() {
        let inst = X86ISelInst::new(
            X86Opcode::Lea,
            vec![gpr64(1), mem(X86ISelOperand::StackSlot(3), 0)],
        );
        let source = source_inst(
            O::StructGep {
                struct_ty: two_i64_struct(),
                field_index: 1,
            },
            &[10],
            &[11],
        );
        let table = addr_bindings(&[(10, gpr64(0)), (11, gpr64(1))]);
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
    }

    // -- formal-argument ABI moves -----------------------------------------

    fn signature(params: &[T]) -> Signature {
        Signature {
            params: params.to_vec(),
            returns: vec![T::I32],
        }
    }

    fn formal_bindings(
        dst: u32,
        param_index: u32,
        ty: T,
        location: X86FormalArgumentLocation,
    ) -> X86FormalArgumentBindings {
        let mut table = X86FormalArgumentBindings::default();
        table.record(
            VReg::new(dst, RegClass::Gpr32),
            X86FormalArgumentBinding {
                param_index,
                ty,
                location,
                abi: X86CallAbi::SystemV,
                sret_return: false,
            },
        );
        table
    }

    #[test]
    fn a_formal_argument_move_binds_the_register_the_convention_assigns() {
        let edi =
            trust_cg_ir::x86_64_regs::x86_gpr64_to_gpr32(RDI).expect("RDI has a 32-bit alias");
        let inst = X86ISelInst::new(X86Opcode::MovRR32, vec![v32(0), X86ISelOperand::PReg(edi)]);
        let table = formal_bindings(0, 0, T::I32, X86FormalArgumentLocation::Register(edi));
        let binding = bind_formal_argument_operands(&inst, &signature(&[T::I32]), &table)
            .expect("parameter 0 arrives in EDI under System V");
        assert_eq!(
            binding.schema(),
            X86OperandBindingSchema::FormalArgumentRegisterCopy
        );
    }

    #[test]
    fn a_formal_argument_move_refuses_a_register_the_convention_does_not_assign() {
        let esi =
            trust_cg_ir::x86_64_regs::x86_gpr64_to_gpr32(RSI).expect("RSI has a 32-bit alias");
        let inst = X86ISelInst::new(X86Opcode::MovRR32, vec![v32(0), X86ISelOperand::PReg(esi)]);
        // Selection CLAIMS parameter 0 arrived in ESI; the independent
        // re-derivation says EDI, so the binding is refused even though the
        // emitted move agrees with the claim.
        let table = formal_bindings(0, 0, T::I32, X86FormalArgumentLocation::Register(esi));
        assert!(bind_formal_argument_operands(&inst, &signature(&[T::I32]), &table).is_none());
    }

    #[test]
    fn a_formal_argument_move_refuses_a_type_the_signature_does_not_declare() {
        let edi =
            trust_cg_ir::x86_64_regs::x86_gpr64_to_gpr32(RDI).expect("RDI has a 32-bit alias");
        let inst = X86ISelInst::new(X86Opcode::MovRR32, vec![v32(0), X86ISelOperand::PReg(edi)]);
        let table = formal_bindings(0, 0, T::I32, X86FormalArgumentLocation::Register(edi));
        // The signature declares an I64 parameter 0; the recorded binding says
        // I32 — a disagreement about the very thing the width check needs.
        assert!(bind_formal_argument_operands(&inst, &signature(&[T::I64]), &table).is_none());
    }

    /// The SysV integer and SSE argument counters advance independently, so the
    /// SECOND integer parameter of `(f64, i32, i32)` is RDX's alias, not RSI's.
    #[test]
    fn the_sysv_derivation_advances_integer_and_sse_counters_independently() {
        assert_eq!(
            derived_formal_argument_register(
                &[T::F64, T::I32, T::I32],
                2,
                X86CallAbi::SystemV,
                false
            ),
            trust_cg_ir::x86_64_regs::x86_gpr64_to_gpr32(trust_cg_ir::x86_64_regs::RSI)
        );
        assert_eq!(
            derived_formal_argument_register(&[T::F64, T::F32], 1, X86CallAbi::SystemV, false),
            Some(XMM1)
        );
        assert_eq!(
            derived_formal_argument_register(&[T::F64], 0, X86CallAbi::SystemV, false),
            Some(XMM0)
        );
    }

    /// A hidden sret return pointer consumes the first integer argument
    /// register, so parameter 0 is RSI's alias, not RDI's.
    #[test]
    fn the_sysv_derivation_accounts_for_a_hidden_sret_pointer() {
        assert_eq!(
            derived_formal_argument_register(&[T::I32], 0, X86CallAbi::SystemV, true),
            trust_cg_ir::x86_64_regs::x86_gpr64_to_gpr32(RSI)
        );
    }

    /// An unclassifiable parameter anywhere at or before the index consumes an
    /// unknown number of register slots, so the derivation refuses rather than
    /// guessing.
    #[test]
    fn the_sysv_derivation_refuses_a_signature_with_a_non_scalar_parameter() {
        assert_eq!(
            derived_formal_argument_register(&[T::I128, T::I32], 1, X86CallAbi::SystemV, false),
            None
        );
    }

    /// Past the sixth integer register the parameter is on the stack, which is
    /// not a register copy at all.
    #[test]
    fn the_sysv_derivation_refuses_a_stack_passed_parameter() {
        let params = vec![T::I64; 7];
        assert_eq!(
            derived_formal_argument_register(&params, 6, X86CallAbi::SystemV, false),
            None
        );
    }

    // -- return ABI moves ---------------------------------------------------

    use trust_cg_lower::x86_64_isel::X86ReturnAbiBinding;

    fn return_bindings(entries: &[(X86PReg, u32, T)]) -> X86ReturnAbiBindings {
        let mut table = X86ReturnAbiBindings::default();
        for (reg, return_index, ty) in entries {
            table.record(
                *reg,
                X86ReturnAbiBinding {
                    return_index: *return_index,
                    ty: ty.clone(),
                    abi: X86CallAbi::SystemV,
                },
            );
        }
        table
    }

    fn eax() -> X86PReg {
        trust_cg_ir::x86_64_regs::x86_gpr64_to_gpr32(trust_cg_ir::x86_64_regs::RAX)
            .expect("RAX has a 32-bit alias")
    }

    fn edx() -> X86PReg {
        trust_cg_ir::x86_64_regs::x86_gpr64_to_gpr32(trust_cg_ir::x86_64_regs::RDX)
            .expect("RDX has a 32-bit alias")
    }

    fn i32_return_signature(count: usize) -> Signature {
        Signature {
            params: vec![],
            returns: vec![T::I32; count],
        }
    }

    /// The schema `bind_copy` refuses and this one earns: the destination is
    /// BOUND, by re-deriving the return register from the declared signature.
    #[test]
    fn a_return_move_binds_the_register_the_convention_assigns() {
        let inst = X86ISelInst::new(
            X86Opcode::MovRR32,
            vec![X86ISelOperand::PReg(eax()), v32(0)],
        );
        let source = source_inst(O::Return, &[10], &[]);
        let table = bindings(&[(10, v32(0))]);
        let returns = return_bindings(&[(eax(), 0, T::I32)]);
        let binding = bind_return_abi_operands(
            &inst,
            SOURCE,
            &source,
            &i32_return_signature(1),
            &table,
            &returns,
        )
        .expect("return value 0 leaves in EAX under System V");
        assert_eq!(
            binding.schema(),
            X86OperandBindingSchema::ReturnAbiRegisterCopy
        );
    }

    /// THE REFUTATION THIS SCHEMA EXISTS FOR, and the one an operands-only copy
    /// credit could never make: the right value moved into the WRONG ABI
    /// register. Selection CLAIMS return 0 leaves in EDX; the independent
    /// re-derivation says EAX, so the binding is refused even though the emitted
    /// move agrees with the claim and the copied value is exactly right.
    #[test]
    fn a_return_move_refuses_a_register_the_convention_does_not_assign() {
        let inst = X86ISelInst::new(
            X86Opcode::MovRR32,
            vec![X86ISelOperand::PReg(edx()), v32(0)],
        );
        let source = source_inst(O::Return, &[10], &[]);
        let table = bindings(&[(10, v32(0))]);
        let returns = return_bindings(&[(edx(), 0, T::I32)]);
        assert!(
            bind_return_abi_operands(
                &inst,
                SOURCE,
                &source,
                &i32_return_signature(1),
                &table,
                &returns
            )
            .is_none()
        );
    }

    /// With TWO return values the index is load-bearing: the move into EDX must
    /// copy the SECOND returned operand, not the first.
    #[test]
    fn a_return_move_refuses_the_wrong_return_value_for_its_register() {
        let source = source_inst(O::Return, &[10, 11], &[]);
        let table = bindings(&[(10, v32(0)), (11, v32(1))]);
        let returns = return_bindings(&[(eax(), 0, T::I32), (edx(), 1, T::I32)]);
        let faithful = X86ISelInst::new(
            X86Opcode::MovRR32,
            vec![X86ISelOperand::PReg(edx()), v32(1)],
        );
        assert_eq!(
            bind_return_abi_operands(
                &faithful,
                SOURCE,
                &source,
                &i32_return_signature(2),
                &table,
                &returns
            )
            .expect("return value 1 leaves in EDX under System V")
            .schema(),
            X86OperandBindingSchema::ReturnAbiRegisterCopy
        );
        // Same register, the OTHER return value: refused.
        let swapped = X86ISelInst::new(
            X86Opcode::MovRR32,
            vec![X86ISelOperand::PReg(edx()), v32(0)],
        );
        assert!(
            bind_return_abi_operands(
                &swapped,
                SOURCE,
                &source,
                &i32_return_signature(2),
                &table,
                &returns
            )
            .is_none()
        );
    }

    /// A signature that contradicts the recorded return type refuses: the type
    /// is what both the width check and the register derivation read.
    #[test]
    fn a_return_move_refuses_a_type_the_signature_does_not_declare() {
        let inst = X86ISelInst::new(
            X86Opcode::MovRR32,
            vec![X86ISelOperand::PReg(eax()), v32(0)],
        );
        let source = source_inst(O::Return, &[10], &[]);
        let table = bindings(&[(10, v32(0))]);
        let returns = return_bindings(&[(eax(), 0, T::I32)]);
        let signature = Signature {
            params: vec![],
            returns: vec![T::I64],
        };
        assert!(
            bind_return_abi_operands(&inst, SOURCE, &source, &signature, &table, &returns)
                .is_none()
        );
    }

    /// A `Return` whose operand count does not match the declared return count
    /// is not the shape this schema indexes into.
    #[test]
    fn a_return_move_refuses_an_operand_count_the_signature_does_not_declare() {
        let inst = X86ISelInst::new(
            X86Opcode::MovRR32,
            vec![X86ISelOperand::PReg(eax()), v32(0)],
        );
        let source = source_inst(O::Return, &[10, 11], &[]);
        let table = bindings(&[(10, v32(0)), (11, v32(1))]);
        let returns = return_bindings(&[(eax(), 0, T::I32)]);
        assert!(
            bind_return_abi_operands(
                &inst,
                SOURCE,
                &source,
                &i32_return_signature(1),
                &table,
                &returns
            )
            .is_none()
        );
    }

    /// An OUTGOING-ARGUMENT move is refused by both binders and that is the
    /// design: `bind_copy` will not credit one end, and the return binder does
    /// not apply because the source instruction is not a `Return`. Deriving an
    /// argument register would need the CALLEE's declared parameter types.
    #[test]
    fn an_outgoing_argument_move_is_refused_by_both_binders() {
        let inst = X86ISelInst::new(
            X86Opcode::MovRR32,
            vec![
                X86ISelOperand::PReg(
                    trust_cg_ir::x86_64_regs::x86_gpr64_to_gpr32(RDI).expect("EDI"),
                ),
                v32(0),
            ],
        );
        let source = source_inst(
            O::Call {
                name: "callee".to_string(),
                binding: Default::default(),
            },
            &[10],
            &[11],
        );
        let table = bindings(&[(10, v32(0)), (11, v32(1))]);
        let returns = return_bindings(&[(eax(), 0, T::I32)]);
        assert!(bind_exact_source_operands(&inst, SOURCE, &source, &table).is_none());
        assert!(
            bind_return_abi_operands(
                &inst,
                SOURCE,
                &source,
                &i32_return_signature(1),
                &table,
                &returns
            )
            .is_none()
        );
    }

    /// The SysV return file is `RAX:RDX` / `XMM0:XMM1` with independent
    /// counters; Windows x64 returns a SINGLE value, so a second return value
    /// has no register at all.
    #[test]
    fn the_return_derivation_matches_each_convention_s_return_file() {
        assert_eq!(
            derived_scalar_return_register(&[T::I64, T::I64], 1, X86CallAbi::SystemV),
            Some(trust_cg_ir::x86_64_regs::RDX)
        );
        assert_eq!(
            derived_scalar_return_register(&[T::F64, T::F64], 1, X86CallAbi::SystemV),
            Some(XMM1)
        );
        assert_eq!(
            derived_scalar_return_register(&[T::I64, T::F64], 1, X86CallAbi::SystemV),
            Some(XMM0),
            "the integer and SSE return counters advance independently"
        );
        assert_eq!(
            derived_scalar_return_register(&[T::I64, T::I64], 1, X86CallAbi::WindowsX64),
            None,
            "Windows x64 returns one value"
        );
        assert_eq!(
            derived_scalar_return_register(&[T::I128], 0, X86CallAbi::SystemV),
            None,
            "an i128 return is the RAX:RDX pair, not a single register"
        );
        assert_eq!(
            derived_scalar_return_register(&[T::Struct(vec![T::I64])], 0, X86CallAbi::SystemV),
            None,
            "an aggregate return is not a single scalar register"
        );
    }

    /// Windows x64 is POSITIONAL: the second parameter uses the second integer
    /// register even when the first travelled in XMM0.
    #[test]
    fn the_windows_derivation_is_positional() {
        assert_eq!(
            derived_formal_argument_register(&[T::F64, T::I64], 1, X86CallAbi::WindowsX64, false),
            Some(trust_cg_ir::x86_64_regs::RDX)
        );
    }
}
