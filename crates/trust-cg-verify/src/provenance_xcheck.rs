// trust-cg-verify/provenance_xcheck.rs - TV-2 lowering-provenance cross-check
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! TV-2: per-instance certs CONSUME the TV-1 lowering provenance.
//!
//! Before this module, both function verifiers derived the "intended" source
//! op FROM the emitted opcode (`x86_opcode_to_source_op` /
//! `opcode_to_source_op`) — pure opcode self-consistency: an ISel that emitted
//! the WRONG opcode for a trust-ir instruction self-attested, because the spec
//! side was reconstructed from the very opcode under test (the codebase's own
//! TCB note named this gap).
//!
//! TV-1 (69feef0) stamped every ISel-emitted machine instruction with
//! [`LoweringProvenance`]: WHICH lowering-input (LIR) instruction the selector
//! was dispatching when it emitted the instruction, plus a
//! verifier-reproducible digest of that source instruction. This module makes
//! the verifiers CROSS-CHECK that claim against the replayed LIR function:
//!
//! 1. **Attribution integrity** — the stamped `(block, index)` must name a
//!    real instruction in the replayed LIR function (`DanglingSourceId`
//!    otherwise), and the recorded digest must equal that instruction's
//!    recomputed [`Instruction::lowering_digest`] (`DigestMismatch`
//!    otherwise). This binds the stamp to the actual source instruction.
//! 2. **Op-class consistency** — when the emitted opcode has a DEFINITE
//!    semantic class (exactly the opcodes the cert's reconstruction path
//!    already classifies via `x86_opcode_to_source_op` /
//!    `opcode_to_source_op`), that class must be a plausible constituent of a
//!    lowering of the claimed source instruction's op class
//!    ([`compatible`]). An `ADDSD` stamped as coming from an `Iadd`, an `IMUL`
//!    stamped as coming from an `Iadd`, or an `IDIV` stamped as coming from a
//!    `Load` means the ISel emitted an opcode that does not implement the
//!    trust-ir instruction it claims to come from => fail closed.
//!
//! # Scope and exemptions (deliberate)
//!
//! * `LoweringProvenance::Synthetic` (including `Unattributed`) instructions
//!   are EXEMPT: prologue/ABI glue, and everything created by downstream
//!   passes, carries no source claim to validate (TV-1's "under-attribution is
//!   legal, misattribution never" invariant). The check therefore can never
//!   false-fire on pass-created instructions.
//! * Operand-identity binding (provenance args vs `value_map` homes) is
//!   explicitly DEFERRED to TV-3's pre-pass walk: at the post-O1-pass cert
//!   point copy-prop/CSE rewrite operands, so operand identity is not stable
//!   here — but OPCODES of kept stamps are: the in-place opcode rewrites
//!   in the x86 pass window (`fold_unique_const_into_imm_forms`:
//!   AddRR→AddRI, SubRR→SubRI, AndRR→AndRI, ImulRR→ImulRRI, CmpRR→CmpRI) are
//!   class-preserving; `x86_strength_reduce` rewrites ImulRR/ImulRRI→MovRR
//!   in place (kept `Imul` stamp on an emitted register copy — glue-exempt,
//!   the exact x86 analogue of the AArch64 `strength_reduce` Mul→Copy
//!   below); and every pass-constructed instruction goes through
//!   `X86ISelInst::new`/`with_flags` which resets provenance to
//!   `UNATTRIBUTED` (verified: no `lowering_provenance` reference exists in
//!   `trust-cg-opt`). On AArch64 the in-place rewrites are
//!   `strength_reduce`/`sroa` Mul→Copy/MovR (Copy is glue-exempt),
//!   `addr_mode` load→load / store→store (class-preserving) and
//!   `loop_latch_layout` B↔BCond (no definite class), so kept stamps are
//!   class-stable there too.
//! * The COMPATIBILITY relation is deliberately coarse (op classes, not exact
//!   opcodes) and seeded permissively for multi-instruction expansions and
//!   idiom-anchor stamps (a fused sequence stamps its ANCHOR source
//!   instruction). Universal lowering glue — register copies, sign/zero
//!   re-extension of narrow carriers (#51/#66), spill/stack traffic, address
//!   materialization (`LEA`), constant materialization (including the
//!   `XOR r,r` zero idiom) — is exempt under every source. Mismatches are
//!   therefore strong evidence, and the matrix can only be extended by
//!   triage, never silently weakened.
//!
//! # Rollout (§2.4 gate protocol)
//!
//! `TCG_PROVENANCE_XCHECK` env: `off`/`0`, `warn`, `enforce`/`1`; unset uses
//! the per-arch default passed by the caller. x86-64 defaults to ENFORCE
//! (differential corpus + canary battery ran 0-hit in warn-only mode first);
//! AArch64 defaults to WARN-ONLY — the aarch64 differential corpus cannot
//! execute on the x86 validation host, so its flip is deferred to the
//! Apple-Silicon lane per the roadmap ownership map (§3: X2 designs, AS
//! wires/validates). `TCG_TRACE_PROVENANCE=1` prints a per-function summary.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

use trust_cg_ir::provenance::{LoweringProvenance, SourceInstDigest, SourceInstId};
use trust_cg_lower::instructions::Opcode as LirOpcode;

// ---------------------------------------------------------------------------
// Op classes
// ---------------------------------------------------------------------------

/// Coarse semantic class shared by the SOURCE side (classified from the real
/// LIR opcode via [`classify_lir_opcode`]) and the EMITTED side (classified
/// from the verifier's existing typed opcode→source-op maps).
///
/// Deliberately coarser than exact opcodes: a lowering legitimately expands
/// one source instruction into several machine instructions of related
/// classes, and O1 in-place peephole rewrites (register→immediate forms) must
/// stay inside one class. See [`compatible`] for the relation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpClass {
    /// Constant materialization (`Iconst`/`Fconst`/vector zeros).
    Const,
    /// Pure value copy / renaming.
    Copy,
    /// Integer add.
    IntAdd,
    /// Integer subtract.
    IntSub,
    /// Integer multiply (low half; includes immediate forms).
    IntMul,
    /// Integer negate.
    IntNeg,
    /// Integer divide / remainder.
    IntDiv,
    /// Scalar bitwise (AND/OR/XOR/NOT/BIC/ORN).
    Bitwise,
    /// Scalar shifts (left/logical-right/arithmetic-right).
    Shift,
    /// Sign/zero extension.
    Extend,
    /// Bit counting (popcount / leading / trailing zeros).
    BitCount,
    /// Bitfield extract/insert.
    BitField,
    /// Truncation / bitcast (same-size reinterpretation).
    Reinterpret,
    /// Integer comparison producing a flag/bool.
    IntCmp,
    /// Checked (overflow-reporting) integer arithmetic.
    Overflow,
    /// Conditional select / conditional move.
    Select,
    /// Fused multiply-add/sub (AArch64 `MADD`/`MSUB`) — emitted-side only;
    /// legitimately implements an `Iadd`/`Isub` anchor consuming an `Imul`.
    FusedMulAdd,
    /// Scalar FP arithmetic (add/sub/mul/div/min/max/sqrt/round/neg/abs).
    FpArith,
    /// Scalar FP comparison.
    FpCmp,
    /// FP<->int and FP<->FP format conversions.
    FpConvert,
    /// Packed integer arithmetic / compare / lane ops.
    VecInt,
    /// Packed full-width bitwise ops (also FP sign-mask idioms ANDPS/ANDPD).
    VecBitwise,
    /// Packed FP arithmetic.
    VecFp,
    /// Address computation (global/stack refs, GEPs; emitted LEA is glue).
    AddrCalc,
    /// Memory load.
    MemLoad,
    /// Memory store.
    MemStore,
    /// Atomic memory operation / fence.
    Atomic,
    /// Bulk memory intrinsic (memcpy/memmove/memset).
    MemIntrinsic,
    /// Direct/indirect/variadic call, invoke.
    CallLike,
    /// Branch / jump / switch / return / trap / EH control flow.
    ControlFlow,
    /// Proof-only guard carrier or runtime assertion.
    Guard,
}

/// Classify a LIR (lowering-input) opcode into its [`OpClass`].
///
/// EXHAUSTIVE by design (no wildcard): a new LIR opcode must be consciously
/// classified here before it compiles, so the cross-check can never silently
/// under-classify new surface.
pub fn classify_lir_opcode(opcode: &LirOpcode) -> OpClass {
    use LirOpcode as O;
    match opcode {
        O::Iconst { .. } | O::Iconst128 { .. } | O::Fconst { .. } | O::V4I32Zero | O::V2I64Zero => {
            OpClass::Const
        }
        O::Copy => OpClass::Copy,
        O::Iadd => OpClass::IntAdd,
        O::Isub => OpClass::IntSub,
        O::Imul => OpClass::IntMul,
        O::Ineg => OpClass::IntNeg,
        O::Udiv | O::Sdiv | O::Urem | O::Srem => OpClass::IntDiv,
        O::GuardDivZero { .. }
        | O::GuardNull { .. }
        | O::GuardShiftRange { .. }
        | O::GuardOverflow { .. }
        | O::GuardBoundsCheck { .. }
        | O::GuardBoundsCheckDyn { .. }
        | O::Assert => OpClass::Guard,
        O::Bnot | O::Band | O::Bor | O::Bxor | O::BandNot | O::BorNot => OpClass::Bitwise,
        O::CtPop => OpClass::BitCount,
        O::Fneg | O::Fabs | O::Fsqrt | O::Ffloor | O::Fceil | O::Ftrunc => OpClass::FpArith,
        O::Ishl | O::Ushr | O::Sshr => OpClass::Shift,
        O::Sextend { .. } | O::Uextend { .. } => OpClass::Extend,
        O::ExtractBits { .. } | O::SextractBits { .. } | O::InsertBits { .. } => OpClass::BitField,
        O::V4I32MaskExtract
        | O::V16I8MaskExtract
        | O::V8I16MaskExtract
        | O::V2I64MaskExtract { .. }
        | O::V4I32PackLanes
        | O::V2I64PackLanes
        | O::V16I8PackLanes
        | O::V8I16PackLanes
        | O::V8I8PackLanes
        | O::V2I64Add
        | O::V2I64Sub
        | O::V2I64Mul
        | O::V4I32Add
        | O::V4I32Sub
        | O::V4I32Mul
        | O::V16I8Add
        | O::V16I8Sub
        | O::V16I8Mul
        | O::V8I16Add
        | O::V8I16Sub
        | O::V8I16Mul
        | O::V16I8Icmp { .. }
        | O::V8I16Icmp { .. }
        | O::V4I32Icmp { .. }
        | O::V2I64Icmp { .. }
        | O::V8I8Icmp { .. }
        | O::V4I32ExtractLane { .. }
        | O::V4I32InsertLane { .. }
        | O::V2I64ExtractLane { .. }
        | O::V2I64InsertLane { .. }
        | O::V16I8ExtractLane { .. }
        | O::V16I8InsertLane { .. }
        | O::V8I16ExtractLane { .. }
        | O::V8I16InsertLane { .. } => OpClass::VecInt,
        O::V4F32Fadd
        | O::V4F32Fsub
        | O::V4F32Fmul
        | O::V4F32Fdiv
        | O::V2F64Fadd
        | O::V2F64Fsub
        | O::V2F64Fmul
        | O::V2F64Fdiv => OpClass::VecFp,
        O::Select { .. } => OpClass::Select,
        O::Icmp { .. } => OpClass::IntCmp,
        O::CheckedSadd
        | O::CheckedSsub
        | O::CheckedSmul
        | O::CheckedUadd
        | O::CheckedUsub
        | O::CheckedUmul => OpClass::Overflow,
        O::Fadd | O::Fsub | O::Fmul | O::Fdiv | O::Fma | O::Fmuladd | O::Fmin | O::Fmax => {
            OpClass::FpArith
        }
        O::Fcmp { .. } => OpClass::FpCmp,
        O::FcvtToInt { .. }
        | O::FcvtToUint { .. }
        | O::FcvtFromInt { .. }
        | O::FcvtFromUint { .. }
        | O::FPExt
        | O::FPTrunc => OpClass::FpConvert,
        O::Trunc { .. } | O::Bitcast { .. } => OpClass::Reinterpret,
        O::GlobalRef { .. }
        | O::ExternRef { .. }
        | O::TlsRef { .. }
        | O::StackAddr { .. }
        | O::StructGep { .. }
        | O::ArrayGep { .. } => OpClass::AddrCalc,
        O::Jump { .. }
        | O::Brif { .. }
        | O::Trap
        | O::Return
        | O::Switch { .. }
        | O::LandingPad { .. }
        | O::Resume => OpClass::ControlFlow,
        O::Call { .. } | O::CallIndirect | O::CallVariadic { .. } | O::Invoke { .. } => {
            OpClass::CallLike
        }
        O::Load { .. } | O::VolatileLoad { .. } => OpClass::MemLoad,
        O::Store { .. } | O::VolatileStore { .. } => OpClass::MemStore,
        O::AtomicLoad { .. }
        | O::AtomicStore { .. }
        | O::AtomicRmw { .. }
        | O::CmpXchg { .. }
        | O::Fence { .. } => OpClass::Atomic,
        O::Memcpy | O::Memmove | O::Memset => OpClass::MemIntrinsic,
    }
}

/// May a correct lowering of a SOURCE instruction of class `source` contain
/// an emitted machine instruction of DEFINITE class `emitted`?
///
/// Direction matters: `source` is the class of the LIR instruction the stamp
/// CLAIMS produced the emission; `emitted` is the definite semantic class the
/// cert path assigns to the emitted opcode. `false` == the emission cannot be
/// part of any correct lowering of that source => misattribution or wrong
/// lowering => fail closed (in enforce mode).
///
/// Seeding rationale (per family, verified against the in-tree ISels where
/// noted; the warn-only corpus run validates the whole matrix empirically):
///
/// * Universal glue (emitted `Copy`/`Extend`/`MemLoad`/`MemStore`/
///   `AddrCalc`/`Const`) is allowed under every source: operand staging,
///   narrow-carrier re-extension (#51/#66), spill/stack traffic, address and
///   constant materialization occur inside arbitrary lowerings. (The
///   per-arch emitted-class mappers additionally return `None` — fully
///   exempt — for these, plus the `XOR r,r` zero idiom.)
/// * `IntMul` allows `Shift` (power-of-two strength reduction) and `IntAdd`:
///   the i128 / wide multiply expansion accumulates partial products with
///   scalar `ADD`s (x86 `select_i128_mul` emits `mul,imul,imul,add,add`;
///   aarch64 uses the analogous `umulh`/`madd` decomposition), all stamped
///   with the `Imul` anchor. Triage-confirmed against the differential corpus
///   (82 i128-mul `IntAdd`-from-`Imul` emissions, all correct vs LLVM).
/// * `Shift` (`Ishl`/`Ushr`/`Sshr`) allows `IntSub` and `Select`: the i128
///   variable-shift branchless decomposition (`select_i128_shl`/`_shr` /
///   `emit_i128_var_shift`) computes `64 - count` and `count - 64` with
///   `SubRR` and selects the shifted half vs zero (for `count >= 64` /
///   `count == 0`) with `CMOV`, all stamped with the shift anchor.
///   Triage-confirmed against the corpus (580 `IntSub`/`Select`-from-shift
///   emissions across all three shift directions, all correct vs LLVM).
/// * `IntDiv` is permissive over the integer classes: division expansions
///   use bias adds, magic-number multiplies, sign fixups, shifts.
/// * `Overflow` (checked arithmetic) is permissive over the integer classes:
///   the division-free wide-mul expansion (#67) composes
///   mul/add/sub/shift/mask steps.
/// * `Icmp`/`Select`/branchy sources allow `IntSub` (x86 CMP's observable
///   value is the subtraction difference — mirrors `CmpRM => MemAlu{Isub}`)
///   and mask/blend bitwise forms; i128 compares compose XOR/OR limbs.
/// * FP sources allow `VecBitwise`/`Bitwise` (ANDPS/ANDPD/XORPS sign-mask
///   idioms for fabs/fneg and min/max NaN blends).
/// * Vector sources are permissive except `IntDiv`: baseline SSE2 lowerings
///   scalarize lanes through scalar mul/add/shift/pack sequences.
/// * `Const`/`Copy` sources allow NO definite-class emission: materializing
///   a constant or renaming a value never needs semantic arithmetic beyond
///   the exempted glue.
pub fn compatible(source: OpClass, emitted: OpClass) -> bool {
    use OpClass::*;
    // Emitted glue classes are legitimate constituents of ANY lowering. The
    // arch mappers normally pre-exempt these (return None), but keep the
    // relation total and safe if one ever reaches here.
    if matches!(
        emitted,
        Copy | Extend | MemLoad | MemStore | AddrCalc | Const
    ) {
        return true;
    }
    match source {
        Const | Copy => false,
        IntAdd => matches!(emitted, IntAdd | IntSub | FusedMulAdd),
        IntSub => matches!(emitted, IntSub | IntAdd | IntNeg | FusedMulAdd),
        IntMul => matches!(emitted, IntMul | Shift | IntAdd | FusedMulAdd),
        IntNeg => matches!(emitted, IntNeg | IntSub),
        IntDiv => matches!(
            emitted,
            IntDiv | IntMul | IntAdd | IntSub | IntNeg | Shift | Bitwise | FusedMulAdd | Select
        ),
        Bitwise => matches!(emitted, Bitwise | VecBitwise | IntNeg),
        Shift => matches!(emitted, Shift | Bitwise | IntSub | Select),
        Extend => matches!(emitted, Bitwise | Shift),
        BitCount => matches!(
            emitted,
            BitCount | Shift | Bitwise | IntAdd | IntSub | IntMul
        ),
        BitField => matches!(emitted, Shift | Bitwise),
        Reinterpret => matches!(emitted, Bitwise | Shift | FpConvert),
        IntCmp => matches!(emitted, IntSub | Bitwise | Select),
        Overflow => matches!(
            emitted,
            IntAdd | IntSub | IntMul | IntNeg | Shift | Bitwise | Select | FusedMulAdd
        ),
        Select => matches!(
            emitted,
            Select | IntSub | Bitwise | IntNeg | Shift | VecBitwise | FpArith
        ),
        FpArith => matches!(emitted, FpArith | FpCmp | VecBitwise | Bitwise | Select),
        FpCmp => matches!(emitted, FpCmp | FpArith | Bitwise | Select | IntSub),
        FpConvert => matches!(
            emitted,
            FpConvert | FpArith | FpCmp | IntAdd | IntSub | Shift | Bitwise | Select | VecBitwise
        ),
        VecInt | VecFp => !matches!(emitted, IntDiv),
        // IntSub belongs here for the same reason it is in the MemLoad/MemStore
        // rows: a StackAddr materializes as FP MINUS offset (`SubRI`) whenever
        // the slot sits below the frame pointer, so a subtract is a legitimate
        // address-calculation lowering, not a misattribution.
        AddrCalc => matches!(emitted, IntAdd | IntSub | IntMul | Shift),
        MemLoad | MemStore => matches!(
            emitted,
            IntAdd | IntSub | IntMul | Shift | Bitwise | VecInt | VecBitwise | VecFp
        ),
        Atomic => matches!(emitted, IntAdd | IntSub | IntNeg | Bitwise | Shift | Select),
        MemIntrinsic => matches!(
            emitted,
            IntAdd | IntSub | Shift | Bitwise | VecInt | VecBitwise | VecFp | Select
        ),
        CallLike | ControlFlow | Guard => {
            matches!(emitted, IntAdd | IntSub | Bitwise | Shift | Select)
        }
        // Emitted-only classes never appear in source position (no LIR opcode
        // classifies to them); conservatively reject if one ever does.
        FusedMulAdd | VecBitwise => false,
    }
}

// ---------------------------------------------------------------------------
// Replayed-LIR source index
// ---------------------------------------------------------------------------

/// One indexed LIR source instruction: recomputed digest + class + a display
/// name for diagnostics.
#[derive(Debug, Clone)]
pub struct LirSourceInst {
    /// Recomputed [`trust_cg_lower::instructions::Instruction::lowering_digest`].
    pub digest: SourceInstDigest,
    /// [`classify_lir_opcode`] of the instruction's opcode.
    pub class: OpClass,
    /// `Debug` rendering of the opcode, for mismatch diagnostics.
    pub opcode_debug: String,
}

/// Index of the EXACT LIR function that was handed to instruction selection,
/// keyed by TV-1 [`SourceInstId`] coordinates `(block, index)`.
///
/// This is the SPEC side of the cross-check: stamps are meaningful only
/// against the function ISel actually consumed (both ISels dispatch over
/// `Function::layout_order()` block instruction lists, which this index
/// replays 1:1).
#[derive(Debug, Clone)]
pub struct LirSourceIndex {
    /// Name of the indexed LIR function (guards caller-side zip alignment).
    pub function_name: String,
    insts: HashMap<(u32, u32), LirSourceInst>,
}

impl LirSourceIndex {
    /// Build the index from the LIR function that was handed to ISel.
    pub fn build(func: &trust_cg_lower::Function) -> Self {
        let mut insts = HashMap::new();
        for (block, bb) in &func.blocks {
            for (index, inst) in bb.instructions.iter().enumerate() {
                insts.insert(
                    (block.0, index as u32),
                    LirSourceInst {
                        digest: inst.lowering_digest(),
                        class: classify_lir_opcode(&inst.opcode),
                        opcode_debug: format!("{:?}", inst.opcode),
                    },
                );
            }
        }
        Self {
            function_name: func.name.clone(),
            insts,
        }
    }

    /// Look up the source instruction at TV-1 coordinates.
    pub fn get(&self, id: SourceInstId) -> Option<&LirSourceInst> {
        self.insts.get(&(id.block, id.index))
    }
}

// ---------------------------------------------------------------------------
// Cross-check core
// ---------------------------------------------------------------------------

/// Why a provenance cross-check failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProvenanceMismatchKind {
    /// The stamped `(block, index)` names no instruction in the replayed LIR
    /// function — the attribution dangles.
    DanglingSourceId,
    /// The stamped digest does not match the recomputed digest of the LIR
    /// instruction at the stamped coordinates — the stamp does not describe
    /// the instruction it points at.
    DigestMismatch,
    /// The emitted opcode's definite semantic class is not a plausible
    /// constituent of a lowering of the claimed source instruction.
    ClassMismatch,
}

/// A provenance cross-check failure (TV-2). In enforce mode this demotes the
/// instruction's verification result to `Failed` => cert `verified:false` =>
/// the compile fails closed.
#[derive(Debug, Clone)]
pub struct ProvenanceMismatch {
    /// Which invariant broke.
    pub kind: ProvenanceMismatchKind,
    /// Human-readable diagnostic (source coords, opcodes, classes, digests).
    pub detail: String,
}

/// Cross-check one emitted instruction's provenance stamp against the
/// replayed LIR function.
///
/// * `provenance` — the TV-1 stamp carried by the emitted instruction.
///   `Synthetic` (incl. `Unattributed`) is EXEMPT by contract and returns
///   `None`.
/// * `emitted_class` — the emitted opcode's definite semantic class per the
///   verifier's existing typed map, or `None` when the opcode has no definite
///   class (only the attribution-integrity checks apply then).
/// * `emitted_opcode_debug` — for diagnostics.
pub fn cross_check_inst(
    provenance: &LoweringProvenance,
    emitted_class: Option<OpClass>,
    emitted_opcode_debug: &str,
    index: &LirSourceIndex,
) -> Option<ProvenanceMismatch> {
    let LoweringProvenance::SourceInst { id, digest, .. } = provenance else {
        // Synthetic / Unattributed: no source claim to validate (documented
        // exemption — under-attribution is legal, misattribution never).
        return None;
    };

    let Some(source) = index.get(*id) else {
        return Some(ProvenanceMismatch {
            kind: ProvenanceMismatchKind::DanglingSourceId,
            detail: format!(
                "emitted {emitted_opcode_debug} is stamped as lowered from LIR {id}, but the \
                 replayed LIR function `{}` has no instruction at those coordinates",
                index.function_name
            ),
        });
    };

    if source.digest != *digest {
        return Some(ProvenanceMismatch {
            kind: ProvenanceMismatchKind::DigestMismatch,
            detail: format!(
                "emitted {emitted_opcode_debug} is stamped as lowered from LIR {id} with digest \
                 {:#018x}, but the replayed source instruction there is {} with digest {:#018x}",
                digest.0, source.opcode_debug, source.digest.0
            ),
        });
    }

    if let Some(emitted) = emitted_class
        && !compatible(source.class, emitted)
    {
        return Some(ProvenanceMismatch {
            kind: ProvenanceMismatchKind::ClassMismatch,
            detail: format!(
                "emitted {emitted_opcode_debug} (class {emitted:?}) is stamped as lowered from \
                 LIR {id} {} (class {:?}), but that emission cannot implement the claimed \
                 source instruction",
                source.opcode_debug, source.class
            ),
        });
    }

    None
}

// ---------------------------------------------------------------------------
// Mode + telemetry
// ---------------------------------------------------------------------------

/// Enforcement mode for the provenance cross-check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProvenanceXCheckMode {
    /// Do not run the cross-check at all.
    Off,
    /// Run the cross-check; count + report hits, never demote a verdict.
    Warn,
    /// Run the cross-check; a mismatch demotes the instruction's result to
    /// `Failed` (cert `verified:false` => compile fails closed).
    Enforce,
}

/// Default mode for the x86-64 verifier: ENFORCE.
///
/// Flipped default-ON per the §2.4 gate rollout protocol. The first warn-only
/// telemetry pass over the differential corpus (`bridge_differential_x86`
/// corpus, all opt levels, `TCG_REFINE_SOLVER=0`) surfaced 662 cross-check
/// hits, ALL `ClassMismatch` (0 dangling, 0 digest — attribution integrity was
/// already perfect). Triage found every one to be a legitimate wide-integer
/// multi-instruction expansion the coarse matrix under-approximated: i128
/// multiply partial-product `ADD`s stamped with the `Imul` anchor (82), and
/// i128 variable-shift `SUB`/`CMOV` (64∓count arithmetic + half selection)
/// stamped with the `Ishl`/`Ushr`/`Sshr` anchor (580). Each is correct vs
/// LLVM on the corpus. Resolution (never a weakening): [`compatible`] was
/// extended by triage to admit exactly `IntMul->IntAdd` and
/// `Shift->{IntSub, Select}`; the re-run reports 0 hits and the differential
/// stays 0-MISMATCH with an unchanged fail-closed set (2026-07-02). Any NEW
/// class a future program surfaces fails closed loudly (never a miscompile)
/// and is triaged into the matrix, not silenced.
pub const X86_PROVENANCE_XCHECK_DEFAULT: ProvenanceXCheckMode = ProvenanceXCheckMode::Enforce;

/// Default mode for the AArch64 verifier: WARN-ONLY.
///
/// The aarch64 differential corpus cannot execute on the x86 validation host
/// (structural compile coverage only), so the §2.4 warn->enforce flip is
/// deferred to the Apple-Silicon lane (roadmap §3: X2 designs, AS validates).
pub const AARCH64_PROVENANCE_XCHECK_DEFAULT: ProvenanceXCheckMode = ProvenanceXCheckMode::Warn;

/// Resolve the active mode: `TCG_PROVENANCE_XCHECK` env overrides
/// (`off`/`0`/`false`, `warn`, `enforce`/`on`/`1`/`true`); unset or
/// unrecognized values use the per-arch default.
pub fn provenance_xcheck_mode(arch_default: ProvenanceXCheckMode) -> ProvenanceXCheckMode {
    match std::env::var("TCG_PROVENANCE_XCHECK") {
        Ok(value) => match value.trim().to_ascii_lowercase().as_str() {
            "off" | "0" | "false" => ProvenanceXCheckMode::Off,
            "warn" | "warn-only" | "warnonly" => ProvenanceXCheckMode::Warn,
            "enforce" | "on" | "1" | "true" => ProvenanceXCheckMode::Enforce,
            _ => arch_default,
        },
        Err(_) => arch_default,
    }
}

/// True when `TCG_TRACE_PROVENANCE=1` requests per-function trace output.
pub fn provenance_trace_enabled() -> bool {
    matches!(
        std::env::var("TCG_TRACE_PROVENANCE").as_deref(),
        Ok("1") | Ok("true") | Ok("on")
    )
}

/// Process-wide count of cross-check mismatches observed (warn or enforce).
static XCHECK_HITS: AtomicU64 = AtomicU64::new(0);

/// Total cross-check mismatches observed by this process (telemetry for the
/// warn-only rollout phase and for tests).
pub fn provenance_xcheck_hit_count() -> u64 {
    XCHECK_HITS.load(Ordering::Relaxed)
}

/// Record one cross-check mismatch: bump the process-wide counter and print a
/// greppable one-line report (`[TCG-PROVENANCE-XCHECK-*]`). Hits are
/// exceptional by design, so the line is always printed.
pub fn record_provenance_xcheck_hit(
    arch: &str,
    function_name: &str,
    inst_index: usize,
    mismatch: &ProvenanceMismatch,
    mode: ProvenanceXCheckMode,
) {
    XCHECK_HITS.fetch_add(1, Ordering::Relaxed);
    let tag = match mode {
        ProvenanceXCheckMode::Enforce => "[TCG-PROVENANCE-XCHECK-FAIL]",
        _ => "[TCG-PROVENANCE-XCHECK-WARN]",
    };
    eprintln!(
        "{tag} arch={arch} fn={function_name} inst#{inst_index} kind={:?}: {}",
        mismatch.kind, mismatch.detail
    );
}

/// Print the per-function trace summary when `TCG_TRACE_PROVENANCE=1`.
pub fn trace_function_summary(
    arch: &str,
    function_name: &str,
    attributed: usize,
    synthetic: usize,
    mismatches: usize,
) {
    if provenance_trace_enabled() {
        eprintln!(
            "[TCG-TRACE-PROVENANCE] arch={arch} fn={function_name} attributed={attributed} \
             synthetic={synthetic} mismatches={mismatches}"
        );
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::{Block, Instruction, Value};
    use trust_cg_lower::types::Type;

    fn lir_with_iconst_imul() -> trust_cg_lower::Function {
        let mut func = trust_cg_lower::Function::new(
            "tv2_test",
            Signature {
                params: vec![Type::I64],
                returns: vec![Type::I64],
            },
        );
        let block = Block(0);
        func.block_order.push(block);
        func.blocks.insert(
            block,
            trust_cg_lower::function::BasicBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: LirOpcode::Iconst {
                            ty: Type::I64,
                            imm: 5,
                        },
                        args: vec![],
                        results: vec![Value(1)],
                    },
                    Instruction {
                        opcode: LirOpcode::Imul,
                        args: vec![Value(0), Value(1)],
                        results: vec![Value(2)],
                    },
                    Instruction {
                        opcode: LirOpcode::Return,
                        args: vec![Value(2)],
                        results: vec![],
                    },
                ],
                source_locs: vec![],
            },
        );
        func
    }

    fn source_stamp(func: &trust_cg_lower::Function, block: u32, index: u32) -> LoweringProvenance {
        let inst = &func.blocks[&Block(block)].instructions[index as usize];
        LoweringProvenance::SourceInst {
            id: SourceInstId { block, index },
            digest: inst.lowering_digest(),
            trust_ir_inst: None,
        }
    }

    #[test]
    fn synthetic_and_unattributed_are_exempt() {
        let lir = lir_with_iconst_imul();
        let index = LirSourceIndex::build(&lir);
        assert!(
            cross_check_inst(
                &LoweringProvenance::UNATTRIBUTED,
                Some(OpClass::IntAdd),
                "AddRR",
                &index
            )
            .is_none()
        );
    }

    #[test]
    fn faithful_stamp_passes() {
        let lir = lir_with_iconst_imul();
        let index = LirSourceIndex::build(&lir);
        // An IMUL emitted while lowering the Imul at (0,1): consistent.
        let stamp = source_stamp(&lir, 0, 1);
        assert!(cross_check_inst(&stamp, Some(OpClass::IntMul), "ImulRR", &index).is_none());
        // Strength-reduced shift under the same Imul: consistent.
        assert!(cross_check_inst(&stamp, Some(OpClass::Shift), "ShlRI", &index).is_none());
        // No definite emitted class: only integrity checks run, which pass.
        assert!(cross_check_inst(&stamp, None, "CmpRR", &index).is_none());
    }

    #[test]
    fn wrong_source_class_is_a_mismatch() {
        let lir = lir_with_iconst_imul();
        let index = LirSourceIndex::build(&lir);
        // An IDIV stamped as coming from an Imul: a divide cannot implement a
        // multiply. (An ADD is deliberately NOT used: the i128 multiply
        // expansion legitimately emits partial-product ADDs stamped with the
        // Imul anchor, so `IntAdd` IS a compatible constituent — see the
        // `IntMul` arm of `compatible`.)
        let stamp = source_stamp(&lir, 0, 1);
        let mismatch = cross_check_inst(&stamp, Some(OpClass::IntDiv), "IdivRR", &index)
            .expect("IDIV cannot implement the claimed Imul");
        assert_eq!(mismatch.kind, ProvenanceMismatchKind::ClassMismatch);
        // FP arithmetic under an integer source: also a mismatch.
        let fp = cross_check_inst(&stamp, Some(OpClass::FpArith), "Addsd", &index)
            .expect("ADDSD cannot implement the claimed Imul");
        assert_eq!(fp.kind, ProvenanceMismatchKind::ClassMismatch);
    }

    #[test]
    fn digest_mismatch_is_detected() {
        let lir = lir_with_iconst_imul();
        let index = LirSourceIndex::build(&lir);
        // Stamp points at (0,0) (the Iconst) but carries the Imul's digest.
        let imul_digest = lir.blocks[&Block(0)].instructions[1].lowering_digest();
        let stamp = LoweringProvenance::SourceInst {
            id: SourceInstId { block: 0, index: 0 },
            digest: imul_digest,
            trust_ir_inst: None,
        };
        let mismatch = cross_check_inst(&stamp, None, "MovRI", &index)
            .expect("stamp digest does not match the instruction at its coordinates");
        assert_eq!(mismatch.kind, ProvenanceMismatchKind::DigestMismatch);
    }

    #[test]
    fn dangling_source_id_is_detected() {
        let lir = lir_with_iconst_imul();
        let index = LirSourceIndex::build(&lir);
        let stamp = LoweringProvenance::SourceInst {
            id: SourceInstId { block: 7, index: 3 },
            digest: SourceInstDigest::compute("Iadd", 2, 1),
            trust_ir_inst: None,
        };
        let mismatch = cross_check_inst(&stamp, None, "AddRR", &index)
            .expect("stamp points at a nonexistent source instruction");
        assert_eq!(mismatch.kind, ProvenanceMismatchKind::DanglingSourceId);
    }

    #[test]
    fn glue_emissions_are_compatible_with_every_source() {
        for source in [
            OpClass::Const,
            OpClass::Copy,
            OpClass::IntAdd,
            OpClass::IntDiv,
            OpClass::FpArith,
            OpClass::ControlFlow,
            OpClass::MemLoad,
        ] {
            for glue in [
                OpClass::Copy,
                OpClass::Extend,
                OpClass::MemLoad,
                OpClass::MemStore,
                OpClass::AddrCalc,
                OpClass::Const,
            ] {
                assert!(compatible(source, glue), "{source:?} must allow {glue:?}");
            }
        }
    }

    #[test]
    fn compatibility_matrix_spot_checks() {
        use OpClass::*;
        // Definite-arith under constants / copies is never legitimate.
        assert!(!compatible(Const, IntAdd));
        assert!(!compatible(Copy, IntMul));
        // The class the emission implements must relate to the source.
        assert!(compatible(IntAdd, IntAdd));
        assert!(!compatible(IntAdd, IntMul)); // scalar mul under a plain add
        assert!(compatible(IntAdd, FusedMulAdd)); // aarch64 MADD anchor at the Iadd
        assert!(compatible(IntMul, Shift)); // power-of-two strength reduction
        assert!(compatible(IntMul, IntAdd)); // i128 multiply partial-product accumulation
        assert!(!compatible(IntMul, IntDiv)); // a divide cannot implement a multiply
        assert!(!compatible(IntMul, FpArith)); // an FP op cannot implement an integer multiply
        assert!(compatible(Shift, IntSub)); // i128 var-shift: 64 - count / count - 64
        assert!(compatible(Shift, Select)); // i128 var-shift: CMOV half/zero selection
        assert!(!compatible(Shift, IntMul)); // a shift never needs a multiply
        assert!(compatible(IntDiv, IntMul)); // magic-number division
        assert!(!compatible(Bitwise, IntAdd));
        assert!(compatible(Bitwise, VecBitwise)); // v128-typed Band -> PAND
        assert!(!compatible(IntCmp, FpCmp));
        assert!(compatible(IntCmp, IntSub)); // CMP's observable value is the difference
        assert!(compatible(FpArith, VecBitwise)); // fabs/fneg sign-mask idioms
        assert!(!compatible(FpArith, IntAdd));
        assert!(!compatible(MemLoad, IntDiv));
        assert!(compatible(VecInt, IntMul)); // scalarized lane fallback
        assert!(!compatible(VecInt, IntDiv));
        assert!(!compatible(ControlFlow, FpArith));
    }

    #[test]
    fn classifier_covers_representative_opcodes() {
        assert_eq!(
            classify_lir_opcode(&LirOpcode::Iconst {
                ty: Type::I64,
                imm: 0
            }),
            OpClass::Const
        );
        assert_eq!(classify_lir_opcode(&LirOpcode::Iadd), OpClass::IntAdd);
        assert_eq!(classify_lir_opcode(&LirOpcode::Sdiv), OpClass::IntDiv);
        assert_eq!(classify_lir_opcode(&LirOpcode::Fma), OpClass::FpArith);
        assert_eq!(classify_lir_opcode(&LirOpcode::Fmuladd), OpClass::FpArith);
        assert_eq!(
            classify_lir_opcode(&LirOpcode::Load {
                ty: Type::I64,
                align: None
            }),
            OpClass::MemLoad
        );
        assert_eq!(classify_lir_opcode(&LirOpcode::V4I32Mul), OpClass::VecInt);
        assert_eq!(
            classify_lir_opcode(&LirOpcode::Memcpy),
            OpClass::MemIntrinsic
        );
    }

    #[test]
    fn mode_defaults_pin_the_rollout_state() {
        // x86 default is ENFORCE (flipped after the 0-hit warn-only corpus
        // run); aarch64 default stays WARN until the AS lane validates on an
        // M-series corpus. Changing either constant is a gate change and
        // must follow the §2.4 rollout protocol.
        assert_eq!(X86_PROVENANCE_XCHECK_DEFAULT, ProvenanceXCheckMode::Enforce);
        assert_eq!(
            AARCH64_PROVENANCE_XCHECK_DEFAULT,
            ProvenanceXCheckMode::Warn
        );
    }
}
