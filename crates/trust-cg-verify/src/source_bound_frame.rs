// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Source-bound obligations for a sixteen-byte AArch64 leaf frame.
//!
//! The complete body must independently match its LIR source in the affine
//! checker. Only then may its exact STP/MOV/LDP envelope supply a frame
//! obligation. The memory is an arbitrary byte array, including unwritten
//! addresses; both saved registers, SP writeback and memory outside the owned
//! frame participate in the formula. Entry requires sixteen writable private
//! bytes below an aligned, non-wrapping SP, as in the affine byte checker.
//!
//! Construction is not discharge. The function verifier may credit this exact
//! envelope only after independent formal replay. This does not prove the Rust
//! checker implementation or authorize arbitrary paired memory instructions.
//! The envelope's two pair records are memory rows: since 2026-10-01 each is
//! credited only with the replayed frame theorem AND a Clean-checked
//! certificate of every part of its word's memory-effect decomposition, bound
//! to the theorem's record ([`crate::aarch64_memory_source_binding`]).
//!
//! A frameless leaf whose body loads and stores is outside the affine domain
//! and has no envelope; [`source_bound_memory_leaf`] binds its accesses to
//! its LIR source instead.

use crate::aarch64_affine_lowering::{
    AffineLoweringError, check_affine_source_domain, check_allocated_aarch64_affine_lowering,
    check_allocated_aarch64_diamond,
};
use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::memory_proofs::{encode_load_le, encode_store_le, memory_sort};
use crate::smt::SmtExpr;
use trust_cg_ir::regs::{RegClass, SP, SpecialReg, X29, X30};
use trust_cg_ir::{AArch64Opcode, BlockId, InstFlags, InstId, MachFunction, MachInst, MachOperand};
use trust_cg_lower::Function;

#[cfg(feature = "source-defined-call")]
pub use crate::source_bound_body::read_only_source::{
    LicensedReadOnlySourceQueries, bind_licensed_read_only_source,
};
pub use crate::source_bound_body::read_only_source::{
    ReadOnlyLoad, ReadOnlySite, ReadOnlySourceError, ReadOnlySourceQueries, ReadOnlyType,
    bind_read_only_source,
};

pub use crate::source_bound_body::read_only_source::scalar_memory::{
    ScalarMemoryAccess, ScalarMemoryCodec, ScalarMemorySourceQueries, bind_scalar_memory_source,
};

pub use crate::source_bound_body::read_only_source::conditional_wrapper::{
    CallCodec, ConditionalWrapperQueries, OutstandingCallRelation, PendingCalleeRelations,
    bind_conditional_wrapper_source,
};

pub use crate::source_bound_body::read_only_source::native_aggregate_target::{
    NativeAggregateTargetObservations, NativeProviderWriteRegion,
    PendingNativeAggregateMaterialization, PendingNativeProviderFootprint, TargetAccess,
    TargetCall, TargetSlotAddress, observe_native_aggregate_target,
};
pub use crate::source_bound_body::read_only_source::native_aggregates::{
    NativeAggregateRecord, NativeAggregateRequirement, NativeAggregateSourceEvents,
    PendingNativeAggregateEvent, observe_native_aggregate_source,
};
pub use crate::source_bound_body::read_only_source::scalar_returns::{
    ScalarReturnCodec, ScalarReturnSourceQueries, bind_scalar_return_source,
};

// Checked scalar edge transport is diagnostic graph correspondence only.
pub use super::source_bound_body::read_only_source::scalar_edge_projection::{
    CheckedScalarBlockArguments, ScalarEdgeCodec, ScalarEdgeTransport, check_scalar_block_arguments,
};

#[path = "source_bound_linear.rs"]
pub(crate) mod linear;

#[path = "source_bound_branch_paths.rs"]
pub(crate) mod branch_paths;

#[path = "source_bound_diamond.rs"]
mod diamond;
#[cfg(test)]
#[path = "source_bound_diamond_arithmetic_tests.rs"]
mod diamond_arithmetic_tests;
#[cfg(test)]
#[path = "source_bound_diamond_tests.rs"]
mod diamond_tests;
#[path = "source_bound_output_memory.rs"]
mod output_memory;

pub use output_memory::Aarch64OutputFrame;

pub use output_memory::final_bytes::{
    CheckedAarch64OutputBytes, OutputByteError, check_aarch64_output_bytes,
};

pub use output_memory::trust_ir_source::{
    CheckedAarch64TrustIrOutputBytes, OutputMemoryRequirements, TrustIrOutputError,
    check_aarch64_trust_ir_output_bytes,
};

#[path = "source_bound_memory_leaf.rs"]
pub(crate) mod memory_leaf;
pub use memory_leaf::{
    BoundLeafAccess, MemoryLeafRefusal, SourceBoundMemoryLeaf, source_bound_memory_leaf,
};

#[path = "source_bound_cell_frame.rs"]
mod cell_frame;
#[path = "source_bound_cell_memory.rs"]
mod cell_memory;
pub use cell_frame::{
    CheckedAarch64ScalarCellFrame, ScalarCellFrameError, check_aarch64_scalar_cell_frame,
};

#[path = "source_bound_cell_source.rs"]
mod cell_source;
pub use cell_source::{
    CheckedAarch64ScalarCellSource, ScalarCellSourceError, check_aarch64_scalar_cell_source,
};

#[path = "source_bound_repeated_cell_source.rs"]
mod repeated_cell_source;
pub use repeated_cell_source::{
    Address as RepeatedCellAddress, Argument as RepeatedCellArgument,
    Base as RepeatedCellAddressBase, Bits as RepeatedCellBits,
    Checked as CheckedAarch64RepeatedCellSource, Contract as RepeatedCellContract,
    Error as RepeatedCellSourceError, Event as RepeatedCellEvent,
    check as check_aarch64_repeated_cell_source,
    check_with_callees as check_aarch64_repeated_cell_source_with_callees,
};

#[path = "source_bound_cell_caller.rs"]
mod cell_caller;
pub use cell_caller::{
    CellRowRole, SCALAR_CELL_CALLER_NEEDS_REPLAY, SCALAR_CELL_CALLER_OBLIGATION_NAME,
    STACK_WINDOW_BYTES, ScalarCellCallerPart, ScalarCellCallerRefusal, SourceBoundScalarCellCaller,
    diagnostic_scalar_cell_caller_obligation, source_bound_scalar_cell_caller,
};
pub(crate) use cell_caller::{
    admission_layout_diagnosis as scalar_cell_admission_layout_diagnosis, scalar_cell_row_result,
};

#[path = "source_bound_cell_bytes.rs"]
mod cell_bytes;
pub use cell_bytes::elf::{
    CheckedAarch64ScalarCellElf, ScalarCellElfError, check_aarch64_scalar_cell_elf,
};
pub use cell_bytes::{
    CheckedAarch64ScalarCellBytes, ScalarCellByteError, ScalarCellRelocation,
    check_aarch64_scalar_cell_bytes,
};

#[path = "source_bound_cell_link.rs"]
mod cell_link;
pub use cell_link::{
    CheckedAarch64ScalarCellLink, ScalarCellLinkError, ScalarCellLinkedCallback,
    check_aarch64_scalar_cell_link,
};

/// Construct a diagnostic, conditional output-memory query from independently
/// matched source and allocated machine effects. This does not construct a
/// `SourceBoundFrame` or grant instruction/publication credit. The caller-memory
/// ownership premise described by the query is not discharged by LIR metadata;
/// production admission therefore continues to refuse this effectful body.
/// Valid source execution must supply live writable output storage; the query's
/// numeric guards do not establish allocation validity, lifetime or permission.
/// This checks allocated instructions, not their subsequently encoded bytes.
pub fn diagnostic_output_memory_obligation(
    source: &Function,
    machine: &MachFunction,
) -> Option<ProofObligation> {
    let view = linear::source_view(source)?;
    let chain = linear::machine_chain(machine).ok()?;
    check_owned_instructions(machine, &chain.live, false)?;
    let (_, body) = frame_body(machine, &chain.instructions).ok()?;
    output_memory::obligation(&view, &body)
}

/// Immutable inputs and the exact frame obligation. No public constructor.
pub struct SourceBoundFrame<'a> {
    source: &'a Function,
    machine: &'a MachFunction,
    pair_instructions: [InstId; 2],
    establish_instruction: InstId,
    obligation: ProofObligation,
}

/// Raw execution paths, reconstructed from the actual laid-out machine edges.
/// No normal-form terms or instruction credit travel through this view.
pub(crate) enum RawControl {
    Chain(Vec<InstId>),
    Diamond {
        prefix: Vec<InstId>,
        branch: InstId,
        paths: [Vec<InstId>; 2],
    },
}

impl<'a> SourceBoundFrame<'a> {
    pub fn source(&self) -> &'a Function {
        self.source
    }

    pub fn machine(&self) -> &'a MachFunction {
        self.machine
    }

    pub fn pair_instructions(&self) -> [InstId; 2] {
        self.pair_instructions
    }

    pub fn obligation(&self) -> &ProofObligation {
        &self.obligation
    }

    pub(crate) fn envelope_instructions(&self) -> [InstId; 3] {
        [
            self.pair_instructions[0],
            self.establish_instruction,
            self.pair_instructions[1],
        ]
    }

    /// Reconstruct control from this immutable owner's actual machine input,
    /// including encoded direct targets and layout fallthrough. The owner has
    /// already checked instruction ownership and the common frame envelope.
    pub(crate) fn raw_control(&self) -> Option<RawControl> {
        if let Ok(chain) = linear::machine_chain(self.machine) {
            return Some(RawControl::Chain(chain.instructions));
        }
        let paths = branch_paths::machine_paths(self.machine).ok()?;
        Some(RawControl::Diamond {
            prefix: paths.prefix,
            branch: paths.branch,
            paths: paths.paths,
        })
    }

    #[cfg(test)]
    pub(crate) fn raw_chain(&self) -> Option<Vec<InstId>> {
        match self.raw_control()? {
            RawControl::Chain(chain) => Some(chain),
            RawControl::Diamond { .. } => None,
        }
    }
}

fn exact_instruction(inst: &MachInst, opcode: AArch64Opcode, operands: &[MachOperand]) -> bool {
    inst.opcode == opcode
        && inst.operands == operands
        && inst.flags == MachInst::new(opcode, Vec::new()).flags
        && inst.implicit_defs.is_empty()
        && inst.implicit_uses.is_empty()
}

pub(crate) fn inert_allocated_nop(inst: &MachInst, next_vreg: u32) -> bool {
    let caller_register = |reg: trust_cg_ir::regs::PReg| matches!(reg.encoding(), 0..=17 | 32..=49);
    inst.opcode == AArch64Opcode::Nop
        && matches!(inst.flags, InstFlags::EMPTY | InstFlags::IS_PSEUDO)
        && inst.implicit_defs.is_empty()
        && inst.implicit_uses.iter().copied().all(caller_register)
        && match inst.operands.as_slice() {
            [] => true,
            [MachOperand::PReg(a), MachOperand::PReg(b)] => a == b && caller_register(*a),
            // Dead copies can retain an unallocated destination. A NOP does
            // not define it; any subsequent read still fails the body check.
            [MachOperand::VReg(a), MachOperand::PReg(b)] => {
                a.id < next_vreg
                    && caller_register(*b)
                    // An erased I32 formal copy may retain its incoming
                    // X-register ABI spelling. No value is defined or read;
                    // later real uses still require independently known bits.
                    && matches!(
                        (a.class, b.encoding()),
                        (RegClass::Gpr32, 0..=17 | 32..=49) | (RegClass::Gpr64, 0..=17)
                    )
            }
            _ => false,
        }
}

/// Why [`source_bound_frame`] constructed no obligation.
///
/// `Unsupported` makes no claim about the pair: it lies outside this binder's
/// checked domain and ordinary coverage rules apply. `Mismatch` is reached only
/// after the LIR source was admitted (chain or pure-arithmetic diamond view inside the
/// affine source domain) and the machine's frame and control skeleton were
/// recognized. The machine then disagrees with that source or with its own
/// layout, so it identifies an erroneous supported target, never missing
/// coverage. Callers enforcing source checking must reject it.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum SourceBoundFrameRefusal {
    #[error("unsupported source-bound frame shape: {0}")]
    Unsupported(FrameShapeUnsupported),
    #[error("source-bound frame mismatch: {0}")]
    Mismatch(FrameBindingMismatch),
}

impl SourceBoundFrameRefusal {
    /// The typed mismatch, when this refusal identifies an erroneous target.
    pub fn mismatch(&self) -> Option<&FrameBindingMismatch> {
        match self {
            Self::Mismatch(mismatch) => Some(mismatch),
            Self::Unsupported(_) => None,
        }
    }
}

/// A pair outside the binder's checked domain. None of these grants or
/// withholds any other authority.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum FrameShapeUnsupported {
    #[error("LIR source is not a bounded unconditional chain or pure-arithmetic diamond")]
    SourceShape,
    #[error("LIR source is outside the affine domain: {0}")]
    SourceDomain(AffineLoweringError),
    #[error("machine control flow is not a bounded chain or single-conditional diamond")]
    MachineControl,
    #[error("live machine instructions are not exactly the checked paths plus inert tombstones")]
    Ownership,
    #[error("machine path is outside the sixteen-byte FP/LR envelope: {0}")]
    Envelope(EnvelopeShape),
    #[error("machine body is outside the checked affine domain: {0}")]
    Body(AffineLoweringError),
}

/// Frame shapes that other, legitimate frame lowerings produce.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum EnvelopeShape {
    #[error("path is too short for save, establish, restore and return")]
    TooShort,
    #[error("path does not begin with an FP/LR pre-index pair save")]
    NoFrameSave,
    #[error("frame pointer is not established from SP")]
    NoFramePointer,
    #[error("return is not preceded by an FP/LR post-index pair restore")]
    NoFrameRestore,
    #[error("body names SP (local area, spill slot or stack probe)")]
    StackPointerBody,
    #[error("diamond paths restore the frame with different instructions")]
    DivergentRestores,
}

/// A recognized supported target that is wrong. Each variant is a defect no
/// correct lowering of an admitted source produces.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum FrameBindingMismatch {
    /// An FP/LR pair save/restore on SP, or an FP establishment from SP,
    /// occupies its envelope position with a different offset, register
    /// order, flag set or implicit effect than the exact sixteen-byte frame.
    #[error(
        "frame {role} instruction {instruction:?} differs from the exact sixteen-byte FP/LR envelope"
    )]
    FrameEnvelope {
        role: FrameEnvelopeRole,
        instruction: InstId,
    },
    /// A direct branch does not transfer to the laid-out block its own CFG
    /// records, or cannot transfer to any block start.
    #[error("branch in block {block:?} (instruction {instruction:?}) {defect}")]
    BranchTarget {
        block: BlockId,
        instruction: Option<InstId>,
        defect: BranchTargetDefect,
    },
    /// The complete scalar body computes a different value than its source,
    /// or is not a valid allocated body (undefined read, clobbered LR or
    /// callee-save, wrong width, unencodable immediate, altered signature).
    #[error("machine body disagrees with its LIR source: {0}")]
    Body(AffineLoweringError),
}

/// Position of an envelope instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FrameEnvelopeRole {
    Save,
    Establish,
    Restore,
}

impl std::fmt::Display for FrameEnvelopeRole {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Save => "save",
            Self::Establish => "establish",
            Self::Restore => "restore",
        })
    }
}

/// Exact branch defect, derived from the final layout's word offsets.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum BranchTargetDefect {
    #[error("has displacement {displacement} outside its {bits}-bit field")]
    DisplacementOutOfRange { displacement: i64, bits: u32 },
    #[error("has displacement {displacement} that lands on no laid-out block start")]
    NoBlockStart { displacement: i64 },
    #[error("targets block {target:?}, which is not laid out")]
    TargetNotLaidOut { target: BlockId },
    #[error("transfers to block {target:?} but the block records successor {recorded:?}")]
    DisagreesWithSuccessor { target: BlockId, recorded: BlockId },
    #[error("transfers along edges that differ from the recorded CFG")]
    DisagreesWithCfg,
}

/// Machine control-skeleton refusal shared by the chain and diamond walkers.
pub(crate) enum ControlRefusal {
    /// Not this walker's shape; no claim.
    Shape,
    /// A recognized direct branch with a definite defect.
    Branch(FrameBindingMismatch),
}

fn unsupported(shape: FrameShapeUnsupported) -> SourceBoundFrameRefusal {
    SourceBoundFrameRefusal::Unsupported(shape)
}

/// Complete-body errors: a returned value that differs, or a body that is not
/// a valid allocated computation, is a mismatch. Opcodes, flags, stack and EH
/// facts outside the modeled domain, and source-domain limits, are not.
pub(crate) fn classify_body(error: AffineLoweringError) -> SourceBoundFrameRefusal {
    match error {
        AffineLoweringError::ReturnMismatch | AffineLoweringError::InvalidMachine(_) => {
            SourceBoundFrameRefusal::Mismatch(FrameBindingMismatch::Body(error))
        }
        AffineLoweringError::UnsupportedMachine(_)
        | AffineLoweringError::UnsupportedSource(_)
        | AffineLoweringError::InvalidSource(_) => unsupported(FrameShapeUnsupported::Body(error)),
    }
}

/// Only the source determines applicability. A source outside the chain,
/// diamond or affine domain is never judged against its machine code.
fn admitted_source_view(source: &Function) -> Result<Function, SourceBoundFrameRefusal> {
    let source_view =
        raw_source_view(source).ok_or(unsupported(FrameShapeUnsupported::SourceShape))?;
    check_affine_source_domain(&source_view)
        .map_err(|error| unsupported(FrameShapeUnsupported::SourceDomain(error)))?;
    Ok(source_view)
}

pub(crate) fn raw_source_view(source: &Function) -> Option<Function> {
    linear::source_view(source).or_else(|| diamond::source_view(source))
}

/// Whether [`source_bound_frame`] judges any machine lowering of `source`.
///
/// This is exactly the binder's own applicability check. When it is `false`,
/// every lowering of `source` is [`SourceBoundFrameRefusal::Unsupported`]
/// before its machine code is inspected, so no FP/LR envelope around that
/// lowering can earn this owner's frame or ALU credit. Frame lowering uses it
/// through [`source_requires_frame_proof_envelope`] to select the remaining
/// frame-bound domain. `true` claims nothing about a particular machine body
/// and does not require an otherwise unnecessary frame.
pub fn source_admits_frame_owner(source: &Function) -> bool {
    admitted_source_view(source).is_ok()
}

/// Whether this source still relies on a proof-only FP/LR envelope.
///
/// This is not an ABI/storage decision and grants no instruction credit.
/// Linear sources have a frame-independent return/control route (or are
/// outside the affine frame owner's domain). Only admitted non-linear
/// sources retain the old owner's proof envelope. Classify the chain once;
/// do not normalize its affine return a second time just to select layout.
pub fn source_requires_frame_proof_envelope(source: &Function) -> bool {
    if linear::source_view(source).is_some() {
        return false;
    }
    diamond::source_view(source).is_some_and(|view| check_affine_source_domain(&view).is_ok())
}

/// Build a frame obligation only for an independently checked complete body.
/// Unsupported shapes grant no weaker binding; source mismatches on a
/// recognized supported shape are returned as a typed [`FrameBindingMismatch`]
/// so enforcing callers reject them instead of treating them as unsupported.
pub fn source_bound_frame<'a>(
    source: &'a Function,
    machine: &'a MachFunction,
) -> Result<SourceBoundFrame<'a>, SourceBoundFrameRefusal> {
    let source_view = admitted_source_view(source)?;
    let chain = match linear::machine_chain(machine) {
        Ok(chain) => Some(chain),
        Err(ControlRefusal::Branch(mismatch)) => {
            return Err(SourceBoundFrameRefusal::Mismatch(mismatch));
        }
        Err(ControlRefusal::Shape) => None,
    };
    let (envelope, bodies) = if let Some(chain) = chain {
        check_owned_instructions(machine, &chain.live, false)
            .ok_or(unsupported(FrameShapeUnsupported::Ownership))?;
        let (envelope, body) = frame_body(machine, &chain.instructions)?;
        check_allocated_aarch64_affine_lowering(&source_view, &body).map_err(classify_body)?;
        (envelope, None)
    } else {
        let paths = match branch_paths::machine_paths(machine) {
            Ok(paths) => paths,
            Err(ControlRefusal::Branch(mismatch)) => {
                return Err(SourceBoundFrameRefusal::Mismatch(mismatch));
            }
            Err(ControlRefusal::Shape) => {
                return Err(unsupported(FrameShapeUnsupported::MachineControl));
            }
        };
        check_owned_instructions(machine, &paths.live, true)
            .ok_or(unsupported(FrameShapeUnsupported::Ownership))?;
        if paths.prefix.len() < 2 {
            return Err(unsupported(FrameShapeUnsupported::Envelope(
                EnvelopeShape::TooShort,
            )));
        }
        let all_ids =
            |path: &[InstId]| paths.prefix.iter().chain(path).copied().collect::<Vec<_>>();
        let (envelope, taken) = frame_body(machine, &all_ids(&paths.paths[0]))?;
        let (other_envelope, not_taken) = frame_body(machine, &all_ids(&paths.paths[1]))?;
        if envelope != other_envelope {
            return Err(unsupported(FrameShapeUnsupported::Envelope(
                EnvelopeShape::DivergentRestores,
            )));
        }
        let prefix = scalar_body(machine, &paths.prefix[2..]);
        (envelope, Some((prefix, paths.branch, taken, not_taken)))
    };
    if let Some((prefix, branch, taken, not_taken)) = bodies {
        check_allocated_aarch64_diamond(
            &source_view,
            &prefix,
            &machine.insts[branch.0 as usize],
            &taken,
            &not_taken,
        )
        .map_err(classify_body)?;
    }
    Ok(SourceBoundFrame {
        source,
        machine,
        pair_instructions: [envelope[0], envelope[2]],
        establish_instruction: envelope[1],
        obligation: frame_obligation(),
    })
}

pub(crate) fn check_owned_instructions(
    machine: &MachFunction,
    live: &[InstId],
    diamond: bool,
) -> Option<()> {
    check_owned_instructions_with(machine, live, diamond, |inst| {
        inert_allocated_nop(inst, machine.next_vreg)
    })
}

fn check_owned_instructions_with(
    machine: &MachFunction,
    live: &[InstId],
    diamond: bool,
    inert_nop: impl Fn(&MachInst) -> bool,
) -> Option<()> {
    // Every live instruction occurs once. Optimizers may retain a completely
    // inert NOP or a branch to a merged-away empty block as an unreferenced
    // arena tombstone. Neither contributes execution or live register uses.
    let mut seen = vec![false; machine.insts.len()];
    for id in live {
        if std::mem::replace(seen.get_mut(id.0 as usize)?, true) {
            return None;
        }
    }
    if machine.insts.iter().zip(&seen).any(|(inst, seen)| {
        !seen
            && !(inert_nop(inst) && inst.implicit_uses.is_empty())
            && !linear::inactive_branch_tombstone(inst, machine)
            && !(diamond && branch_paths::removed_edge(inst, machine))
    }) {
        return None;
    }
    Some(())
}

/// An FP/LR pair access on SP with the envelope opcode, in either register
/// order and with any immediate. Frame lowering emits this opcode for FP/LR
/// only as the exact sixteen-byte envelope: larger callee-save areas save
/// another pair first and address FP/LR with the offset form.
fn frame_pair_like(inst: &MachInst, opcode: AArch64Opcode) -> bool {
    inst.opcode == opcode
        && matches!(
            inst.operands.as_slice(),
            [
                MachOperand::PReg(first),
                MachOperand::PReg(second),
                MachOperand::Special(SpecialReg::SP),
                MachOperand::Imm(_),
            ] if (*first == X29 && *second == X30) || (*first == X30 && *second == X29)
        )
}

fn frame_body(
    machine: &MachFunction,
    ids: &[InstId],
) -> Result<([InstId; 3], MachFunction), SourceBoundFrameRefusal> {
    let envelope = |shape| unsupported(FrameShapeUnsupported::Envelope(shape));
    let wrong = |role, instruction| {
        SourceBoundFrameRefusal::Mismatch(FrameBindingMismatch::FrameEnvelope { role, instruction })
    };
    if ids.len() < 4 {
        return Err(envelope(EnvelopeShape::TooShort));
    }
    let save = ids[0];
    let establish = ids[1];
    let restore = ids[ids.len() - 2];
    let save_inst = &machine.insts[save.0 as usize];
    let save_record =
        frame_record_instruction(FrameEnvelopeRole::Save).expect("the save is a frame record");
    if !exact_instruction(save_inst, save_record.opcode, &save_record.operands) {
        return Err(if frame_pair_like(save_inst, AArch64Opcode::StpPreIndex) {
            wrong(FrameEnvelopeRole::Save, save)
        } else {
            envelope(EnvelopeShape::NoFrameSave)
        });
    }
    let restore_inst = &machine.insts[restore.0 as usize];
    let restore_record = frame_record_instruction(FrameEnvelopeRole::Restore)
        .expect("the restore is a frame record");
    if !exact_instruction(
        restore_inst,
        restore_record.opcode,
        &restore_record.operands,
    ) {
        return Err(
            if frame_pair_like(restore_inst, AArch64Opcode::LdpPostIndex) {
                wrong(FrameEnvelopeRole::Restore, restore)
            } else {
                envelope(EnvelopeShape::NoFrameRestore)
            },
        );
    }
    let establish_inst = &machine.insts[establish.0 as usize];
    if !exact_instruction(
        establish_inst,
        AArch64Opcode::AddRI,
        &[
            MachOperand::PReg(X29),
            MachOperand::Special(SpecialReg::SP),
            MachOperand::Imm(0),
        ],
    ) {
        let from_sp = establish_inst.opcode == AArch64Opcode::AddRI
            && matches!(
                establish_inst.operands.as_slice(),
                [
                    MachOperand::PReg(X29),
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::Imm(_),
                ]
            );
        return Err(if from_sp {
            wrong(FrameEnvelopeRole::Establish, establish)
        } else {
            envelope(EnvelopeShape::NoFramePointer)
        });
    }
    // Check every remaining computation and return. Register allocation may
    // leave erased copies: these bounded NOP forms emit no bytes and change
    // no state. All real copies and scratch writes are interpreted separately.
    let ids: Vec<_> = ids[2..ids.len() - 2]
        .iter()
        .chain(ids.last())
        .copied()
        .collect();
    if ids
        .iter()
        .any(|id| names_stack_pointer(&machine.insts[id.0 as usize]))
    {
        return Err(envelope(EnvelopeShape::StackPointerBody));
    }
    Ok(([save, establish, restore], scalar_body(machine, &ids)))
}

/// Whether `inst` reads, writes or addresses through SP.
///
/// The obligation models only the sixteen-byte FP/LR envelope; the body is a
/// scalar computation over registers. A frame with a local area adds SP
/// adjustments, and above the probe threshold `str xzr, [sp]` stack probes and
/// probe-loop blocks. Such a body is refused here, by name, rather than handed
/// to the scalar checker as if it were an ordinary computation.
fn names_stack_pointer(inst: &MachInst) -> bool {
    inst.operands.iter().any(|operand| match operand {
        MachOperand::Special(SpecialReg::SP) => true,
        MachOperand::PReg(reg) => *reg == SP,
        MachOperand::MemOp { base, .. } => *base == SP,
        _ => false,
    })
}

pub(crate) fn scalar_body(machine: &MachFunction, ids: &[InstId]) -> MachFunction {
    let mut body = machine.clone();
    body.insts = ids
        .iter()
        .map(|id| machine.insts[id.0 as usize].clone())
        .filter(|inst| !inert_allocated_nop(inst, machine.next_vreg))
        .collect();
    body.blocks[0].insts = (0..body.insts.len()).map(|n| InstId(n as u32)).collect();
    body.blocks.truncate(1);
    body.blocks[0].preds.clear();
    body.blocks[0].succs.clear();
    body.block_order = vec![body.entry];
    body
}

/// Bytes the frame record occupies below the entry SP: the save allocates
/// them (pre-index `#-16`), the restore releases them (post-index `#16`).
/// The frame theorem and the frame-record contract
/// ([`crate::aarch64_memory_source_binding::ContractAccess::frame_record`])
/// both read this constant.
pub const FRAME_RECORD_BYTES: u64 = 16;

/// Bytes per saved register in the frame record: LR sits one lane above FP.
pub const FRAME_RECORD_LANE_BYTES: u64 = 8;

/// The one spelling of a frame record the owner admits for `role`: the save
/// `STP X29, X30, [SP, #-16]!` or the restore `LDP X29, X30, [SP], #16`, with
/// the opcode's own flags and no implicit operands (`None` for the
/// establishing ADD, which is no record). The envelope check compares the
/// body's pair instructions with exactly these, and
/// [`crate::aarch64_memory_source_binding::frame_record_part_obligations`]
/// decomposes them.
pub fn frame_record_instruction(role: FrameEnvelopeRole) -> Option<MachInst> {
    let record = FRAME_RECORD_BYTES as i64;
    let (opcode, offset) = match role {
        FrameEnvelopeRole::Save => (AArch64Opcode::StpPreIndex, -record),
        FrameEnvelopeRole::Restore => (AArch64Opcode::LdpPostIndex, record),
        FrameEnvelopeRole::Establish => return None,
    };
    Some(MachInst::new(
        opcode,
        vec![
            MachOperand::PReg(X29),
            MachOperand::PReg(X30),
            MachOperand::Special(SpecialReg::SP),
            MachOperand::Imm(offset),
        ],
    ))
}

/// Name of the fixed frame theorem. A database entry alone grants no opcode
/// credit: the verifier still requires the complete source-bound envelope.
pub const FRAME_OBLIGATION_NAME: &str =
    "Source-bound AArch64 leaf: FP/LR frame memory and writeback";

/// The fixed frame theorem, as an SMT obligation over an arbitrary byte
/// memory.
///
/// # Evidence boundary: the theorem is true; the installed checker cannot certify it
///
/// z3 answers `unsat` on the exact query `ay_bridge` generates, so the theorem
/// is true and this encoding is faithful. A current ay also answers `unsat`,
/// with an Alethe proof that has no `hole` or `trust` steps, and still answers
/// `sat` on the wrong-value, wrong-load, wrong-writeback, out-of-frame-store
/// and widened-constant mutations. The tests stay red because the installed
/// authority cannot certify that proof: the installed ay pack answers
/// `unknown`, and the installed Clean checker cannot check the current ay's
/// proof.
///
/// Unblocking needs all three of:
///   1. Clean with the upstream checked array rules and the `zero_extend`
///      normalizer;
///   2. ay advanced PAIRED with that Clean (an unpaired ay advance emits
///      proofs the pinned Clean cannot read, and has turned a 25 s census into
///      a 3 h timeout); and
///   3. that Clean in the checker actually selected:
///      `default_clean_checker_candidates()` tries the owning Trust toolchain's
///      `clean` first and aterm's packaged `clean` only as a fallback, so on a
///      Trust-built process the toolchain's `clean` must be new enough, and
///      republishing the atpkg pack alone does not close this.
///
/// Do NOT close this by classifying the gate refusal as a certification gap,
/// by reshaping the formula until a solver defect stops firing (the
/// `ite`/uninterpreted-function encoding and reversed store order both hide
/// the defect without reaching a verdict), or by relaxing the obligation.
/// Measurements: `reports/2026-09-21-frame-layout-ay-authority-gap/`, commit
/// `9002ea21b`, and `docs/archive/session-reports/2026-09-25-frame-layout-checker-pack.md`.
///
/// Exported (not `pub(crate)`) so the corpus ratchet
/// `source_bound_leaf_frame_corpus_addition_is_exact_live_and_nondegenerate`
/// in `tests/proof_gate_strict.rs` can bind its corpus row to the
/// constructor that produces it rather than to its name and category,
/// which any long-standing `FrameLayout` row satisfies. This matches the
/// visibility every other proof constructor in the crate already has
/// (`frame_proofs`, `atomic_proofs`); exporting the theorem grants no opcode
/// credit, exactly as the paragraph above states.
pub fn frame_obligation() -> ProofObligation {
    let sp = SmtExpr::var("entry_sp", 64);
    let fp = SmtExpr::var("entry_fp", 64);
    let lr = SmtExpr::var("entry_lr", 64);
    let observe = SmtExpr::var("observe", 64);
    // A zero-argument SMT function is an arbitrary array-valued constant.
    // It represents initial memory only; no instruction is an uninterpreted
    // function and no constant-default memory approximation is involved.
    let memory = SmtExpr::uf("entry_memory", Vec::new(), memory_sort());
    let frame = sp.clone().bvsub(SmtExpr::bv_const(FRAME_RECORD_BYTES, 64));
    let second = frame
        .clone()
        .bvadd(SmtExpr::bv_const(FRAME_RECORD_LANE_BYTES, 64));
    let saved_first = encode_store_le(&memory, &frame, &fp, 8);
    let saved_both = encode_store_le(&saved_first, &second, &lr, 8);
    let restored_fp = encode_load_le(&saved_both, &frame, 8);
    let restored_lr = encode_load_le(&saved_both, &second, 8);
    let restored_sp = frame
        .clone()
        .bvadd(SmtExpr::bv_const(FRAME_RECORD_BYTES, 64));
    let outside = observe
        .clone()
        .bvult(frame)
        .or_expr(observe.clone().bvuge(sp.clone()));
    let memory_preserved = outside.not_expr().or_expr(
        SmtExpr::select(saved_both, observe.clone()).eq_expr(SmtExpr::select(memory, observe)),
    );
    let complete = restored_fp
        .eq_expr(fp)
        .and_expr(restored_lr.eq_expr(lr))
        .and_expr(restored_sp.eq_expr(sp.clone()))
        .and_expr(memory_preserved);
    ProofObligation {
        name: FRAME_OBLIGATION_NAME.into(),
        trust_ir_expr: SmtExpr::bool_const(true),
        aarch64_expr: complete,
        inputs: ["entry_sp", "entry_fp", "entry_lr", "observe"]
            .into_iter()
            .map(|name| (name.into(), 64))
            .collect(),
        preconditions: vec![
            sp.clone().bvuge(SmtExpr::bv_const(FRAME_RECORD_BYTES, 64)),
            sp.bvand(SmtExpr::bv_const(15, 64))
                .eq_expr(SmtExpr::bv_const(0, 64)),
        ],
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::RegisterAllocation),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::function::{Signature, Type};
    use trust_cg_ir::regs::{X0, X1, X19};
    use trust_cg_lower::function::BasicBlock;
    use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};

    fn fixture() -> (Function, MachFunction) {
        let mut source = Function::new(
            "framed_leaf",
            trust_cg_lower::function::Signature {
                params: vec![],
                returns: vec![trust_cg_lower::Type::I64],
            },
        );
        source.blocks.insert(
            source.entry_block,
            BasicBlock {
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Iconst {
                            imm: 42,
                            ty: trust_cg_lower::Type::I64,
                        },
                        args: vec![],
                        results: vec![Value(0)],
                    },
                    Instruction {
                        opcode: Opcode::Return,
                        args: vec![Value(0)],
                        results: vec![],
                    },
                ],
                ..BasicBlock::default()
            },
        );
        let mut machine =
            MachFunction::new(source.name.clone(), Signature::new(vec![], vec![Type::I64]));
        for (opcode, operands) in [
            (
                AArch64Opcode::StpPreIndex,
                vec![
                    MachOperand::PReg(X29),
                    MachOperand::PReg(X30),
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::Imm(-16),
                ],
            ),
            (
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::PReg(X29),
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::Imm(0),
                ],
            ),
            (
                AArch64Opcode::Movz,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::Imm(42),
                    MachOperand::Imm(0),
                ],
            ),
            (
                AArch64Opcode::LdpPostIndex,
                vec![
                    MachOperand::PReg(X29),
                    MachOperand::PReg(X30),
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::Imm(16),
                ],
            ),
            (AArch64Opcode::Ret, vec![MachOperand::PReg(X30)]),
        ] {
            let id = machine.push_inst(MachInst::new(opcode, operands));
            machine.append_inst(machine.entry, id);
        }
        (source, machine)
    }

    fn linear_fixture() -> (Function, MachFunction, InstId) {
        let (mut source, mut machine) = fixture();
        let header = source.blocks.get_mut(&source.entry_block).unwrap();
        let ret = header.instructions.pop().unwrap();
        header.instructions.push(Instruction {
            opcode: Opcode::Jump { dest: Block(1) },
            args: vec![],
            results: vec![],
        });
        source.blocks.insert(
            Block(1),
            BasicBlock {
                instructions: vec![ret],
                ..Default::default()
            },
        );
        source.block_order = vec![source.entry_block, Block(1)];
        let exit = machine.create_block();
        let branch = machine.push_inst(MachInst::new(AArch64Opcode::B, vec![MachOperand::Imm(1)]));
        machine.blocks[0].insts = vec![InstId(0), InstId(1), InstId(2), branch];
        machine.blocks[0].succs = vec![exit];
        machine.blocks[exit.0 as usize].insts = vec![InstId(3), InstId(4)];
        machine.blocks[exit.0 as usize].preds = vec![machine.entry];
        (source, machine, branch)
    }

    fn frameless_linear_fixture() -> (Function, MachFunction, InstId) {
        let (source, mut machine, branch) = linear_fixture();
        machine.insts = vec![
            machine.insts[2].clone(),
            machine.insts[branch.0 as usize].clone(),
            machine.insts[4].clone(),
        ];
        machine.blocks[0].insts = vec![InstId(0), InstId(1)];
        machine.blocks[1].insts = vec![InstId(2)];
        (source, machine, InstId(1))
    }

    #[test]
    fn frameless_control_binds_complete_routing_and_credits_only_branches() {
        use crate::source_bound_a64_control::{CheckedFramelessLinear, SourceBoundA64Control};
        let (source, machine, branch) = frameless_linear_fixture();
        assert!(source_admits_frame_owner(&source));
        assert!(!source_requires_frame_proof_envelope(&source));
        let checked = CheckedFramelessLinear::bind(&source, &machine).unwrap();
        let control = SourceBoundA64Control::bind_frameless(&checked).unwrap();
        assert!(!control.obligation().is_degenerate());
        assert!(control.obligation().name.contains("frameless control"));
        for index in 0..machine.insts.len() {
            assert_eq!(
                control.credits(InstId(index as u32)),
                InstId(index as u32) == branch
            );
        }
        assert!(control.replay_reason().contains("independently replayed"));
    }

    #[test]
    fn frameless_control_refuses_bad_values_edges_effects_and_unowned_rows() {
        use crate::source_bound_a64_control::CheckedFramelessLinear;
        let (source, machine, branch) = frameless_linear_fixture();
        for mutation in 0..8 {
            let mut source = source.clone();
            let mut machine = machine.clone();
            match mutation {
                0 => machine.insts[branch.0 as usize].operands[0] = MachOperand::Imm(0),
                1 => {
                    source
                        .blocks
                        .get_mut(&source.entry_block)
                        .unwrap()
                        .instructions[1]
                        .opcode = Opcode::Jump {
                        dest: source.entry_block,
                    }
                }
                2 => machine.insts[0].operands[1] = MachOperand::Imm(43),
                3 => machine.insts[0].operands[0] = MachOperand::PReg(X1),
                4 => machine.insts[0].operands[0] = MachOperand::PReg(X19),
                5 => machine.insts[branch.0 as usize].implicit_defs = &[X0],
                6 => machine.insts.push(MachInst::new(
                    AArch64Opcode::Movz,
                    vec![
                        MachOperand::PReg(X1),
                        MachOperand::Imm(1),
                        MachOperand::Imm(0),
                    ],
                )),
                _ => machine.insts[2].operands[0] = MachOperand::PReg(X0),
            }
            assert!(
                CheckedFramelessLinear::bind(&source, &machine).is_err(),
                "mutation {mutation} gained binding"
            );
        }
    }

    #[test]
    fn frameless_identity_return_routing_is_checked_without_value_credit() {
        use crate::source_bound_a64_control::{CheckedFramelessLinear, SourceBoundA64Control};
        let (mut source, mut machine, _) = frameless_linear_fixture();
        source.signature.params = vec![trust_cg_lower::Type::I64; 2];
        let entry = source.blocks.get_mut(&source.entry_block).unwrap();
        entry.params = vec![
            (Value(0), trust_cg_lower::Type::I64),
            (Value(1), trust_cg_lower::Type::I64),
        ];
        entry.instructions.remove(0);
        source.blocks.get_mut(&Block(1)).unwrap().instructions[0].args = vec![Value(0)];
        machine.signature.params = vec![Type::I64; 2];
        machine.insts.remove(0);
        machine.blocks[0].insts = vec![InstId(0)];
        machine.blocks[1].insts = vec![InstId(1)];
        let checked = CheckedFramelessLinear::bind(&source, &machine).unwrap();
        let control = SourceBoundA64Control::bind_frameless(&checked).unwrap();
        assert!(control.credits(InstId(0)));
        assert!(!control.credits(InstId(1)));
        source.blocks.get_mut(&Block(1)).unwrap().instructions[0].args = vec![Value(1)];
        assert!(matches!(
            CheckedFramelessLinear::bind(&source, &machine),
            Err(SourceBoundFrameRefusal::Mismatch(
                FrameBindingMismatch::Body(_)
            ))
        ));

        // No branch means no control theorem. The exact return routing still
        // must be checked; no identity/copy instruction proof is invented.
        source.blocks.get_mut(&Block(1)).unwrap().instructions[0].args = vec![Value(0)];
        let mut flat = linear::source_view(&source).unwrap();
        machine.insts.remove(0);
        machine.blocks.truncate(1);
        machine.blocks[0].insts = vec![InstId(0)];
        machine.blocks[0].succs.clear();
        machine.block_order = vec![machine.entry];
        let checked = CheckedFramelessLinear::bind(&flat, &machine).unwrap();
        assert!(SourceBoundA64Control::bind_frameless(&checked).is_none());
        let verifier = crate::FunctionVerifier::new();
        let request = verifier
            .capture_request_with_mode(crate::provenance_xcheck::ProvenanceXCheckMode::Enforce);
        let captured = verifier.verify_with_request(&machine, Some(&flat), &request);
        assert_eq!(captured.report().genuinely_verified_count(), 0);
        assert!(
            captured
                .checked_aarch64_structural_return(&machine, &flat)
                .is_some()
        );
        assert!(!captured.reusable_for(&request));
        let source_less = verifier.verify_with_request(&machine, None, &request);
        assert!(
            source_less
                .checked_aarch64_structural_return(&machine, &flat)
                .is_none()
        );
        let mut real_nop = machine.clone();
        let id = real_nop.push_inst(MachInst::new(AArch64Opcode::Nop, vec![]));
        real_nop.insts[id.0 as usize].flags = InstFlags::EMPTY;
        real_nop.blocks[0].insts.insert(0, id);
        let nops = verifier.verify_with_request(&real_nop, Some(&flat), &request);
        assert!(
            nops.checked_aarch64_structural_return(&real_nop, &flat)
                .is_none()
        );
        let mut wrong_lr = machine.clone();
        wrong_lr.insts[0].operands = vec![MachOperand::PReg(X0)];
        assert!(
            captured
                .checked_aarch64_structural_return(&wrong_lr, &flat)
                .is_none()
        );
        let wrong_lr_report = verifier.verify_with_request(&wrong_lr, Some(&flat), &request);
        assert!(
            wrong_lr_report
                .checked_aarch64_structural_return(&wrong_lr, &flat)
                .is_none()
        );

        flat.blocks
            .get_mut(&flat.entry_block)
            .unwrap()
            .instructions
            .last_mut()
            .unwrap()
            .args = vec![Value(1)];
        assert!(CheckedFramelessLinear::bind(&flat, &machine).is_err());
        assert!(
            captured
                .checked_aarch64_structural_return(&machine, &flat)
                .is_none()
        );
        let wrong_source = verifier.verify_with_request(&machine, Some(&flat), &request);
        assert!(
            wrong_source
                .checked_aarch64_structural_return(&machine, &flat)
                .is_none()
        );
    }

    #[test]
    fn framed_control_binds_edges_and_credits_only_branches() {
        let (source, machine, branch) = linear_fixture();
        let frame = source_bound_frame(&source, &machine).unwrap();
        let control = crate::source_bound_a64_control::SourceBoundA64Control::bind(&frame)
            .expect("source edge and decoded B share the same destination");
        assert!(control.credits(branch));
        for index in 0..machine.insts.len() {
            assert_eq!(
                control.credits(InstId(index as u32)),
                InstId(index as u32) == branch
            );
        }
        assert!(!control.obligation().is_degenerate());
        let query = crate::ay_bridge::generate_smt2_query_raw(
            control.obligation(),
            &crate::ay_bridge::AYConfig::default(),
        );
        assert!(query.contains("image_base"));
        assert!(query.contains("sign_extend 36"));
        assert!(query.contains("concat"));
    }

    #[test]
    fn framed_control_rejects_source_target_frame_and_effect_mutations() {
        let (source, machine, branch) = linear_fixture();
        for mutation in 0..6 {
            let mut source = source.clone();
            let mut machine = machine.clone();
            match mutation {
                0 => machine.insts[branch.0 as usize].operands[0] = MachOperand::Imm(0),
                1 => {
                    source
                        .blocks
                        .get_mut(&source.entry_block)
                        .unwrap()
                        .instructions[1]
                        .opcode = Opcode::Jump {
                        dest: source.entry_block,
                    }
                }
                2 => machine.blocks[0].succs = vec![machine.entry],
                3 => machine.insts[branch.0 as usize].implicit_defs = &[X0],
                4 => machine.insts[0].operands[3] = MachOperand::Imm(-32),
                _ => machine.insts[branch.0 as usize].flags |= InstFlags::IS_PSEUDO,
            }
            if let Ok(frame) = source_bound_frame(&source, &machine) {
                assert!(
                    crate::source_bound_a64_control::SourceBoundA64Control::bind(&frame).is_none(),
                    "mutation {mutation} reached control ownership"
                );
            }
        }
    }

    #[test]
    fn framed_control_requires_original_edges_even_when_return_values_match() {
        let (mut source, mut machine, _) = linear_fixture();
        let ret = source
            .blocks
            .get_mut(&Block(1))
            .unwrap()
            .instructions
            .pop()
            .unwrap();
        source
            .blocks
            .get_mut(&Block(1))
            .unwrap()
            .instructions
            .push(Instruction {
                opcode: Opcode::Jump { dest: Block(2) },
                args: vec![],
                results: vec![],
            });
        source.blocks.insert(
            Block(2),
            BasicBlock {
                instructions: vec![ret],
                ..Default::default()
            },
        );
        source.block_order.push(Block(2));

        // Both complete chains return 42, but the source takes 0->1->2 and
        // the machine takes 0->2->1. A value-only match does not establish
        // the explicit block-address correspondence of this PC theorem.
        let exit = BlockId(1);
        let middle = machine.create_block();
        assert_eq!(middle, BlockId(2));
        let jump = machine.push_inst(MachInst::new(AArch64Opcode::B, vec![MachOperand::Imm(1)]));
        machine.append_inst(middle, jump);
        machine.blocks[0].succs = vec![middle];
        machine.blocks[middle.0 as usize].preds = vec![machine.entry];
        machine.blocks[middle.0 as usize].succs = vec![exit];
        machine.blocks[exit.0 as usize].preds = vec![middle];
        machine.block_order = vec![machine.entry, middle, exit];
        let frame = source_bound_frame(&source, &machine)
            .expect("the existing affine frame owner compares the flattened value chains");
        assert!(crate::source_bound_a64_control::SourceBoundA64Control::bind(&frame).is_none());
    }

    #[test]
    fn framed_control_identity_keeps_the_noncomputing_body_guard() {
        let (mut source, mut machine, branch) = linear_fixture();
        source.signature.params = vec![trust_cg_lower::Type::I64];
        let entry = source.blocks.get_mut(&source.entry_block).unwrap();
        entry.params = vec![(Value(0), trust_cg_lower::Type::I64)];
        entry.instructions[0] = Instruction {
            opcode: Opcode::Copy,
            args: vec![Value(0)],
            results: vec![Value(1)],
        };
        source.blocks.get_mut(&Block(1)).unwrap().instructions[0].args = vec![Value(1)];
        machine.signature.params = vec![Type::I64];
        machine.insts[2] = MachInst::new(
            AArch64Opcode::Nop,
            vec![MachOperand::PReg(X0), MachOperand::PReg(X0)],
        );
        machine.insts[2].flags = InstFlags::IS_PSEUDO;
        let frame = source_bound_frame(&source, &machine).unwrap();
        assert!(crate::source_bound_body::SourceBoundBody::bind(&frame).is_none());
        let control = crate::source_bound_a64_control::SourceBoundA64Control::bind(&frame)
            .expect("identity body still has a non-vacuous branch PC observable");
        assert!(control.credits(branch));
        assert!(!control.credits(InstId(2)));
        assert!(!control.obligation().is_degenerate());
    }

    #[test]
    fn framed_control_live_replay_handles_backward_layout_and_nops() {
        use crate::function_verifier::{FunctionVerifier, InstructionVerificationResult};
        use crate::lowering_proof::VerificationConfig;
        use crate::provenance_xcheck::ProvenanceXCheckMode;
        use crate::verify::VerificationStrength;

        crate::ay_identity::resolve_for_process().expect("authenticated AY is required");
        crate::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "1")], || {
            for flags in [InstFlags::EMPTY, InstFlags::IS_PSEUDO] {
                let (mut source, mut machine, forward) = linear_fixture();
                let middle = source.blocks.get_mut(&Block(1)).unwrap();
                let ret = middle.instructions.pop().unwrap();
                middle.instructions.push(Instruction {
                    opcode: Opcode::Jump { dest: Block(2) },
                    args: vec![],
                    results: vec![],
                });
                source.blocks.insert(
                    Block(2),
                    BasicBlock {
                        instructions: vec![ret],
                        ..Default::default()
                    },
                );
                source.block_order.push(Block(2));

                let middle = BlockId(1);
                let exit = machine.create_block();
                assert_eq!(exit, BlockId(2));
                let mut nop = MachInst::new(AArch64Opcode::Nop, vec![]);
                nop.flags = flags;
                let nop = machine.push_inst(nop);
                let exit_words = if flags == InstFlags::EMPTY { 3 } else { 2 };
                let backward = machine.push_inst(MachInst::new(
                    AArch64Opcode::B,
                    vec![MachOperand::Imm(-exit_words)],
                ));
                machine.insts[forward.0 as usize].operands[0] = MachOperand::Imm(exit_words + 1);
                machine.blocks[middle.0 as usize].insts = vec![backward];
                machine.blocks[middle.0 as usize].succs = vec![exit];
                machine.blocks[exit.0 as usize].insts = vec![nop, InstId(3), InstId(4)];
                machine.blocks[exit.0 as usize].preds = vec![middle];
                // Source edges remain 0->1->2. Physical layout is 0,2,1:
                // the second B goes backward over the exact emitted exit.
                machine.block_order = vec![machine.entry, exit, middle];
                let frame = source_bound_frame(&source, &machine).unwrap();
                let control = crate::source_bound_a64_control::SourceBoundA64Control::bind(&frame)
                    .expect("decoded signed displacements match the original source edges");
                assert!(control.credits(forward));
                assert!(control.credits(backward));
                assert!(!control.credits(nop));
                assert!(!control.obligation().is_degenerate());

                for displacement in [0, exit_words, -4 * exit_words] {
                    let mut wrong = machine.clone();
                    wrong.insts[backward.0 as usize].operands[0] = MachOperand::Imm(displacement);
                    if let Ok(frame) = source_bound_frame(&source, &wrong) {
                        assert!(
                            crate::source_bound_a64_control::SourceBoundA64Control::bind(&frame)
                                .is_none()
                        );
                    }
                }

                let verifier =
                    FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
                let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
                let captured = verifier.verify_with_request(&machine, Some(&source), &request);
                assert!(captured.matches_aarch64_input(&machine, Some(&source)));
                for branch in [forward, backward] {
                    let row = captured
                        .report()
                        .instructions
                        .iter()
                        .find(|row| row.inst_index == branch.0 as usize)
                        .unwrap();
                    assert!(
                        matches!(&row.result,
                            InstructionVerificationResult::Verified {
                                proof_name,
                                category: crate::proof_database::ProofCategory::Branch,
                                strength: VerificationStrength::Formal,
                                degenerate: false,
                            } if proof_name.starts_with("Source-bound AArch64 framed control theorem")
                        ),
                        "{:?}",
                        row.result
                    );
                }
            }
        });
    }

    #[test]
    fn framed_control_live_replay_credits_the_bound_branch() {
        use crate::function_verifier::{FunctionVerifier, InstructionVerificationResult};
        use crate::lowering_proof::VerificationConfig;
        use crate::provenance_xcheck::ProvenanceXCheckMode;
        use crate::verify::VerificationStrength;

        crate::ay_identity::resolve_for_process().expect("authenticated AY is required");
        crate::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "1")], || {
            let (source, machine, branch) = linear_fixture();
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            let captured = verifier.verify_with_request(&machine, Some(&source), &request);
            assert!(captured.matches_aarch64_input(&machine, Some(&source)));
            let row = captured
                .report()
                .instructions
                .iter()
                .find(|row| row.inst_index == branch.0 as usize)
                .unwrap();
            assert!(
                matches!(
                    &row.result,
                    InstructionVerificationResult::Verified {
                        proof_name,
                        category: crate::proof_database::ProofCategory::Branch,
                        strength: VerificationStrength::Formal,
                        degenerate: false,
                    } if proof_name.starts_with("Source-bound AArch64 framed control theorem")
                ),
                "{:?}",
                row.result
            );
        });
    }

    #[test]
    fn linear_frame_checks_complete_source_chain() {
        let (source, machine, _) = linear_fixture();
        assert!(source_bound_frame(&source, &machine).is_ok());
        for mutation in 0..10 {
            let mut wrong = source.clone();
            match mutation {
                0 => {
                    wrong
                        .blocks
                        .get_mut(&wrong.entry_block)
                        .unwrap()
                        .instructions[1]
                        .opcode = Opcode::Jump {
                        dest: wrong.entry_block,
                    }
                }
                1 => {
                    wrong
                        .blocks
                        .get_mut(&wrong.entry_block)
                        .unwrap()
                        .instructions[1]
                        .opcode = Opcode::Jump { dest: Block(99) }
                }
                2 => wrong
                    .blocks
                    .get_mut(&wrong.entry_block)
                    .unwrap()
                    .instructions[1]
                    .args
                    .push(Value(0)),
                3 => wrong
                    .blocks
                    .get_mut(&wrong.entry_block)
                    .unwrap()
                    .instructions[1]
                    .results
                    .push(Value(9)),
                4 => wrong
                    .blocks
                    .get_mut(&Block(1))
                    .unwrap()
                    .params
                    .push((Value(9), trust_cg_lower::Type::I64)),
                5 => {
                    wrong.blocks.insert(Block(2), BasicBlock::default());
                }
                6 => wrong.block_order[1] = wrong.entry_block,
                7 => {
                    let header = wrong.blocks.get_mut(&wrong.entry_block).unwrap();
                    header.instructions.insert(
                        1,
                        Instruction {
                            opcode: Opcode::Iconst {
                                imm: 1,
                                ty: trust_cg_lower::Type::B1,
                            },
                            args: vec![],
                            results: vec![Value(1)],
                        },
                    );
                    header.instructions[2].opcode = Opcode::Brif {
                        cond: Value(1),
                        then_dest: Block(1),
                        else_dest: Block(1),
                    };
                }
                8 => wrong.blocks.get_mut(&Block(1)).unwrap().instructions[0].args[0] = Value(99),
                _ => {
                    wrong
                        .blocks
                        .get_mut(&wrong.entry_block)
                        .unwrap()
                        .instructions[0]
                        .opcode = Opcode::Iconst {
                        imm: 43,
                        ty: trust_cg_lower::Type::I64,
                    }
                }
            }
            assert!(
                source_bound_frame(&wrong, &machine).is_err(),
                "source mutation {mutation}"
            );
        }
    }

    #[test]
    fn linear_frame_checks_actual_branch_offsets_and_cfg() {
        let (source, machine, branch) = linear_fixture();
        for mutation in 0..15 {
            let mut wrong = machine.clone();
            match mutation {
                0..=3 => {
                    wrong.insts[branch.0 as usize].operands[0] =
                        MachOperand::Imm([2, 0, -3, 1 << 25][mutation])
                }
                4 => {
                    wrong.insts[branch.0 as usize].operands[0] =
                        MachOperand::Symbol("outside".into())
                }
                5 => wrong.blocks[0].succs.clear(),
                6 => wrong.blocks[1].preds.clear(),
                7 => wrong.block_order.swap(0, 1),
                8 => wrong.entry = trust_cg_ir::BlockId(1),
                9 => wrong.blocks[1].insts.insert(0, InstId(2)),
                10 => wrong.blocks[1].insts.push(InstId(999)),
                11 => wrong.insts[branch.0 as usize].implicit_defs = &[X0],
                12 => wrong.insts[branch.0 as usize].flags = InstFlags::EMPTY,
                13 => {
                    wrong.create_block();
                }
                _ => wrong.insts[2].operands[1] = MachOperand::Imm(43),
            }
            assert!(
                source_bound_frame(&source, &wrong).is_err(),
                "machine mutation {mutation}"
            );
        }
    }

    #[test]
    fn linear_frame_follows_symbolic_branches_and_layout_fallthrough() {
        let (source, mut machine, branch) = linear_fixture();
        machine.insts[branch.0 as usize].operands[0] = MachOperand::Block(trust_cg_ir::BlockId(1));
        assert!(source_bound_frame(&source, &machine).is_ok());
        machine.insts[branch.0 as usize] = MachInst::new(AArch64Opcode::Nop, vec![]);
        assert!(source_bound_frame(&source, &machine).is_ok());
    }

    #[test]
    fn reordered_linear_frame_binds_real_and_pseudo_nop_word_offsets() {
        for flags in [InstFlags::EMPTY, InstFlags::IS_PSEUDO] {
            let (source, mut machine) = fixture();
            let body = machine.create_block();
            let exit = machine.create_block();
            machine.block_order = vec![machine.entry, exit, body];
            let mut nop = MachInst::new(AArch64Opcode::Nop, vec![]);
            nop.flags = flags;
            let nop = machine.push_inst(nop);
            let offset = if flags == InstFlags::EMPTY { 4 } else { 3 };
            let enter = machine.push_inst(MachInst::new(
                AArch64Opcode::B,
                vec![MachOperand::Imm(offset)],
            ));
            let leave = machine.push_inst(MachInst::new(
                AArch64Opcode::B,
                vec![MachOperand::Imm(-offset)],
            ));
            machine.blocks[0].insts = vec![InstId(0), InstId(1), enter];
            machine.blocks[0].succs = vec![body];
            machine.blocks[body.0 as usize].insts = vec![InstId(2), leave];
            machine.blocks[body.0 as usize].preds = vec![machine.entry];
            machine.blocks[body.0 as usize].succs = vec![exit];
            machine.blocks[exit.0 as usize].insts = vec![nop, InstId(3), InstId(4)];
            machine.blocks[exit.0 as usize].preds = vec![body];
            assert!(source_bound_frame(&source, &machine).is_ok());

            // The old opcode-only count accepted +3/-3 even with a real NOP.
            // In that case B+3 actually lands on RET before the value/restore.
            let wrong_offset = if flags == InstFlags::EMPTY { 3 } else { 4 };
            machine.insts[enter.0 as usize].operands[0] = MachOperand::Imm(wrong_offset);
            machine.insts[leave.0 as usize].operands[0] = MachOperand::Imm(-wrong_offset);
            assert!(source_bound_frame(&source, &machine).is_err());
        }
    }

    #[test]
    fn linear_frame_allows_only_empty_merged_block_remnants() {
        let (source, _, _) = linear_fixture();
        let (_, mut machine) = fixture();
        let inactive = machine.create_block();
        machine.block_order.pop();
        let branch = machine.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(inactive)],
        ));
        assert!(source_bound_frame(&source, &machine).is_ok());
        for mutation in 0..5 {
            let mut wrong = machine.clone();
            match mutation {
                0 => wrong.insts[branch.0 as usize].operands[0] = MachOperand::Block(machine.entry),
                1 => wrong.insts[branch.0 as usize].implicit_uses = &[X0],
                2 => wrong.insts[branch.0 as usize].flags = InstFlags::HAS_SIDE_EFFECTS,
                3 => wrong.blocks[inactive.0 as usize].preds.push(machine.entry),
                _ => wrong.blocks[inactive.0 as usize].insts.push(InstId(2)),
            }
            assert!(
                source_bound_frame(&source, &wrong).is_err(),
                "remnant mutation {mutation}"
            );
        }
    }

    #[test]
    fn final_frame_body_rejects_unemitted_pseudo_copies() {
        let (source, mut machine) = fixture();
        machine.insts[2].operands[0] = MachOperand::PReg(X1);
        let copy = machine.push_inst(MachInst::new(
            AArch64Opcode::Copy,
            vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
        ));
        machine.blocks[0].insts.insert(3, copy);
        // A pseudo copy would change the abstract register state but emits no
        // move. The final-body interpreter must not credit that computation.
        assert!(source_bound_frame(&source, &machine).is_err());
    }

    #[test]
    fn source_bound_frame_requires_exact_body_and_source() {
        let (source, machine) = fixture();
        let checked = source_bound_frame(&source, &machine).expect("valid framed leaf");
        assert!(std::ptr::eq(checked.source(), &source));
        assert!(std::ptr::eq(checked.machine(), &machine));
        assert_eq!(checked.pair_instructions(), [InstId(0), InstId(3)]);
        for value in [0, 41, 43, -1] {
            let mut wrong = machine.clone();
            wrong.insts[2].operands[1] = MachOperand::Imm(value);
            assert!(
                source_bound_frame(&source, &wrong).is_err(),
                "wrong constant {value}"
            );
        }
        let mut wrong_source = source.clone();
        wrong_source
            .blocks
            .get_mut(&source.entry_block)
            .unwrap()
            .instructions[0]
            .opcode = Opcode::Iconst {
            imm: 43,
            ty: trust_cg_lower::Type::I64,
        };
        assert!(source_bound_frame(&wrong_source, &machine).is_err());
        wrong_source.name = "different source".into();
        assert!(source_bound_frame(&wrong_source, &machine).is_err());
    }

    /// Frame lowering drops an envelope kept only for this owner when the
    /// owner never judges the source. That query must be the binder's own
    /// applicability check: an admitted source is judged against its machine
    /// code, and an inadmissible one is unsupported before any machine
    /// instruction is inspected, whatever the frame looks like.
    #[test]
    fn frame_owner_applicability_is_decided_by_the_source_alone() {
        let (source, machine) = fixture();
        assert!(source_admits_frame_owner(&source));
        assert!(source_bound_frame(&source, &machine).is_ok());

        let mut multiply = source.clone();
        let block = multiply.blocks.get_mut(&multiply.entry_block).unwrap();
        block.instructions.insert(
            1,
            Instruction {
                opcode: Opcode::Imul,
                args: vec![Value(0), Value(0)],
                results: vec![Value(1)],
            },
        );
        block.instructions[2].args = vec![Value(1)];
        assert!(!source_admits_frame_owner(&multiply));
        assert!(matches!(
            unsupported_shape(&multiply, &machine),
            FrameShapeUnsupported::SourceDomain(_)
        ));

        // A two-block cycle is neither a bounded chain nor a diamond.
        let mut looping = source.clone();
        let entry = looping.entry_block;
        let next = Block(entry.0 + 1);
        let jump = |dest| Instruction {
            opcode: Opcode::Jump { dest },
            args: vec![],
            results: vec![],
        };
        looping.blocks.get_mut(&entry).unwrap().instructions[1] = jump(next);
        looping.blocks.insert(
            next,
            BasicBlock {
                instructions: vec![jump(entry)],
                ..BasicBlock::default()
            },
        );
        assert!(!source_admits_frame_owner(&looping));
        assert_eq!(
            unsupported_shape(&looping, &machine),
            FrameShapeUnsupported::SourceShape
        );
    }

    #[test]
    fn source_bound_frame_refuses_every_pair_operand_mutation() {
        let (source, machine) = fixture();
        for index in [0, 3] {
            for (operand, replacement) in [
                (0, MachOperand::PReg(X19)),
                (1, MachOperand::PReg(X29)),
                (1, MachOperand::PReg(X1)),
                (2, MachOperand::PReg(X29)),
                (3, MachOperand::Imm(0)),
                (3, MachOperand::Imm(8)),
                (3, MachOperand::Imm(24)),
            ] {
                let mut wrong = machine.clone();
                wrong.insts[index].operands[operand] = replacement;
                assert!(
                    source_bound_frame(&source, &wrong).is_err(),
                    "instruction {index}, operand {operand}"
                );
            }
            let mut wrong = machine.clone();
            wrong.insts[index].implicit_defs = &[X19];
            assert!(source_bound_frame(&source, &wrong).is_err());
        }
    }

    #[test]
    fn source_bound_frame_refuses_probed_and_adjusted_frames() {
        let (source, machine) = fixture();
        assert!(source_bound_frame(&source, &machine).is_ok());
        let sp = || MachOperand::Special(SpecialReg::SP);
        let adjust =
            |opcode, bytes| MachInst::new(opcode, vec![sp(), sp(), MachOperand::Imm(bytes)]);
        let probe = || {
            MachInst::new(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(trust_cg_ir::regs::XZR),
                    sp(),
                    MachOperand::Imm(0),
                ],
            )
        };
        // Frame lowering's 4096-byte probed local area around the body, the
        // bare probe, and an SP adjustment alone: each is refused by name.
        let shapes: [Vec<MachInst>; 3] = [
            vec![
                adjust(AArch64Opcode::SubRI, 4080),
                adjust(AArch64Opcode::SubRI, 16),
                probe(),
                adjust(AArch64Opcode::AddRI, 4080),
                adjust(AArch64Opcode::AddRI, 16),
            ],
            vec![probe()],
            vec![
                adjust(AArch64Opcode::SubRI, 16),
                adjust(AArch64Opcode::AddRI, 16),
            ],
        ];
        for shape in shapes {
            assert!(shape.iter().all(names_stack_pointer));
            let mut wrong = machine.clone();
            let ids: Vec<_> = shape
                .into_iter()
                .map(|inst| wrong.push_inst(inst))
                .collect();
            let body = &mut wrong.blocks[0].insts;
            for (offset, id) in ids.into_iter().enumerate() {
                body.insert(2 + offset, id);
            }
            let chain = wrong.blocks[0].insts.clone();
            assert!(frame_body(&wrong, &chain).is_err());
            assert!(source_bound_frame(&source, &wrong).is_err());
        }
        // The admitted body itself never names SP.
        assert!(!names_stack_pointer(&machine.insts[2]));
    }

    #[test]
    fn source_bound_frame_refuses_hidden_state_and_malformed_ownership() {
        let (source, machine) = fixture();
        let mut wrong = machine.clone();
        wrong.blocks[0].insts[2] = InstId(u32::MAX);
        assert!(source_bound_frame(&source, &wrong).is_err());
        wrong.blocks[0].insts[2] = InstId(0);
        assert!(source_bound_frame(&source, &wrong).is_err());
        for operands in [
            vec![
                MachOperand::PReg(X19),
                MachOperand::Imm(42),
                MachOperand::Imm(0),
            ],
            vec![
                MachOperand::PReg(X30),
                MachOperand::Imm(42),
                MachOperand::Imm(0),
            ],
        ] {
            let mut wrong = machine.clone();
            wrong.insts[2].operands = operands;
            assert!(source_bound_frame(&source, &wrong).is_err());
        }
        let mut wrong = machine.clone();
        wrong.insts[2] = MachInst::new(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::Imm(0),
            ],
        );
        assert!(source_bound_frame(&source, &wrong).is_err());
        let mut wrong = machine.clone();
        wrong.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        assert!(source_bound_frame(&source, &wrong).is_err());
    }

    #[test]
    fn source_bound_frame_checks_erased_copy_operands_and_effects() {
        let (source, mut machine) = fixture();
        let mut copy = MachInst::new(
            AArch64Opcode::Nop,
            vec![MachOperand::PReg(X0), MachOperand::PReg(X0)],
        );
        copy.flags = InstFlags::IS_PSEUDO;
        let id = machine.push_inst(copy);
        machine.blocks[0].insts.insert(3, id);
        assert!(source_bound_frame(&source, &machine).is_ok());
        for mutation in 0..5 {
            let mut wrong = machine.clone();
            let copy = &mut wrong.insts[id.0 as usize];
            match mutation {
                0 => copy.operands[1] = MachOperand::PReg(X1),
                1 => copy.flags = InstFlags::HAS_SIDE_EFFECTS,
                2 => copy.implicit_defs = &[X0],
                3 => copy.implicit_uses = &[X19],
                _ => copy.operands = vec![MachOperand::Imm(0), MachOperand::Imm(0)],
            }
            assert!(source_bound_frame(&source, &wrong).is_err());
        }
        machine.insts[2].operands[1] = MachOperand::Imm(43);
        assert!(source_bound_frame(&source, &machine).is_err());
    }

    #[test]
    fn allocated_scratch_and_move_widths_bind_actual_values() {
        use trust_cg_ir::regs::{PReg, W0, W2, X2, X3};
        let (source, mut machine) = fixture();
        machine.insts[2].operands[0] = MachOperand::PReg(X2);
        let copy = machine.push_inst(MachInst::new(
            AArch64Opcode::MOVXrr,
            vec![MachOperand::PReg(X0), MachOperand::PReg(X2)],
        ));
        machine.blocks[0].insts.insert(3, copy);
        assert!(source_bound_frame(&source, &machine).is_ok());
        // The opcode fixes the width even when allocation retains W views.
        machine.insts[copy.0 as usize].operands =
            vec![MachOperand::PReg(W0), MachOperand::PReg(W2)];
        assert!(source_bound_frame(&source, &machine).is_ok());
        for mutation in 0..8 {
            let mut wrong = machine.clone();
            match mutation {
                0 => wrong.insts[2].operands[1] = MachOperand::Imm(43),
                1 => wrong.insts[copy.0 as usize].operands[1] = MachOperand::PReg(X3),
                2 => wrong.insts[copy.0 as usize].opcode = AArch64Opcode::MOVWrr,
                3 => wrong.insts[copy.0 as usize].implicit_defs = &[X0],
                4 => wrong.insts[copy.0 as usize].flags = InstFlags::IS_PSEUDO,
                5 => wrong.insts[2].operands[0] = MachOperand::PReg(PReg::new(18)),
                6 => wrong.insts[2].operands[0] = MachOperand::PReg(X19),
                _ => wrong.insts[2].operands[0] = MachOperand::Special(SpecialReg::SP),
            }
            assert!(
                source_bound_frame(&source, &wrong).is_err(),
                "mutation {mutation}"
            );
        }
    }

    #[test]
    fn inert_nops_do_not_define_virtual_values_or_hide_clobbers() {
        use trust_cg_ir::regs::{VReg, W0};
        let (source, mut machine) = fixture();
        machine.next_vreg = 1;
        let dead = machine.push_inst(MachInst::new(
            AArch64Opcode::Nop,
            vec![
                MachOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                MachOperand::PReg(X0),
            ],
        ));
        machine.insts[dead.0 as usize].flags = InstFlags::EMPTY;
        assert!(source_bound_frame(&source, &machine).is_ok());
        machine.blocks[0].insts.insert(3, dead);
        machine.insts[dead.0 as usize].implicit_uses = &[X1];
        assert!(source_bound_frame(&source, &machine).is_ok());
        for mutation in 0..5 {
            let mut wrong = machine.clone();
            let nop = &mut wrong.insts[dead.0 as usize];
            match mutation {
                0 => nop.operands[0] = MachOperand::VReg(VReg::new(1, RegClass::Gpr64)),
                1 => nop.operands[1] = MachOperand::PReg(W0),
                2 => nop.implicit_defs = &[X0],
                3 => nop.implicit_uses = &[X19],
                _ => nop.flags = InstFlags::READS_MEMORY,
            }
            assert!(
                source_bound_frame(&source, &wrong).is_err(),
                "mutation {mutation}"
            );
        }
        let mut narrow = machine.clone();
        narrow.insts[dead.0 as usize].operands[0] =
            MachOperand::VReg(VReg::new(0, RegClass::Gpr32));
        assert!(source_bound_frame(&source, &narrow).is_ok());
        narrow.insts[dead.0 as usize].implicit_defs = &[X0];
        assert!(source_bound_frame(&source, &narrow).is_err());
        let read = machine.push_inst(MachInst::new(
            AArch64Opcode::Copy,
            vec![
                MachOperand::PReg(X0),
                MachOperand::VReg(VReg::new(0, RegClass::Gpr64)),
            ],
        ));
        machine.blocks[0].insts.insert(4, read);
        assert!(source_bound_frame(&source, &machine).is_err());
    }

    #[test]
    fn source_bound_frame_checks_unreferenced_nop_tombstones() {
        let (source, mut machine) = fixture();
        let id = machine.push_inst(MachInst::new(AArch64Opcode::Nop, vec![]));
        assert!(source_bound_frame(&source, &machine).is_ok());
        machine.insts[id.0 as usize].flags = InstFlags::EMPTY;
        assert!(source_bound_frame(&source, &machine).is_ok());
        for mutation in 0..4 {
            let mut wrong = machine.clone();
            let tombstone = &mut wrong.insts[id.0 as usize];
            match mutation {
                0 => tombstone.operands.push(MachOperand::PReg(X0)),
                1 => tombstone.flags = InstFlags::HAS_SIDE_EFFECTS,
                2 => tombstone.implicit_defs = &[X0],
                _ => tombstone.implicit_uses = &[X0],
            }
            assert!(source_bound_frame(&source, &wrong).is_err());
        }
    }

    #[test]
    fn source_bound_frame_query_uses_arbitrary_memory() {
        let (source, machine) = fixture();
        let checked = source_bound_frame(&source, &machine).expect("valid framed leaf");
        assert!(!checked.obligation().is_degenerate());
        let query = crate::ay_bridge::generate_smt2_query_raw(
            checked.obligation(),
            &crate::ay_bridge::AYConfig::default(),
        );
        assert!(query.contains("(declare-fun entry_memory () (Array (_ BitVec 64) (_ BitVec 8)))"));
        assert!(!query.contains("as const"));
        for name in ["entry_fp", "entry_lr", "entry_sp", "observe"] {
            assert!(query.contains(&format!("(declare-const {name} (_ BitVec 64))")));
        }
        println!(
            "SOURCE_BOUND_FRAME_SMT2={}",
            serde_json::to_string(&query).unwrap()
        );
    }

    #[test]
    fn source_bound_frame_verifier_requires_independent_discharge() {
        use crate::function_verifier::{FunctionVerifier, InstructionVerificationResult};
        use crate::lowering_proof::VerificationConfig;
        use crate::provenance_xcheck::ProvenanceXCheckMode;

        crate::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "0")], || {
            let (source, machine) = fixture();
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            let captured = verifier.verify_with_request(&machine, Some(&source), &request);
            assert!(captured.matches_aarch64_input(&machine, Some(&source)));
            for index in [0, 1, 3] {
                assert!(matches!(
                    &captured.report().instructions[index].result,
                    InstructionVerificationResult::Unverified { reason }
                        if reason == "source-bound frame needs independently replayed proof"
                ));
            }
            assert!(!captured.report().emitted_opcode_inventory().is_promotable());
            let mut wrong = machine.clone();
            wrong.insts[2].operands[1] = MachOperand::Imm(43);
            assert!(!captured.matches_aarch64_input(&wrong, Some(&source)));
            let mut wrong_source = source.clone();
            wrong_source.name.push_str("_different");
            assert!(!captured.matches_aarch64_input(&machine, Some(&wrong_source)));
        });
    }

    /// The FRAME theorem's Formal credit must not leak outside the envelope.
    ///
    /// The subject here is the source-bound frame obligation, not the pair
    /// opcodes. In a diagnostic cross-check mode the frame envelope is never
    /// built, for the matching body and for a mismatched one alike, so
    /// instructions 0 and 3 must NOT carry [`FRAME_OBLIGATION_NAME`] or its
    /// `Formal` strength. Under enforced source checking a mismatched body is
    /// rejected by name, as a precondition failure, before any instruction is
    /// credited.
    ///
    /// What 0 and 3 DO carry in the diagnostic modes: they are a
    /// `STP …, [SP,#-16]!` and an `LDP …, [SP],#16` with real operands, so the
    /// operand-bound pair lane (`aarch64_pair_memory_proofs`) checks its
    /// concrete-word obligation (not refuted) and the Formal-only bound-memory
    /// rule (owner ruling 2026-09-29, `bound_memory_authority`) credits each
    /// row through the committed, replayed certificate of its OWN pair form
    /// theorem (`PairMem[stp.pre.gpr.w8]`, `PairMem[ldp.post.gpr.w8]`) —
    /// instruction credit, never the frame theorem. (On a host whose checker
    /// the bound-memory manifest does not qualify, each row is instead a
    /// fail-closed checker-identity miss; never the frame theorem either.)
    #[test]
    fn source_bound_frame_verifier_refuses_unbound_body_and_diagnostic_modes() {
        use crate::function_verifier::{FunctionVerificationPreconditionFailure, FunctionVerifier};
        use crate::lowering_proof::VerificationConfig;
        use crate::provenance_xcheck::ProvenanceXCheckMode;

        let assert_pair_form_credit_without_frame_authority =
            |report: &crate::function_verifier::FunctionVerificationReport, what: &str| {
                for (index, form) in [
                    (0usize, "PairMem[stp.pre.gpr.w8]"),
                    (3, "PairMem[ldp.post.gpr.w8]"),
                ] {
                    let result = &report.instructions[index].result;
                    crate::bound_memory_authority::assert_form_credit_or_checker_miss(
                        result,
                        form,
                        &format!("{what}[{index}]"),
                    );
                    assert!(
                        !format!("{result:?}").contains(FRAME_OBLIGATION_NAME),
                        "{what}[{index}]: frame authority outside the envelope: {result:?}"
                    );
                }
            };

        crate::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "0")], || {
            let (source, machine) = fixture();
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let mut wrong = machine.clone();
            wrong.insts[2].operands[1] = MachOperand::Imm(43);
            for mode in [ProvenanceXCheckMode::Off, ProvenanceXCheckMode::Warn] {
                // Diagnostic modes never credit the envelope, and a wrong body
                // there is a named warning, not a verdict change. The pair
                // opcodes keep only their own operand-bound pair credit.
                for candidate in [&machine, &wrong] {
                    let report =
                        verifier.verify_with_lir_source_and_mode(candidate, Some(&source), mode);
                    assert!(report.precondition_failure.is_none());
                    assert_pair_form_credit_without_frame_authority(&report, "diagnostic mode");
                }
            }
            // Enforced source checking rejects the erroneous supported target
            // by name instead of reporting its envelope as merely uncovered.
            for verifier in [
                verifier,
                FunctionVerifier::with_config(VerificationConfig::default()),
            ] {
                let report = verifier.verify_with_lir_source_and_mode(
                    &wrong,
                    Some(&source),
                    ProvenanceXCheckMode::Enforce,
                );
                assert_eq!(
                    report.precondition_failure,
                    Some(
                        FunctionVerificationPreconditionFailure::SourceBoundFrameMismatch(
                            FrameBindingMismatch::Body(AffineLoweringError::ReturnMismatch)
                        )
                    )
                );
                assert!(report.has_failures() && report.instructions.is_empty());
                let inventory = report.emitted_opcode_inventory();
                assert!(!inventory.is_promotable());
                assert!(
                    inventory
                        .promotion_rejection_reason()
                        .unwrap()
                        .contains("[TCG-SOURCE-BOUND-FRAME-MISMATCH]")
                );
            }
        });
    }

    fn mismatch(source: &Function, machine: &MachFunction) -> FrameBindingMismatch {
        match source_bound_frame(source, machine) {
            Err(SourceBoundFrameRefusal::Mismatch(mismatch)) => mismatch,
            Err(other) => panic!("expected a mismatch, got {other}"),
            Ok(_) => panic!("expected a mismatch, got a binding"),
        }
    }

    fn unsupported_shape(source: &Function, machine: &MachFunction) -> FrameShapeUnsupported {
        match source_bound_frame(source, machine) {
            Err(SourceBoundFrameRefusal::Unsupported(shape)) => shape,
            Err(other) => panic!("expected an unsupported shape, got {other}"),
            Ok(_) => panic!("expected an unsupported shape, got a binding"),
        }
    }

    #[test]
    fn supported_frame_corruptions_are_typed_mismatches() {
        let (source, machine) = fixture();
        assert!(source_bound_frame(&source, &machine).is_ok());

        // Wrong constant: the complete body returns a different value.
        for value in [0, 41, 43, 0xffff] {
            let mut wrong = machine.clone();
            wrong.insts[2].operands[1] = MachOperand::Imm(value);
            assert_eq!(
                mismatch(&source, &wrong),
                FrameBindingMismatch::Body(AffineLoweringError::ReturnMismatch),
                "constant {value}"
            );
        }
        // Wrong register: the value lands in X1 and X0 is returned undefined.
        let mut wrong = machine.clone();
        wrong.insts[2].operands[0] = MachOperand::PReg(X1);
        assert!(matches!(
            mismatch(&source, &wrong),
            FrameBindingMismatch::Body(AffineLoweringError::InvalidMachine(_))
        ));
        // A callee-saved destination is an unsaved clobber, not a new shape.
        wrong.insts[2].operands[0] = MachOperand::PReg(X19);
        assert!(matches!(
            mismatch(&source, &wrong),
            FrameBindingMismatch::Body(AffineLoweringError::InvalidMachine(_))
        ));

        // Altered frame offsets and register order in each envelope position.
        for (index, operand, replacement, role) in [
            (0, 3, MachOperand::Imm(-32), FrameEnvelopeRole::Save),
            (0, 3, MachOperand::Imm(-8), FrameEnvelopeRole::Save),
            (0, 0, MachOperand::PReg(X30), FrameEnvelopeRole::Save),
            (3, 3, MachOperand::Imm(32), FrameEnvelopeRole::Restore),
            (3, 3, MachOperand::Imm(0), FrameEnvelopeRole::Restore),
            (3, 1, MachOperand::PReg(X29), FrameEnvelopeRole::Restore),
            (1, 2, MachOperand::Imm(16), FrameEnvelopeRole::Establish),
        ] {
            let mut wrong = machine.clone();
            wrong.insts[index].operands[operand] = replacement.clone();
            if role == FrameEnvelopeRole::Save && operand == 0 {
                wrong.insts[index].operands[1] = MachOperand::PReg(X29);
            }
            if role == FrameEnvelopeRole::Restore && operand == 1 {
                wrong.insts[index].operands[0] = MachOperand::PReg(X30);
            }
            assert_eq!(
                mismatch(&source, &wrong),
                FrameBindingMismatch::FrameEnvelope {
                    role,
                    instruction: InstId(index as u32),
                },
                "instruction {index} operand {operand} -> {replacement:?}"
            );
        }
        let mut wrong = machine.clone();
        wrong.insts[3].implicit_defs = &[X19];
        assert!(matches!(
            mismatch(&source, &wrong),
            FrameBindingMismatch::FrameEnvelope {
                role: FrameEnvelopeRole::Restore,
                ..
            }
        ));
    }

    #[test]
    fn supported_chain_branch_corruptions_are_typed_mismatches() {
        let (source, machine, branch) = linear_fixture();
        assert!(source_bound_frame(&source, &machine).is_ok());
        let entry = machine.entry;
        for (operand, defect) in [
            (
                MachOperand::Imm(2),
                BranchTargetDefect::NoBlockStart { displacement: 2 },
            ),
            (
                MachOperand::Imm(0),
                BranchTargetDefect::NoBlockStart { displacement: 0 },
            ),
            (
                MachOperand::Imm(-3),
                BranchTargetDefect::DisagreesWithSuccessor {
                    target: entry,
                    recorded: trust_cg_ir::BlockId(1),
                },
            ),
            (
                MachOperand::Imm(1 << 25),
                BranchTargetDefect::DisplacementOutOfRange {
                    displacement: 1 << 25,
                    bits: 26,
                },
            ),
            (
                MachOperand::Block(entry),
                BranchTargetDefect::DisagreesWithSuccessor {
                    target: entry,
                    recorded: trust_cg_ir::BlockId(1),
                },
            ),
        ] {
            let mut wrong = machine.clone();
            wrong.insts[branch.0 as usize].operands[0] = operand.clone();
            assert_eq!(
                mismatch(&source, &wrong),
                FrameBindingMismatch::BranchTarget {
                    block: entry,
                    instruction: Some(branch),
                    defect,
                },
                "branch operand {operand:?}"
            );
        }
        // A symbolic branch to a block outside the layout cannot execute.
        let mut wrong = machine.clone();
        let orphan = wrong.create_block();
        wrong.block_order.retain(|block| *block != orphan);
        wrong.insts[branch.0 as usize].operands[0] = MachOperand::Block(orphan);
        assert!(matches!(
            mismatch(&source, &wrong),
            FrameBindingMismatch::BranchTarget {
                defect: BranchTargetDefect::TargetNotLaidOut { .. },
                ..
            }
        ));
        // Metadata-only and tail-call shapes remain unsupported, not mismatches.
        let mut metadata = machine.clone();
        metadata.blocks[0].succs.clear();
        assert_eq!(
            unsupported_shape(&source, &metadata),
            FrameShapeUnsupported::MachineControl
        );
        let mut tail = machine.clone();
        tail.insts[branch.0 as usize].operands[0] = MachOperand::Symbol("outside".into());
        assert_eq!(
            unsupported_shape(&source, &tail),
            FrameShapeUnsupported::MachineControl
        );
    }

    #[test]
    fn unsupported_shapes_stay_unsupported_and_uncredited() {
        use crate::function_verifier::FunctionVerifier;
        use crate::lowering_proof::VerificationConfig;
        use crate::provenance_xcheck::ProvenanceXCheckMode;

        let (source, machine) = fixture();
        // Frameless leaf: legitimately compiled, outside the envelope domain.
        let mut frameless = machine.clone();
        frameless.blocks[0].insts = vec![InstId(2), InstId(4)];
        frameless.insts.truncate(5);
        frameless.insts[0] = MachInst::new(AArch64Opcode::Nop, vec![]);
        frameless.insts[1] = MachInst::new(AArch64Opcode::Nop, vec![]);
        frameless.insts[3] = MachInst::new(AArch64Opcode::Nop, vec![]);
        assert_eq!(
            unsupported_shape(&source, &frameless),
            FrameShapeUnsupported::Envelope(EnvelopeShape::TooShort)
        );
        // A callee-saved pair allocates the frame first: another lowering.
        let mut callee_saved = machine.clone();
        callee_saved.insts[0].operands[0] = MachOperand::PReg(X19);
        callee_saved.insts[0].operands[1] = MachOperand::PReg(trust_cg_ir::regs::X20);
        assert_eq!(
            unsupported_shape(&source, &callee_saved),
            FrameShapeUnsupported::Envelope(EnvelopeShape::NoFrameSave)
        );
        // Frame pointer omitted.
        let mut no_fp = machine.clone();
        no_fp.insts[1] = MachInst::new(
            AArch64Opcode::Movz,
            vec![
                MachOperand::PReg(X1),
                MachOperand::Imm(1),
                MachOperand::Imm(0),
            ],
        );
        assert_eq!(
            unsupported_shape(&source, &no_fp),
            FrameShapeUnsupported::Envelope(EnvelopeShape::NoFramePointer)
        );
        // A local area or spill names SP.
        let mut local_area = machine.clone();
        let adjust = local_area.push_inst(MachInst::new(
            AArch64Opcode::SubRI,
            vec![
                MachOperand::Special(SpecialReg::SP),
                MachOperand::Special(SpecialReg::SP),
                MachOperand::Imm(16),
            ],
        ));
        local_area.blocks[0].insts.insert(2, adjust);
        assert_eq!(
            unsupported_shape(&source, &local_area),
            FrameShapeUnsupported::Envelope(EnvelopeShape::StackPointerBody)
        );
        // An opcode outside the modeled body domain.
        let mut opcode = machine.clone();
        opcode.insts[2] = MachInst::new(
            AArch64Opcode::MulRR,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
            ],
        );
        assert!(matches!(
            unsupported_shape(&source, &opcode),
            FrameShapeUnsupported::Body(AffineLoweringError::UnsupportedMachine(_))
        ));
        // Source outside the chain/diamond or affine domain is never judged,
        // even when its machine code is also wrong.
        let mut wrong = machine.clone();
        wrong.insts[2].operands[1] = MachOperand::Imm(43);
        let mut trapping = source.clone();
        trapping
            .blocks
            .get_mut(&trapping.entry_block)
            .unwrap()
            .instructions[1]
            .opcode = trust_cg_lower::instructions::Opcode::Trap;
        assert!(matches!(
            unsupported_shape(&trapping, &wrong),
            FrameShapeUnsupported::SourceDomain(AffineLoweringError::UnsupportedSource(_))
        ));
        let (mut looping, chain_machine, branch) = linear_fixture();
        let entry = looping.entry_block;
        looping
            .blocks
            .get_mut(&entry)
            .unwrap()
            .instructions
            .last_mut()
            .unwrap()
            .opcode = trust_cg_lower::instructions::Opcode::Jump { dest: entry };
        let mut wrong_chain = chain_machine.clone();
        wrong_chain.insts[branch.0 as usize].operands[0] = MachOperand::Imm(2);
        assert_eq!(
            unsupported_shape(&looping, &wrong_chain),
            FrameShapeUnsupported::SourceShape
        );

        // The verifier keeps the unchanged uncovered-envelope path for these.
        crate::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "0")], || {
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let report = verifier.verify_with_lir_source_and_mode(
                &callee_saved,
                Some(&source),
                ProvenanceXCheckMode::Enforce,
            );
            assert!(report.precondition_failure.is_none());
            // Row 0 (the prologue STP) is never frame-credited. It is
            // credited only as an INSTRUCTION, by the replayed certificate of
            // its own pair form theorem (the Formal-only bound-memory rule,
            // owner ruling 2026-09-29); the unsupported envelope still keeps
            // the function from promoting.
            let result = &report.instructions[0].result;
            crate::bound_memory_authority::assert_form_credit_or_checker_miss(
                result,
                "PairMem[stp.",
                "prologue STP",
            );
            assert!(
                !format!("{result:?}").contains(FRAME_OBLIGATION_NAME),
                "{result:?}"
            );
            assert!(!report.emitted_opcode_inventory().is_promotable());
        });
    }
}
