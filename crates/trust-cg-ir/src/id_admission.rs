// trust-cg-ir - Machine-IR identity counter admission
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Identity-counter admission for [`MachFunction`] (ledger L10-P5).
//!
//! Every fresh machine-IR identity comes from a counter: `next_vreg` for
//! virtual registers and the arena length for instructions, blocks, stack
//! slots and jump tables. The legacy allocators (`alloc_vreg`, `push_inst`,
//! `create_block`, `alloc_stack_slot`) issue the counter's current value
//! without looking at the body, so an ID they issue is fresh only while every
//! identity the function already references lies below its counter. Public
//! IR fields let any caller break that: an operand naming `v7` while
//! `next_vreg == 5`, a block listing `inst9` in an eight-entry arena, or a
//! sidecar keyed by an instruction that does not exist yet would each be
//! aliased by the next allocation.
//!
//! [`MachFunction::admit_id_counters`] re-derives every referenced identity
//! from the function and refuses, by name, a function in which some live ID
//! is not below the counter that issues its domain's next ID, or whose arena
//! has outgrown the `u32` ID space.
//!
//! Where it runs. Eagerly at the pipeline boundaries that hand a function
//! between owners: the instruction-selection exit, the optimizer pass
//! manager's entry and exit, and each codegen phase boundary
//! ([`MachFunction::admit_id_counters_at`]). Inside the pass manager it runs
//! at the moment it is needed: each pass entry marks the function
//! ([`MachFunction::require_id_admission_before_allocation`]) and the pass's
//! first allocation of any kind, legacy or checked, re-derives every live
//! identity before issuing an ID. A pass that allocates nothing issues no ID
//! and needs no scan, so the scan is paid once per allocating pass rather
//! than at every boundary. A refusal there is sticky: the legacy allocators
//! keep their infallible signatures, the checked ones return `None`, and the
//! pass manager refuses the function by name at that pass's exit (and every
//! later admission reports the same refusal), so it is never emitted.
//!
//! Together with the allocators' saturating exhaustion (an exhausted counter
//! issues the sentinel `u32::MAX`, which no counter can exceed, instead of
//! wrapping), no allocator issues an ID inside a pass from a counter that was
//! not re-derived after the pass began, so a fresh ID cannot alias an ID that
//! was live before the pass's first allocation; the next eager re-derivation
//! refuses any ID a pass wrote at or above the counter without allocating it,
//! unless something raised the counter past it.
//!
//! A pass that must number new IDs before it can mutate the function (SROA
//! plans its shadow registers while the function is borrowed for analysis)
//! allocates exactly the planned range through
//! [`MachFunction::try_alloc_vreg_range`] before any operand names one. Code
//! that allocates on a private copy published only on success admits the
//! function itself first ([`MachFunction::admit_ids_before_allocation`]), so
//! the refusal stays where the pipeline reports it rather than on a discarded
//! copy, and a later counter synchronization on the copy cannot repair it.
//!
//! What this does not cover: a pass that writes an ID it did not allocate
//! after its first allocation, where a later allocation in the same pass then
//! issues it, is not distinguishable from one that reuses an existing value on
//! purpose, and a pass that numbers IDs by hand and then raises the counter
//! past them itself satisfies every later re-derivation; the allocator-only
//! discipline for new IDs is a code property. A provenance map passed beside
//! the function (which may hold other functions' instruction IDs) is not
//! admitted. The x86-64 selector's `X86ISelFunction` is a different type and
//! is not admitted.

use crate::function::{DebugVariableStorage, EhCallSiteBindings, MachFunction};
use crate::operand::MachOperand;

/// The largest arena length whose every index is a `u32` ID.
const MAX_ARENA_LEN: u64 = u32::MAX as u64 + 1;

/// An identity domain whose fresh IDs come from a [`MachFunction`] counter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MachIdDomain {
    /// Virtual registers; `next_vreg` issues the next ID.
    VReg,
    /// The instruction arena; its length issues the next `InstId`.
    Inst,
    /// The block arena; its length issues the next `BlockId`.
    Block,
    /// The stack-slot arena; its length issues the next `StackSlotId`.
    StackSlot,
    /// The jump-table list; its length is the next `JumpTableIndex`.
    JumpTable,
}

impl MachIdDomain {
    /// Stable lowercase name used in diagnostics.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::VReg => "vreg",
            Self::Inst => "instruction",
            Self::Block => "block",
            Self::StackSlot => "stack-slot",
            Self::JumpTable => "jump-table",
        }
    }
}

impl core::fmt::Display for MachIdDomain {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Where the admission found a live identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MachIdSite {
    /// Operand `operand` of arena instruction `inst` (linked or detached).
    Operand { inst: u32, operand: usize },
    /// Entry `index` of `MachFunction::noalias_params`.
    NoaliasParam { index: usize },
    /// The instruction list of block `block`.
    BlockInsts { block: u32 },
    /// A predecessor or successor edge of block `block`.
    BlockEdge { block: u32 },
    /// `MachFunction::block_order`.
    BlockOrder,
    /// `MachFunction::entry`.
    Entry,
    /// A target of jump table `table`.
    JumpTableTarget { table: usize },
    /// A local table-address expansion's anchor, add or table identity.
    JumpTableAddress,
    /// Landing-pad entry `index` of the exception-handling metadata.
    LandingPad { index: usize },
    /// Call-site entry `index` of the exception-handling metadata.
    EhCallSite { index: usize },
    /// Exact selected-invoke binding `index` of the EH metadata.
    EhInvokeBinding { index: usize },
    /// `MachFunction::stack_limit_overflow_block`.
    StackLimitOverflowBlock,
    /// A key of `MachFunction::lowering_provenance`.
    LoweringProvenance,
    /// A key of `MachFunction::call_abi_facts`.
    CallAbiFacts,
    /// `MachFunction::stack_protector_slot`.
    StackProtectorSlot,
    /// Debug local variable `index` of `MachFunction::debug_meta`.
    DebugLocal { index: usize },
    /// Trap-expansion record `index`: an instruction it lists, or an operand
    /// of its saved carrier.
    TrapExpansion { index: usize },
}

impl core::fmt::Display for MachIdSite {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Self::Operand { inst, operand } => write!(f, "operand {operand} of inst{inst}"),
            Self::NoaliasParam { index } => write!(f, "noalias parameter entry {index}"),
            Self::BlockInsts { block } => write!(f, "the instruction list of bb{block}"),
            Self::BlockEdge { block } => write!(f, "a CFG edge of bb{block}"),
            Self::BlockOrder => f.write_str("the block layout order"),
            Self::Entry => f.write_str("the entry block"),
            Self::JumpTableTarget { table } => write!(f, "a target of jump table {table}"),
            Self::JumpTableAddress => f.write_str("a jump-table address expansion"),
            Self::LandingPad { index } => write!(f, "landing pad entry {index}"),
            Self::EhCallSite { index } => write!(f, "EH call-site entry {index}"),
            Self::EhInvokeBinding { index } => write!(f, "EH invoke binding {index}"),
            Self::StackLimitOverflowBlock => f.write_str("the stack-limit overflow block"),
            Self::LoweringProvenance => f.write_str("the lowering-provenance sidecar"),
            Self::CallAbiFacts => f.write_str("the call-ABI facts sidecar"),
            Self::StackProtectorSlot => f.write_str("the stack-protector slot"),
            Self::DebugLocal { index } => write!(f, "debug local variable {index}"),
            Self::TrapExpansion { index } => write!(f, "trap-expansion record {index}"),
        }
    }
}

/// Why [`MachFunction::admit_id_counters`] refused a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MachIdAdmissionError {
    /// A live ID is not below the counter that issues the domain's next ID,
    /// so the next allocation in that domain could alias it
    /// (`[TCG-MIR-STALE-ID-COUNTER]`).
    StaleCounter {
        /// The identity domain.
        domain: MachIdDomain,
        /// The ID the domain's allocator would issue next.
        counter: u64,
        /// The live ID at or above the counter.
        live_id: u32,
        /// Where the live ID was found.
        site: MachIdSite,
    },
    /// The domain cannot issue another distinct ID: an arena has more entries
    /// than `u32` IDs can name, or the function references the exhausted-
    /// counter sentinel `u32::MAX` as a virtual register
    /// (`[TCG-MIR-ID-EXHAUSTED]`).
    Exhausted {
        /// The identity domain.
        domain: MachIdDomain,
        /// The arena length, or `u32::MAX` for the virtual-register sentinel.
        extent: u64,
        /// Where the sentinel was found (`None` for an arena length).
        site: Option<MachIdSite>,
    },
}

impl MachIdAdmissionError {
    /// The stable diagnostic code of this refusal.
    pub fn code(&self) -> &'static str {
        match self {
            Self::StaleCounter { .. } => "TCG-MIR-STALE-ID-COUNTER",
            Self::Exhausted { .. } => "TCG-MIR-ID-EXHAUSTED",
        }
    }

    /// The identity domain this refusal names.
    pub fn domain(&self) -> MachIdDomain {
        match *self {
            Self::StaleCounter { domain, .. } | Self::Exhausted { domain, .. } => domain,
        }
    }
}

impl core::fmt::Display for MachIdAdmissionError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Self::StaleCounter {
                domain,
                counter,
                live_id,
                site,
            } => write!(
                f,
                "[{}] {domain} counter {counter} does not exceed live {domain} id {live_id} \
                 (at {site}); a fresh {domain} id would alias it",
                self.code()
            ),
            Self::Exhausted {
                domain,
                extent,
                site: Some(site),
            } => write!(
                f,
                "[{}] {domain} id {extent} is the exhausted-counter sentinel (at {site})",
                self.code()
            ),
            Self::Exhausted {
                domain,
                extent,
                site: None,
            } => write!(
                f,
                "[{}] the {domain} arena holds {extent} entries, more than u32 ids can name",
                self.code()
            ),
        }
    }
}

impl std::error::Error for MachIdAdmissionError {}

/// A refused admission at a named pipeline boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MachIdRefusal {
    /// The function's name.
    pub function: String,
    /// The pipeline boundary that ran the admission, e.g. "exit of pass `licm`".
    pub boundary: String,
    /// What the admission found.
    pub error: MachIdAdmissionError,
}

impl core::fmt::Display for MachIdRefusal {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "function `{}` refused at {}: {}",
            self.function, self.boundary, self.error
        )
    }
}

impl std::error::Error for MachIdRefusal {}

/// Allocation-time admission state of one function.
#[derive(Clone, Copy, PartialEq, Eq)]
enum IdAdmissionState {
    /// The counters were re-derived (or the function was built by its
    /// allocators alone) since the last boundary: allocate freely.
    Admitted,
    /// A boundary passed: the next allocation re-derives first.
    Pending,
    /// A re-derivation refused; sticky until the function is dropped.
    Refused(MachIdAdmissionError),
}

/// The allocation-time admission state a [`MachFunction`] carries. Opaque in
/// `Debug` (a constant spelling), so a function's `Debug` text, which tests
/// and diagnostics compare, still describes only its IR.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct IdAdmissionCell(IdAdmissionState);

impl IdAdmissionCell {
    /// A function built from nothing by its own allocators.
    pub(crate) const ADMITTED: Self = Self(IdAdmissionState::Admitted);
}

impl core::fmt::Debug for IdAdmissionCell {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("IdAdmissionCell")
    }
}

fn stale(
    domain: MachIdDomain,
    counter: u64,
    live_id: u32,
    site: MachIdSite,
) -> MachIdAdmissionError {
    if domain == MachIdDomain::VReg && live_id == u32::MAX {
        return MachIdAdmissionError::Exhausted {
            domain,
            extent: u64::from(u32::MAX),
            site: Some(site),
        };
    }
    MachIdAdmissionError::StaleCounter {
        domain,
        counter,
        live_id,
        site,
    }
}

/// Counters of one function, read once per admission.
#[derive(Clone, Copy)]
struct Limits {
    vreg: u32,
    insts: u64,
    blocks: u64,
    slots: u64,
    tables: u64,
}

impl Limits {
    fn of(func: &MachFunction) -> Self {
        Self {
            vreg: func.next_vreg,
            insts: func.insts.len() as u64,
            blocks: func.blocks.len() as u64,
            slots: func.stack_slots.len() as u64,
            tables: func.jump_tables.len() as u64,
        }
    }

    /// Whether `operand` names no identity at or above its counter: the
    /// branch-light predicate of the accepting scan.
    #[inline(always)]
    fn operand_in_range(self, operand: &MachOperand) -> bool {
        match *operand {
            MachOperand::VReg(reg) => reg.id < self.vreg,
            MachOperand::Block(block) => u64::from(block.0) < self.blocks,
            MachOperand::StackSlot(slot) => u64::from(slot.0) < self.slots,
            MachOperand::FrameIndex(index) => index.0 < 0 || (index.0 as u64) < self.slots,
            MachOperand::JumpTableIndex(table) => u64::from(table) < self.tables,
            _ => true,
        }
    }

    /// The operand's identity at or above its counter, if any.
    #[inline]
    fn check_operand(
        self,
        operand: &MachOperand,
        site: MachIdSite,
    ) -> Result<(), MachIdAdmissionError> {
        match operand {
            MachOperand::VReg(reg) if reg.id >= self.vreg => Err(stale(
                MachIdDomain::VReg,
                u64::from(self.vreg),
                reg.id,
                site,
            )),
            MachOperand::Block(block) if u64::from(block.0) >= self.blocks => {
                Err(stale(MachIdDomain::Block, self.blocks, block.0, site))
            }
            MachOperand::StackSlot(slot) if u64::from(slot.0) >= self.slots => {
                Err(stale(MachIdDomain::StackSlot, self.slots, slot.0, site))
            }
            // A non-negative frame index names a stack slot (frame-index
            // elimination resolves it through the same arena); a negative one
            // is an offset no fresh slot can alias.
            MachOperand::FrameIndex(index) if index.0 >= 0 && index.0 as u64 >= self.slots => Err(
                stale(MachIdDomain::StackSlot, self.slots, index.0 as u32, site),
            ),
            MachOperand::JumpTableIndex(table) if u64::from(*table) >= self.tables => {
                Err(stale(MachIdDomain::JumpTable, self.tables, *table, site))
            }
            _ => Ok(()),
        }
    }
}

fn check_block(limits: Limits, block: u32, site: MachIdSite) -> Result<(), MachIdAdmissionError> {
    if u64::from(block) >= limits.blocks {
        return Err(stale(MachIdDomain::Block, limits.blocks, block, site));
    }
    Ok(())
}

fn check_slot(limits: Limits, slot: u32, site: MachIdSite) -> Result<(), MachIdAdmissionError> {
    if u64::from(slot) >= limits.slots {
        return Err(stale(MachIdDomain::StackSlot, limits.slots, slot, site));
    }
    Ok(())
}

fn check_inst(limits: Limits, inst: u32, site: MachIdSite) -> Result<(), MachIdAdmissionError> {
    if u64::from(inst) >= limits.insts {
        return Err(stale(MachIdDomain::Inst, limits.insts, inst, site));
    }
    Ok(())
}

impl MachFunction {
    /// Refuse this function if a fresh ID from any of its allocators could
    /// alias an identity it already references (see the
    /// [module documentation](crate::id_admission)), or report the sticky
    /// refusal of an earlier allocation-time admission.
    ///
    /// Checks every register, block, stack-slot and jump-table operand of
    /// every arena instruction (detached ones included), the noalias
    /// parameter identities, every block's instruction list and CFG edges,
    /// the layout order and entry, jump-table targets, exception-handling
    /// blocks, the stack-limit overflow block, the instruction-keyed
    /// sidecars, the trap-expansion records (their instructions and saved
    /// carriers), the stack-protector slot and debug stack slots. One linear
    /// scan; it reads and never repairs.
    pub fn admit_id_counters(&self) -> Result<(), MachIdAdmissionError> {
        if let IdAdmissionState::Refused(error) = self.id_admission.0 {
            return Err(error);
        }
        self.scan_id_counters()
    }

    fn scan_id_counters(&self) -> Result<(), MachIdAdmissionError> {
        for (domain, extent) in [
            (MachIdDomain::Inst, self.insts.len()),
            (MachIdDomain::Block, self.blocks.len()),
            (MachIdDomain::StackSlot, self.stack_slots.len()),
            (MachIdDomain::JumpTable, self.jump_tables.len()),
        ] {
            if extent as u64 > MAX_ARENA_LEN {
                return Err(MachIdAdmissionError::Exhausted {
                    domain,
                    extent: extent as u64,
                    site: None,
                });
            }
        }
        let limits = Limits::of(self);

        // This runs at every optimizer pass boundary, so the accepting path is
        // one tight predicate scan; only a refusal walks again to name a site.
        let operands_in_range = self.insts.iter().all(|inst| {
            inst.operands
                .iter()
                .all(|operand| limits.operand_in_range(operand))
        });
        if !operands_in_range {
            for (inst_index, inst) in self.insts.iter().enumerate() {
                for (operand_index, operand) in inst.operands.iter().enumerate() {
                    let site = MachIdSite::Operand {
                        inst: inst_index as u32,
                        operand: operand_index,
                    };
                    limits.check_operand(operand, site)?;
                }
            }
        }
        for (index, &reg) in self.noalias_params.iter().enumerate() {
            if reg >= limits.vreg {
                return Err(stale(
                    MachIdDomain::VReg,
                    u64::from(limits.vreg),
                    reg,
                    MachIdSite::NoaliasParam { index },
                ));
            }
        }

        let blocks_in_range = self.blocks.iter().all(|block| {
            block
                .insts
                .iter()
                .all(|inst| u64::from(inst.0) < limits.insts)
                && block
                    .preds
                    .iter()
                    .chain(block.succs.iter())
                    .all(|edge| u64::from(edge.0) < limits.blocks)
        });
        for (block_index, block) in self.blocks.iter().enumerate().filter(|_| !blocks_in_range) {
            let block_index = block_index as u32;
            for &inst in &block.insts {
                check_inst(
                    limits,
                    inst.0,
                    MachIdSite::BlockInsts { block: block_index },
                )?;
            }
            for &edge in block.preds.iter().chain(block.succs.iter()) {
                check_block(limits, edge.0, MachIdSite::BlockEdge { block: block_index })?;
            }
        }
        for &block in &self.block_order {
            check_block(limits, block.0, MachIdSite::BlockOrder)?;
        }
        check_block(limits, self.entry.0, MachIdSite::Entry)?;
        for (table, data) in self.jump_tables.iter().enumerate() {
            for &target in &data.targets {
                check_block(limits, target.0, MachIdSite::JumpTableTarget { table })?;
            }
        }
        for (&anchor, expansion) in &self.jump_table_address_expansions {
            let site = MachIdSite::JumpTableAddress;
            check_inst(limits, anchor.0, site)?;
            check_inst(limits, expansion.add.0, site)?;
            if u64::from(expansion.table) >= limits.tables {
                return Err(stale(
                    MachIdDomain::JumpTable,
                    limits.tables,
                    expansion.table,
                    site,
                ));
            }
        }
        for (index, pad) in self.eh_metadata.landing_pads.iter().enumerate() {
            check_block(limits, pad.block.0, MachIdSite::LandingPad { index })?;
        }
        for (index, site) in self.eh_metadata.call_sites.iter().enumerate() {
            check_block(limits, site.call_block.0, MachIdSite::EhCallSite { index })?;
            if let Some(pad) = site.landing_pad_block {
                check_block(limits, pad.0, MachIdSite::EhCallSite { index })?;
            }
        }
        if let EhCallSiteBindings::ExactInstructions(bindings) =
            &self.eh_metadata.call_site_bindings
        {
            for (index, binding) in bindings.iter().enumerate() {
                let site = MachIdSite::EhInvokeBinding { index };
                check_inst(limits, binding.call_inst.0, site)?;
                check_block(limits, binding.call_block.0, site)?;
                check_block(limits, binding.landing_pad_block.0, site)?;
            }
        }
        if let Some(block) = self.stack_limit_overflow_block {
            check_block(limits, block.0, MachIdSite::StackLimitOverflowBlock)?;
        }

        for (index, record) in self.trap_expansions.iter().enumerate() {
            let site = MachIdSite::TrapExpansion { index };
            for &inst in &record.insts {
                check_inst(limits, inst.0, site)?;
            }
            // The saved carrier is not in the arena, so its operands carry the
            // record's site rather than an instruction index.
            for operand in &record.carrier.operands {
                limits.check_operand(operand, site)?;
            }
        }

        // Both sidecars are ordered maps: the last key is the largest.
        if let Some((&inst, _)) = self.lowering_provenance.last_key_value() {
            check_inst(limits, inst.0, MachIdSite::LoweringProvenance)?;
        }
        if let Some((&inst, _)) = self.call_abi_facts.last_key_value() {
            check_inst(limits, inst.0, MachIdSite::CallAbiFacts)?;
        }

        if let Some(slot) = self.stack_protector_slot {
            check_slot(limits, slot.0, MachIdSite::StackProtectorSlot)?;
        }
        for (index, local) in self.debug_meta.local_variables.iter().enumerate() {
            if let DebugVariableStorage::StackSlot(slot) = local.storage {
                check_slot(limits, slot, MachIdSite::DebugLocal { index })?;
            }
        }
        Ok(())
    }

    /// [`Self::admit_id_counters`] at a named pipeline boundary. An admitted
    /// function may allocate until the next boundary without another scan; a
    /// refused one keeps the refusal.
    ///
    /// `boundary` is built only on refusal, so the accepting path allocates
    /// nothing.
    pub fn admit_id_counters_at(
        &mut self,
        boundary: impl FnOnce() -> String,
    ) -> Result<(), MachIdRefusal> {
        let verdict = self.admit_id_counters();
        self.id_admission.0 = match verdict {
            Ok(()) => IdAdmissionState::Admitted,
            Err(error) => IdAdmissionState::Refused(error),
        };
        verdict.map_err(|error| MachIdRefusal {
            function: self.name.clone(),
            boundary: boundary(),
            error,
        })
    }

    /// Mark a pipeline boundary: the next allocation of any kind first
    /// re-derives every live identity. Callers that hand the function to code
    /// that may have changed it (each optimizer pass entry) call this; a
    /// sticky refusal stays.
    pub fn require_id_admission_before_allocation(&mut self) {
        if !matches!(self.id_admission.0, IdAdmissionState::Refused(_)) {
            self.id_admission.0 = IdAdmissionState::Pending;
        }
    }

    /// Run the allocation-time admission now, without allocating: re-derive
    /// every live identity if a boundary is pending (at most once, as an
    /// allocator would), and report the sticky refusal. For code that is
    /// about to allocate on a private copy of this function (a candidate
    /// rewrite published only on success): admitting the function itself
    /// first keeps a refusal on it, where the pipeline reports it, instead of
    /// on a copy that is then discarded.
    pub fn admit_ids_before_allocation(&mut self) -> Result<(), MachIdAdmissionError> {
        self.admit_before_allocation();
        match self.id_admission.0 {
            IdAdmissionState::Refused(error) => Err(error),
            IdAdmissionState::Admitted | IdAdmissionState::Pending => Ok(()),
        }
    }

    /// The sticky refusal of an allocation-time admission, if one refused.
    pub fn id_admission_refusal(&self) -> Option<MachIdAdmissionError> {
        match self.id_admission.0 {
            IdAdmissionState::Refused(error) => Some(error),
            IdAdmissionState::Admitted | IdAdmissionState::Pending => None,
        }
    }

    /// Run by every allocator before it issues an ID: re-derive after a
    /// boundary, at most once. `false` when the function is refused (the
    /// checked allocators then return `None`; the legacy ones proceed and the
    /// sticky refusal fails the function at the pass's exit).
    #[inline]
    pub(crate) fn admit_before_allocation(&mut self) -> bool {
        match self.id_admission.0 {
            IdAdmissionState::Admitted => true,
            IdAdmissionState::Refused(_) => false,
            IdAdmissionState::Pending => self.admit_pending_allocation(),
        }
    }

    #[cold]
    #[inline(never)]
    fn admit_pending_allocation(&mut self) -> bool {
        match self.scan_id_counters() {
            Ok(()) => {
                self.id_admission.0 = IdAdmissionState::Admitted;
                true
            }
            Err(error) => {
                self.id_admission.0 = IdAdmissionState::Refused(error);
                false
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function::{
        CallAbiFacts, CalleeSavedSet, DebugBaseType, DebugLocalVariable, EhCallSiteEntry,
        JumpTableData, LandingPadEntry, Signature, StackSlot,
    };
    use crate::inst::{AArch64Opcode, MachInst};
    use crate::provenance::LoweringProvenance;
    use crate::regs::{RegClass, VReg};
    use crate::types::{BlockId, FrameIdx, InstId, StackSlotId};

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    /// `bb0: v0 = mov #1; v1 = add v0, #2; b bb1` / `bb1: ret`, counters synced.
    fn well_formed() -> MachFunction {
        let mut func = MachFunction::new("f".into(), Signature::new(vec![], vec![]));
        let bb1 = func.create_block();
        let v0 = func.alloc_vreg();
        let v1 = func.alloc_vreg();
        let mov = func.push_inst(MachInst::new(
            AArch64Opcode::MovI,
            vec![vreg(v0), MachOperand::Imm(1)],
        ));
        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(v1), vreg(v0), MachOperand::Imm(2)],
        ));
        let br = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        for id in [mov, add, br] {
            func.append_inst(BlockId(0), id);
        }
        func.append_inst(bb1, ret);
        func.add_edge(BlockId(0), bb1);
        let slot = func.alloc_stack_slot(StackSlot::new(8, 8));
        func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(v1), MachOperand::StackSlot(slot)],
        ));
        func
    }

    fn refusal(func: &MachFunction) -> MachIdAdmissionError {
        func.admit_id_counters()
            .expect_err("a stale or exhausted counter must be refused")
    }

    #[test]
    fn allocator_built_function_is_admitted() {
        assert_eq!(well_formed().admit_id_counters(), Ok(()));
        let empty = MachFunction::new("e".into(), Signature::new(vec![], vec![]));
        assert_eq!(empty.admit_id_counters(), Ok(()));
    }

    #[test]
    fn stale_vreg_counter_is_refused_with_its_site() {
        let mut func = well_formed();
        func.next_vreg = 1; // v1 is live
        let error = refusal(&func);
        assert_eq!(
            error,
            MachIdAdmissionError::StaleCounter {
                domain: MachIdDomain::VReg,
                counter: 1,
                live_id: 1,
                site: MachIdSite::Operand {
                    inst: 1,
                    operand: 0
                },
            }
        );
        let text = error.to_string();
        assert!(
            text.starts_with("[TCG-MIR-STALE-ID-COUNTER] vreg counter 1"),
            "{text}"
        );
        // The counter the legacy allocator would use next is exactly the
        // aliasing ID the admission names.
        assert_eq!(func.clone().alloc_vreg(), 1);
    }

    #[test]
    fn detached_instructions_and_noalias_ids_count_as_live() {
        let mut func = well_formed();
        func.insts
            .push(MachInst::new(AArch64Opcode::MovI, vec![vreg(40)]));
        assert_eq!(refusal(&func).domain(), MachIdDomain::VReg);
        func.next_vreg = 41;
        assert_eq!(func.admit_id_counters(), Ok(()));
        func.noalias_params.push(41);
        assert!(matches!(
            refusal(&func),
            MachIdAdmissionError::StaleCounter {
                site: MachIdSite::NoaliasParam { index: 0 },
                live_id: 41,
                ..
            }
        ));
    }

    #[test]
    fn instruction_references_past_the_arena_are_refused() {
        let len = well_formed().insts.len() as u32;
        let mut listed = well_formed();
        listed.blocks[1].insts.push(InstId(len));
        assert!(matches!(
            refusal(&listed),
            MachIdAdmissionError::StaleCounter {
                domain: MachIdDomain::Inst,
                live_id,
                site: MachIdSite::BlockInsts { block: 1 },
                ..
            } if live_id == len
        ));

        let mut provenance = well_formed();
        provenance
            .lowering_provenance
            .insert(InstId(len + 3), LoweringProvenance::UNATTRIBUTED);
        assert_eq!(
            refusal(&provenance),
            MachIdAdmissionError::StaleCounter {
                domain: MachIdDomain::Inst,
                counter: u64::from(len),
                live_id: len + 3,
                site: MachIdSite::LoweringProvenance,
            }
        );

        let mut facts = well_formed();
        facts.call_abi_facts.insert(
            InstId(len),
            CallAbiFacts {
                callee: Some("g".into()),
                stack_arg_bytes: 0,
                stack_stores: Vec::new(),
                aggregate_stack_args: false,
                hidden_result_pointer: false,
                by_reference_argument_copies: false,
                variadic: false,
                callee_saved: CalleeSavedSet::Aapcs64,
            },
        );
        assert!(matches!(
            refusal(&facts),
            MachIdAdmissionError::StaleCounter {
                site: MachIdSite::CallAbiFacts,
                ..
            }
        ));
        // A fresh push would have been given exactly that sidecar's key.
        assert_eq!(
            facts.push_inst(MachInst::new(AArch64Opcode::Nop, vec![])),
            InstId(len)
        );
    }

    #[test]
    fn every_block_reference_is_checked() {
        let blocks = well_formed().blocks.len() as u32;
        let dangling = BlockId(blocks);
        type Corrupt = Box<dyn Fn(&mut MachFunction)>;
        let cases: Vec<(MachIdSite, Corrupt)> = vec![
            (
                MachIdSite::Operand {
                    inst: 2,
                    operand: 0,
                },
                Box::new(move |f| f.insts[2].operands[0] = MachOperand::Block(dangling)),
            ),
            (
                MachIdSite::BlockEdge { block: 0 },
                Box::new(move |f| f.blocks[0].succs.push(dangling)),
            ),
            (
                MachIdSite::BlockEdge { block: 1 },
                Box::new(move |f| f.blocks[1].preds.push(dangling)),
            ),
            (
                MachIdSite::BlockOrder,
                Box::new(move |f| f.block_order.push(dangling)),
            ),
            (MachIdSite::Entry, Box::new(move |f| f.entry = dangling)),
            (
                MachIdSite::JumpTableTarget { table: 0 },
                Box::new(move |f| {
                    f.jump_tables.push(JumpTableData {
                        min_val: 0,
                        targets: vec![BlockId(1), dangling],
                    })
                }),
            ),
            (
                MachIdSite::LandingPad { index: 0 },
                Box::new(move |f| {
                    f.eh_metadata.add_landing_pad(LandingPadEntry {
                        block: dangling,
                        offset: 0,
                        catch_type_indices: vec![0],
                        is_cleanup: false,
                    })
                }),
            ),
            (
                MachIdSite::EhCallSite { index: 0 },
                Box::new(move |f| {
                    f.eh_metadata.add_call_site(EhCallSiteEntry {
                        call_block: BlockId(0),
                        start_offset: 0,
                        length: 4,
                        landing_pad_block: Some(dangling),
                    })
                }),
            ),
            (
                MachIdSite::StackLimitOverflowBlock,
                Box::new(move |f| f.stack_limit_overflow_block = Some(dangling)),
            ),
        ];
        for (site, corrupt) in cases {
            let mut func = well_formed();
            corrupt(&mut func);
            assert_eq!(
                refusal(&func),
                MachIdAdmissionError::StaleCounter {
                    domain: MachIdDomain::Block,
                    counter: u64::from(blocks),
                    live_id: blocks,
                    site,
                },
                "{site}"
            );
            assert_eq!(
                func.create_block(),
                dangling,
                "{site}: the aliasing fresh id"
            );
        }
    }

    #[test]
    fn stack_slot_and_jump_table_references_are_checked() {
        let slots = well_formed().stack_slots.len() as u32;
        let store = (well_formed().insts.len() - 1) as u32;
        let mut operand = well_formed();
        operand.insts[store as usize].operands[1] = MachOperand::StackSlot(StackSlotId(slots));
        assert!(matches!(
            refusal(&operand),
            MachIdAdmissionError::StaleCounter {
                domain: MachIdDomain::StackSlot,
                site: MachIdSite::Operand { operand: 1, .. },
                ..
            }
        ));

        let mut frame_index = well_formed();
        frame_index.insts[store as usize].operands[1] =
            MachOperand::FrameIndex(FrameIdx(slots as i32));
        assert_eq!(refusal(&frame_index).domain(), MachIdDomain::StackSlot);
        // A negative frame index is an offset, not a slot identity.
        frame_index.insts[store as usize].operands[1] = MachOperand::FrameIndex(FrameIdx(-8));
        assert_eq!(frame_index.admit_id_counters(), Ok(()));

        let mut protector = well_formed();
        protector.stack_protector_slot = Some(StackSlotId(slots));
        assert!(matches!(
            refusal(&protector),
            MachIdAdmissionError::StaleCounter {
                site: MachIdSite::StackProtectorSlot,
                ..
            }
        ));

        let mut debug = well_formed();
        debug.debug_meta.local_variables.push(DebugLocalVariable {
            name: "x".into(),
            ty: DebugBaseType::I64,
            storage: DebugVariableStorage::StackSlot(slots),
            decl_line: 1,
        });
        assert!(matches!(
            refusal(&debug),
            MachIdAdmissionError::StaleCounter {
                site: MachIdSite::DebugLocal { index: 0 },
                ..
            }
        ));
        assert_eq!(
            debug.alloc_stack_slot(StackSlot::new(8, 8)),
            StackSlotId(slots),
            "the debug variable would have been bound to a fresh slot"
        );

        let mut table = well_formed();
        table.insts[0].operands[1] = MachOperand::JumpTableIndex(0);
        assert_eq!(
            refusal(&table),
            MachIdAdmissionError::StaleCounter {
                domain: MachIdDomain::JumpTable,
                counter: 0,
                live_id: 0,
                site: MachIdSite::Operand {
                    inst: 0,
                    operand: 1
                },
            }
        );
    }

    #[test]
    fn trap_expansion_records_are_checked() {
        let len = well_formed().insts.len() as u32;
        let mut listed = well_formed();
        listed
            .trap_expansions
            .push(crate::function::TrapExpansionRecord {
                carrier: MachInst::new(AArch64Opcode::Nop, vec![]),
                insts: vec![InstId(0), InstId(len)],
            });
        assert_eq!(
            refusal(&listed),
            MachIdAdmissionError::StaleCounter {
                domain: MachIdDomain::Inst,
                counter: u64::from(len),
                live_id: len,
                site: MachIdSite::TrapExpansion { index: 0 },
            }
        );
        let mut carrier = well_formed();
        carrier
            .trap_expansions
            .push(crate::function::TrapExpansionRecord {
                carrier: MachInst::new(AArch64Opcode::MovI, vec![vreg(9), MachOperand::Imm(0)]),
                insts: vec![InstId(0)],
            });
        assert!(matches!(
            refusal(&carrier),
            MachIdAdmissionError::StaleCounter {
                domain: MachIdDomain::VReg,
                live_id: 9,
                site: MachIdSite::TrapExpansion { index: 0 },
                ..
            }
        ));
    }

    #[test]
    fn legacy_vreg_allocator_saturates_instead_of_wrapping() {
        let mut func = well_formed();
        func.next_vreg = u32::MAX - 1;
        assert_eq!(func.alloc_vreg(), u32::MAX - 1);
        assert_eq!(func.next_vreg, u32::MAX);
        for _ in 0..3 {
            assert_eq!(
                func.alloc_vreg(),
                u32::MAX,
                "exhaustion returns the sentinel"
            );
            assert_eq!(func.next_vreg, u32::MAX, "the counter never wraps to 0");
        }
        // An unused sentinel is harmless; a used one is refused by name.
        assert_eq!(func.admit_id_counters(), Ok(()));
        let sentinel = func.alloc_vreg();
        let use_id = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(sentinel)]));
        func.append_inst(BlockId(0), use_id);
        let error = refusal(&func);
        assert_eq!(
            error,
            MachIdAdmissionError::Exhausted {
                domain: MachIdDomain::VReg,
                extent: u64::from(u32::MAX),
                site: Some(MachIdSite::Operand {
                    inst: use_id.0,
                    operand: 0
                }),
            }
        );
        assert!(error.to_string().starts_with("[TCG-MIR-ID-EXHAUSTED] vreg"));
    }

    #[test]
    fn boundary_refusal_names_function_and_builds_label_lazily() {
        let mut func = well_formed();
        assert_eq!(
            func.admit_id_counters_at(|| unreachable!("label built on success")),
            Ok(())
        );
        let mut stale = well_formed();
        stale.next_vreg = 0;
        let refusal = stale
            .admit_id_counters_at(|| "exit of pass `p`".into())
            .unwrap_err();
        assert_eq!(refusal.function, "f");
        assert_eq!(refusal.boundary, "exit of pass `p`");
        assert!(
            refusal.to_string().starts_with(
                "function `f` refused at exit of pass `p`: [TCG-MIR-STALE-ID-COUNTER]"
            ),
            "{refusal}"
        );
    }

    #[test]
    fn a_marked_boundary_rederives_at_the_first_allocation_and_refusal_is_sticky() {
        let mut func = well_formed();
        func.require_id_admission_before_allocation();
        func.next_vreg = 1; // v1 is live
        // The legacy allocator keeps its signature and issues the stale ID;
        // the refusal it recorded fails the function at the pass's exit.
        assert_eq!(func.alloc_vreg(), 1);
        let refusal = func
            .id_admission_refusal()
            .expect("the first allocation after a boundary re-derives");
        assert_eq!(
            refusal,
            MachIdAdmissionError::StaleCounter {
                domain: MachIdDomain::VReg,
                counter: 1,
                live_id: 1,
                site: MachIdSite::Operand {
                    inst: 1,
                    operand: 0
                },
            }
        );
        // The checked allocators refuse at the call site, changing nothing.
        let before = format!("{func:?}");
        assert_eq!(func.try_alloc_vreg(), None);
        assert_eq!(
            func.try_push_inst(MachInst::new(AArch64Opcode::Nop, vec![])),
            None
        );
        assert_eq!(func.try_create_block(), None);
        assert_eq!(func.try_alloc_stack_slot(StackSlot::new(8, 8)), None);
        assert_eq!(format!("{func:?}"), before);
        // Sticky: neither a repaired counter nor a new boundary clears it.
        func.next_vreg = 100;
        assert_eq!(func.admit_id_counters(), Err(refusal));
        func.require_id_admission_before_allocation();
        assert_eq!(func.id_admission_refusal(), Some(refusal));
        assert_eq!(
            func.admit_id_counters_at(|| "b".into())
                .map_err(|refused| refused.error),
            Err(refusal)
        );
    }

    #[test]
    fn a_planned_register_range_is_admitted_before_it_is_issued() {
        // Admitted after a boundary: the range starts at the counter the
        // planner read, and nothing else moves.
        let mut func = well_formed();
        func.require_id_admission_before_allocation();
        let planned_first = func.next_vreg;
        assert_eq!(
            func.try_alloc_vreg_range(3),
            Some(planned_first..planned_first + 3)
        );
        assert_eq!(func.next_vreg, planned_first + 3);
        assert_eq!(func.id_admission_refusal(), None);

        // A near-miss stale counter (one below the live v1): refused before
        // any ID is issued, sticky, and the counter is not repaired.
        let mut stale = well_formed();
        stale.require_id_admission_before_allocation();
        stale.next_vreg = 1;
        assert_eq!(stale.try_alloc_vreg_range(2), None);
        assert_eq!(stale.next_vreg, 1);
        assert!(matches!(
            stale.id_admission_refusal(),
            Some(MachIdAdmissionError::StaleCounter {
                domain: MachIdDomain::VReg,
                counter: 1,
                live_id: 1,
                ..
            })
        ));
        // Even an empty range runs the admission.
        let mut empty = well_formed();
        empty.require_id_admission_before_allocation();
        empty.next_vreg = 1;
        assert_eq!(empty.try_alloc_vreg_range(0), None);

        // Exhaustion: the range end must stay a representable counter.
        let mut full = MachFunction::new("x".into(), Signature::new(vec![], vec![]));
        full.next_vreg = u32::MAX - 2;
        assert_eq!(full.try_alloc_vreg_range(3), None);
        assert_eq!(full.next_vreg, u32::MAX - 2);
        assert_eq!(full.try_alloc_vreg_range(2), Some(u32::MAX - 2..u32::MAX));
    }

    #[test]
    fn an_admission_before_allocation_refuses_on_the_function_itself() {
        let mut stale = well_formed();
        stale.require_id_admission_before_allocation();
        stale.next_vreg = 1;
        let before = format!("{stale:?}");
        let refusal = stale
            .admit_ids_before_allocation()
            .expect_err("a pending boundary re-derives");
        assert_eq!(stale.id_admission_refusal(), Some(refusal));
        assert_eq!(format!("{stale:?}"), before, "an admission never repairs");
        // A copy taken afterwards carries the refusal; its synchronization
        // cannot launder it.
        let mut copy = stale.clone();
        assert_eq!(copy.try_sync_vreg_counter(), Some(()));
        assert_eq!(copy.try_alloc_vreg(), None);

        let mut clean = well_formed();
        clean.require_id_admission_before_allocation();
        assert_eq!(clean.admit_ids_before_allocation(), Ok(()));
        // Admitted now: the next allocation does not scan again.
        clean.next_vreg = 1;
        assert_eq!(clean.alloc_vreg(), 1);
        assert_eq!(clean.id_admission_refusal(), None);
    }

    #[test]
    fn a_marked_boundary_scans_only_when_the_pass_allocates() {
        let blocks = well_formed().blocks.len() as u32;
        let mut func = well_formed();
        func.require_id_admission_before_allocation();
        func.block_order.push(BlockId(blocks));
        // Nothing was issued, so nothing was refused yet; the next boundary
        // admission or allocation re-derives.
        assert_eq!(func.id_admission_refusal(), None);
        assert_eq!(func.create_block(), BlockId(blocks));
        assert!(matches!(
            func.id_admission_refusal(),
            Some(MachIdAdmissionError::StaleCounter {
                domain: MachIdDomain::Block,
                site: MachIdSite::BlockOrder,
                ..
            })
        ));

        // An eager boundary admission leaves an accepted function admitted.
        let mut clean = well_formed();
        clean.require_id_admission_before_allocation();
        assert_eq!(clean.admit_id_counters_at(|| unreachable!()), Ok(()));
        let id = clean.alloc_vreg();
        assert_eq!(id, 2);
        assert_eq!(clean.id_admission_refusal(), None);
        // `Debug` text describes the IR only, whatever the admission state.
        let mut marked = well_formed();
        marked.require_id_admission_before_allocation();
        assert_eq!(format!("{marked:?}"), format!("{:?}", well_formed()));
    }

    /// Deterministic xorshift64* generator; tests need no external crate.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next() % n.max(1)
        }
    }

    /// Every admitted function: any sequence of legacy allocations issues IDs
    /// that are pairwise distinct and alias no identity the function
    /// referenced at admission, in every domain.
    #[test]
    fn admitted_counters_issue_only_fresh_ids() {
        let mut rng = Rng(0x05ee_d1d5);
        for case in 0..400 {
            let mut func = MachFunction::new(format!("g{case}"), Signature::new(vec![], vec![]));
            for _ in 0..rng.below(4) {
                func.create_block();
            }
            for _ in 0..rng.below(3) {
                func.alloc_stack_slot(StackSlot::new(8, 8));
            }
            // Sparse register IDs, as a producer that numbers its own values.
            let blocks = func.blocks.len() as u64;
            for _ in 0..1 + rng.below(12) {
                let operands = vec![
                    vreg(rng.below(5_000) as u32),
                    vreg(rng.below(5_000) as u32),
                    MachOperand::Block(BlockId(rng.below(blocks) as u32)),
                ];
                let id = func.push_inst(MachInst::new(AArch64Opcode::AddRR, operands));
                if rng.below(4) != 0 {
                    let block = BlockId(rng.below(blocks) as u32);
                    func.append_inst(block, id);
                }
            }
            // A stale counter is refused; synchronized, the same body is
            // admitted.
            func.next_vreg = rng.below(5_000) as u32;
            if func.admit_id_counters().is_err() {
                assert_eq!(func.try_sync_vreg_counter(), Some(()));
            }
            assert_eq!(func.admit_id_counters(), Ok(()), "case {case}");

            let live_vregs: std::collections::BTreeSet<u32> = func
                .insts
                .iter()
                .flat_map(|inst| inst.operands.iter().filter_map(MachOperand::as_vreg))
                .map(|reg| reg.id)
                .collect();
            let insts_before = func.insts.len() as u32;
            let blocks_before = func.blocks.len() as u32;
            let slots_before = func.stack_slots.len() as u32;
            let mut issued = std::collections::BTreeSet::new();
            for _ in 0..rng.below(64) {
                match rng.below(4) {
                    0 => {
                        let id = func.alloc_vreg();
                        assert!(!live_vregs.contains(&id), "case {case}: v{id} aliases");
                        assert!(issued.insert(("v", id)), "case {case}: v{id} reissued");
                    }
                    1 => {
                        let id = func.push_inst(MachInst::new(AArch64Opcode::Nop, vec![]));
                        assert!(id.0 >= insts_before && issued.insert(("i", id.0)));
                    }
                    2 => {
                        let id = func.create_block();
                        assert!(id.0 >= blocks_before && issued.insert(("b", id.0)));
                    }
                    _ => {
                        let id = func.alloc_stack_slot(StackSlot::new(4, 4));
                        assert!(id.0 >= slots_before && issued.insert(("s", id.0)));
                    }
                }
            }
            assert_eq!(
                func.admit_id_counters(),
                Ok(()),
                "case {case} after allocation"
            );
        }
    }
}
