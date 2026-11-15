// trust-cg-verify/cegis_pass.rs - CEGIS superopt pass wrapper
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Wraps the `CegisLoop` primitive as a `MachinePass` so callers can request
// CEGIS-based superoptimization from the optimization pipeline with a
// per-function wall-clock budget for solver-backed verification. Results
// (whether the candidate rewrite was proven equivalent or rejected) are keyed
// into the shared compilation cache under a per-function hash derived from
// (instructions + target triple + cpu + features). Repeat compilations reuse
// cached outcomes so that expensive CEGIS searches are paid for only once per
// input tuple.
//
// ty supremacy blocker #8 (part of epic #390, issue #395).

//! CEGIS superoptimization pass wrapper.
//!
//! This module exposes the existing [`crate::CegisLoop`] verification loop as
//! a [`trust_cg_opt::MachinePass`] implementation. It is feature-gated off by
//! default via [`CegisSuperoptConfig::budget_sec = 0`] and only activates
//! when the pipeline threads through a non-zero budget.
//!
//! # Algorithm per function
//!
//! 1. Compute a deterministic 128-bit hash of the function body + target
//!    triple + CPU + features via [`crate::CegisLoop`]-independent key.
//! 2. Lookup the cache. On a hit: deserialize [`CegisCacheEntry`] and apply
//!    the stored rewrites (skip all solver work), each only where the
//!    search's matcher rebuilds exactly the recorded body; any other entry is
//!    stale and the function is searched again.
//! 3. On a miss: walk every instruction, identify candidate rewrite sites,
//!    and call [`crate::CegisLoop::verify`] with a per-query timeout derived
//!    from `per_query_ms`. `budget_sec` bounds the solver work: its clock
//!    starts with the first solver-backed verification, and no further
//!    verification starts once it has elapsed (see `SolverBudget`).
//! 4. On successful equivalence proofs, record rewrites in
//!    [`CegisCacheEntry`], serialize via [`crate::cegis_cache_codec`], and
//!    store under the function hash.
//!
//! The first payload layer recognizes one hand-seeded single-instruction
//! rewrite: `MulRR x, (Movz #0)` within a block can become `Movz #0` when the
//! replacement is strictly cheaper and CEGIS proves equivalence.

use std::collections::{HashMap, HashSet};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};
use trust_cg_ir::cost_model::{AppleSiliconCostModel, CostModel, CostModelGen};
use trust_cg_ir::provenance::PassId as TracePassId;
use trust_cg_ir::trace::{CompilationTrace, EventKind, Justification, RuleId};
use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, SpecialReg, VReg,
};
use trust_cg_opt::effects::{aarch64_for_each_def_position, aarch64_for_each_use_position};
use trust_cg_opt::{CacheBackend, CacheKey, MachinePass, StableHasher};

use crate::cegis::{CegisLoop, CegisResult};
use crate::cegis_cache_codec::CacheCodecError;
use crate::cegis_pass::obligation::{RewriteObligation, window_obligation};
use crate::failed_proof_reducer::FailedProofCounterexampleCorpus;
use crate::rewrite_admission::{SourceRegionIdentity, TargetAbiLayoutIdentity};
use crate::smt::SmtExpr;
use crate::synthesis::ProvenRuleDb;

#[path = "cegis_pass_obligation.rs"]
mod obligation;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Visit each vreg `inst` reads: the vreg operands at the use positions of
/// the shared AArch64 operand-role model
/// ([`aarch64_for_each_use_position`]).
///
/// Operand 0 is a read for compares, stores, conditional branches and the
/// other opcodes without a register result, and both a def and a read for the
/// tied forms such as `Movk`; a paired or atomic load's defined operands after
/// operand 0 are not reads. `cegis_pass_operand_uses_tests` checks this
/// against the register allocator's partition over every opcode.
fn for_each_vreg_read(inst: &MachInst, mut f: impl FnMut(VReg)) {
    aarch64_for_each_use_position(inst.opcode, inst.operands.len(), |pos| {
        if let Some(MachOperand::VReg(vreg)) = inst.operands.get(pos) {
            f(*vreg);
        }
    });
}

/// Visit each vreg `inst` writes, at the def positions of the shared operand
/// role model ([`aarch64_for_each_def_position`]): operand 0 of a value
/// producer, and the later defined operands of paired loads, writeback
/// addressing and atomics.
fn for_each_vreg_def(inst: &MachInst, mut f: impl FnMut(VReg)) {
    aarch64_for_each_def_position(inst.opcode, inst.operands.len(), |pos| {
        if let Some(MachOperand::VReg(vreg)) = inst.operands.get(pos) {
            f(*vreg);
        }
    });
}

/// Reads of vreg `id`, under any register class, by `inst`.
fn vreg_reads_in(inst: &MachInst, id: u32) -> u32 {
    let mut reads = 0u32;
    for_each_vreg_read(inst, |vreg| {
        if vreg.id == id {
            reads = reads.saturating_add(1);
        }
    });
    reads
}

/// Whether `inst` writes vreg `id` under any register class.
fn defines_vreg_id(inst: &MachInst, id: u32) -> bool {
    let mut defines = false;
    for_each_vreg_def(inst, |vreg| defines |= vreg.id == id);
    defines
}

/// Count the reads of `target`'s id in the instruction arena, including
/// instructions no block schedules any more.
///
/// A rewrite that deletes the instruction defining `target` is sound only if
/// the reads it removes with it are all the reads there are, so this must
/// count every read position, operand 0 included, and nothing else.
fn count_vreg_uses(func: &MachFunction, target: VReg) -> u32 {
    func.insts.iter().fold(0u32, |uses, inst| {
        uses.saturating_add(vreg_reads_in(inst, target.id))
    })
}

/// Record the vregs `inst` defines in a block-local reaching-definition map.
///
/// Every def position counts: a later write to a constant's register at
/// operand 1 (a paired load, say) must hide the materializer from the
/// matchers, and a read at operand 0 must not.
fn record_defs(def_map: &mut HashMap<u32, InstId>, inst_id: InstId, inst: &MachInst) {
    for_each_vreg_def(inst, |vreg| {
        def_map.insert(vreg.id, inst_id);
    });
}

/// The reaching-definition map of `block_id` just before `target_id`.
fn block_prefix_defs(
    func: &MachFunction,
    block_id: BlockId,
    target_id: InstId,
) -> HashMap<u32, InstId> {
    let mut def_map = HashMap::new();
    for &inst_id in &func.block(block_id).insts {
        if inst_id == target_id {
            break;
        }
        record_defs(&mut def_map, inst_id, func.inst(inst_id));
    }
    def_map
}

/// Whether the block schedule of `func` lists some instruction id more than
/// once, within one block or across the blocks of `block_order` (a block
/// listed twice repeats all of its ids).
///
/// Every layer rewrites an instruction in place, in the shared arena, so a
/// rewrite of a repeated id would also change its other occurrences, whose
/// windows the matcher never checked. A well-formed layout schedules each id
/// once; the pass skips any other function rather than reason about it.
fn schedule_repeats_an_instruction(func: &MachFunction) -> bool {
    let mut scheduled = HashSet::with_capacity(func.insts.len());
    func.block_order
        .iter()
        .flat_map(|&block_id| func.block(block_id).insts.iter())
        .any(|&inst_id| !scheduled.insert(inst_id))
}

/// Low-`width` bitmask of a register.
fn mask_u64(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

fn target_matches_config(target: &TargetAbiLayoutIdentity, config: &CegisSuperoptConfig) -> bool {
    target.arch == "aarch64"
        && target.target_triple == config.target_triple
        && target.cpu == config.cpu
        && sorted_feature_strings(&target.features) == sorted_feature_strings(&config.features)
}

fn sorted_feature_strings(features: &[String]) -> Vec<&str> {
    let mut sorted = features.iter().map(String::as_str).collect::<Vec<_>>();
    sorted.sort_unstable();
    sorted
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Cache-key schema for the complete set of inputs that can affect a CEGIS
/// search result.
///
/// This is deliberately separate from the payload codec version: changing a
/// matcher, enumeration order, solver contract, or schedule policy can change
/// which proven rewrites a bounded search discovers without changing the
/// serialized entry layout. Such a change must bump this revision.
///
/// Revision 2: the per-function budget gates only the start of solver-backed
/// verifications (see `SolverBudget`) instead of every instruction.
///
/// Revision 3: the matchers and cache replay read and write registers by the
/// shared operand-role model. Revision 2 skipped operand 0 of every
/// instruction when counting reads, so a `Movz` whose register a compare,
/// store or `Movk` also read (at operand 0) was spliced out, leaving that
/// read undefined, and it ignored definitions after operand 0. Its entries
/// can therefore record wrong-code rewrites and must never replay; the
/// candidate set also changed (`AddRI` immediates beyond `imm12` are no longer
/// candidates), and every obligation, and so every proof hash, is now built
/// from the instruction windows instead of the matcher's constant.
///
/// Two later changes kept revision 3: replay now applies a recorded body only
/// if the matcher rebuilds it exactly, and the pass skips a schedule that
/// repeats an instruction id. The search records the same entries, every
/// honest revision 3 entry still replays, and a skipped function never reads
/// its entry.
pub const CEGIS_SEARCH_SEMANTICS_REVISION: u32 = 3;

/// Version of the outer-executor schedule identity bound into CEGIS keys.
///
/// A wall-clock-bounded search is sensitive to the amount of concurrent work
/// sharing its CPU. The schedule is therefore an artifact input until the
/// search moves to deterministic fuel rather than elapsed time.
pub const CEGIS_SEARCH_SCHEDULE_VERSION: u32 = 1;

/// Effective outer-executor schedule for one CEGIS invocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CegisSearchScheduleIdentity {
    effective_parallelism: u32,
}

impl CegisSearchScheduleIdentity {
    /// A search running outside a parallel executor.
    pub const fn serial() -> Self {
        Self {
            effective_parallelism: 1,
        }
    }

    /// Explicit schedule identity for an embedding that already resolved its
    /// worker plan.
    pub const fn with_effective_parallelism(effective_parallelism: u32) -> Self {
        Self {
            effective_parallelism: if effective_parallelism == 0 {
                1
            } else {
                effective_parallelism
            },
        }
    }

    /// Resolve the Rayon executor currently driving this call.
    ///
    /// Outside a Rayon worker the CEGIS pass itself is serial, so the identity
    /// is one. Inside module/file fanout, `current_num_threads` is the exact
    /// width of the pool whose workers contend for the wall-clock search.
    pub fn current_execution() -> Self {
        if rayon::current_thread_index().is_none() {
            return Self::serial();
        }
        let effective_parallelism = u32::try_from(rayon::current_num_threads()).unwrap_or(u32::MAX);
        Self::with_effective_parallelism(effective_parallelism)
    }

    /// Number of workers in the effective outer schedule.
    pub const fn effective_parallelism(self) -> u32 {
        self.effective_parallelism
    }
}

impl Default for CegisSearchScheduleIdentity {
    fn default() -> Self {
        Self::serial()
    }
}

/// Configuration for [`CegisSuperoptPass`].
///
/// The pass is effectively disabled when `budget_sec == 0`, which is the
/// default. The CLI flag `--cegis-superopt=<secs>` sets this field to a
/// non-zero value.
#[derive(Clone)]
pub struct CegisSuperoptConfig {
    /// Per-function wall-clock budget, in seconds, for solver-backed
    /// verification. Its clock starts with the function's first solver-backed
    /// verification; no further verification starts once it has elapsed, and
    /// the search then fails closed as
    /// [`CegisSearchCompletion::DeadlineExceeded`]. The structural walk that
    /// finds candidates is linear in the function and always completes.
    /// `0` disables the pass.
    pub budget_sec: u64,
    /// Per solver query timeout (milliseconds).
    pub per_query_ms: u64,
    /// Target triple (used for cache keying).
    pub target_triple: String,
    /// CPU variant (e.g. "apple-m1"; used for cache keying).
    pub cpu: String,
    /// Target features (used for cache keying; order-invariant).
    pub features: Vec<String>,
    /// Optimization level (0-3, used for cache keying).
    pub opt_level: u8,
    /// Effective outer-executor schedule (used for cache keying).
    ///
    /// This is result-affecting while `budget_sec` and `per_query_ms` are
    /// wall-clock limits: a wider outer fanout can change which candidates or
    /// solver queries finish before those limits.
    pub search_schedule: CegisSearchScheduleIdentity,
    /// Optional cache backend. If `None`, the pass runs but never caches.
    pub cache: Option<Arc<dyn CacheBackend>>,
    /// Optional structured compilation trace collector. When set, the pass
    /// emits a per-function summary event via [`CompilationTrace::emit`] at
    /// the end of [`CegisSuperoptPass::run`]. Level filtering is delegated
    /// to the trace itself (see [`trust_cg_ir::trace::TraceLevel`]); passing
    /// a trace at level `None` is effectively a no-op.
    pub trace: Option<Arc<CompilationTrace>>,
}

impl CegisSuperoptConfig {
    /// Build a disabled-default configuration.
    pub fn disabled() -> Self {
        Self {
            budget_sec: 0,
            per_query_ms: 5_000,
            target_triple: String::new(),
            cpu: String::new(),
            features: Vec::new(),
            opt_level: 2,
            search_schedule: CegisSearchScheduleIdentity::serial(),
            cache: None,
            trace: None,
        }
    }

    /// Returns true if this configuration will actually run CEGIS queries.
    #[inline]
    pub fn is_enabled(&self) -> bool {
        self.budget_sec > 0
    }
}

impl Default for CegisSuperoptConfig {
    fn default() -> Self {
        Self::disabled()
    }
}

impl std::fmt::Debug for CegisSuperoptConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CegisSuperoptConfig")
            .field("budget_sec", &self.budget_sec)
            .field("per_query_ms", &self.per_query_ms)
            .field("target_triple", &self.target_triple)
            .field("cpu", &self.cpu)
            .field("features", &self.features)
            .field("opt_level", &self.opt_level)
            .field("search_schedule", &self.search_schedule)
            .field("cache", &self.cache.as_ref().map(|_| "<CacheBackend>"))
            .field("trace", &self.trace.as_ref().map(|t| t.level()))
            .finish()
    }
}

// ---------------------------------------------------------------------------
// Cache entry
// ---------------------------------------------------------------------------

/// Which matcher / payload layer produced a rewrite.
///
/// Stored alongside each cached [`ProvenRewrite`] so the cache-hit replay
/// path can apply serialized replacement bodies without re-invoking CEGIS.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RewriteLayer {
    /// Layer A — single-instruction rewrite (e.g. `MulRR x, Movz #0` → `Movz #0`).
    A,
    /// Layer B — two-instruction window fusion (e.g. `Movz+AddRR` → `AddRI`).
    B,
    /// Layer C — constant materialization feeding `AndRR` fused into `AndRI`.
    C,
}

/// A matched Layer C window: the materializer chain in schedule order and the
/// `AndRI` that replaces the `AndRR` it feeds.
#[derive(Debug, Clone)]
struct LayerCAndImmCandidate {
    materializer_ids: Vec<InstId>,
    replacement: MachInst,
}

/// Serializable register-class projection for [`MachInstBlob`] operands.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum RegClassBlob {
    Gpr64,
    Gpr32,
    Fpr128,
    Fpr64,
    Fpr32,
    Fpr16,
    Fpr8,
    System,
}

impl From<RegClass> for RegClassBlob {
    fn from(class: RegClass) -> Self {
        match class {
            RegClass::Gpr64 => Self::Gpr64,
            RegClass::Gpr32 => Self::Gpr32,
            RegClass::Fpr128 => Self::Fpr128,
            RegClass::Fpr64 => Self::Fpr64,
            RegClass::Fpr32 => Self::Fpr32,
            RegClass::Fpr16 => Self::Fpr16,
            RegClass::Fpr8 => Self::Fpr8,
            RegClass::System => Self::System,
        }
    }
}

impl From<RegClassBlob> for RegClass {
    fn from(class: RegClassBlob) -> Self {
        match class {
            RegClassBlob::Gpr64 => Self::Gpr64,
            RegClassBlob::Gpr32 => Self::Gpr32,
            RegClassBlob::Fpr128 => Self::Fpr128,
            RegClassBlob::Fpr64 => Self::Fpr64,
            RegClassBlob::Fpr32 => Self::Fpr32,
            RegClassBlob::Fpr16 => Self::Fpr16,
            RegClassBlob::Fpr8 => Self::Fpr8,
            RegClassBlob::System => Self::System,
        }
    }
}

/// Serializable special-register projection for [`MachInstBlob`] operands.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SpecialRegBlob {
    SP,
    XZR,
    WZR,
}

impl From<SpecialReg> for SpecialRegBlob {
    fn from(reg: SpecialReg) -> Self {
        match reg {
            SpecialReg::SP => Self::SP,
            SpecialReg::XZR => Self::XZR,
            SpecialReg::WZR => Self::WZR,
        }
    }
}

impl From<SpecialRegBlob> for SpecialReg {
    fn from(reg: SpecialRegBlob) -> Self {
        match reg {
            SpecialRegBlob::SP => Self::SP,
            SpecialRegBlob::XZR => Self::XZR,
            SpecialRegBlob::WZR => Self::WZR,
        }
    }
}

/// Serializable projection of [`MachOperand`] used by [`MachInstBlob`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum MachOperandBlob {
    VReg { id: u32, class: RegClassBlob },
    PReg { encoding: u16 },
    Imm(i64),
    FImmBits(u64),
    Block(u32),
    StackSlot(u32),
    FrameIndex(i32),
    MemOp { base_encoding: u16, offset: i64 },
    Special(SpecialRegBlob),
    Symbol(String),
    JumpTableIndex(u32),
    IncomingArg(i64),
    ExactModuleSymbol(String),
}

impl MachOperandBlob {
    fn from_operand(operand: &MachOperand) -> Self {
        match operand {
            MachOperand::VReg(vreg) => Self::VReg {
                id: vreg.id,
                class: vreg.class.into(),
            },
            MachOperand::PReg(preg) => Self::PReg {
                encoding: preg.encoding(),
            },
            MachOperand::Imm(imm) => Self::Imm(*imm),
            MachOperand::FImm(fimm) => Self::FImmBits(fimm.to_bits()),
            MachOperand::Block(block) => Self::Block(block.0),
            MachOperand::StackSlot(slot) => Self::StackSlot(slot.0),
            MachOperand::FrameIndex(frame) => Self::FrameIndex(frame.0),
            MachOperand::MemOp { base, offset } => Self::MemOp {
                base_encoding: base.encoding(),
                offset: *offset,
            },
            MachOperand::Special(reg) => Self::Special((*reg).into()),
            MachOperand::Symbol(symbol) => Self::Symbol(symbol.clone()),
            MachOperand::ExactModuleSymbol(symbol) => Self::ExactModuleSymbol(symbol.clone()),
            MachOperand::JumpTableIndex(index) => Self::JumpTableIndex(*index),
            MachOperand::IncomingArg(offset) => Self::IncomingArg(*offset),
        }
    }

    /// The inverse of [`Self::from_operand`], which the tests use to show the
    /// projection loses nothing that replay's equality check relies on.
    #[cfg(test)]
    fn to_operand(&self) -> MachOperand {
        match self {
            Self::VReg { id, class } => MachOperand::VReg(VReg::new(*id, (*class).into())),
            Self::PReg { encoding } => MachOperand::PReg(trust_cg_ir::PReg::new(*encoding)),
            Self::Imm(imm) => MachOperand::Imm(*imm),
            Self::FImmBits(bits) => MachOperand::FImm(f64::from_bits(*bits)),
            Self::Block(block) => MachOperand::Block(trust_cg_ir::BlockId(*block)),
            Self::StackSlot(slot) => MachOperand::StackSlot(trust_cg_ir::StackSlotId(*slot)),
            Self::FrameIndex(frame) => MachOperand::FrameIndex(trust_cg_ir::FrameIdx(*frame)),
            Self::MemOp {
                base_encoding,
                offset,
            } => MachOperand::MemOp {
                base: trust_cg_ir::PReg::new(*base_encoding),
                offset: *offset,
            },
            Self::Special(reg) => MachOperand::Special((*reg).into()),
            Self::Symbol(symbol) => MachOperand::Symbol(symbol.clone()),
            Self::ExactModuleSymbol(symbol) => MachOperand::ExactModuleSymbol(symbol.clone()),
            Self::JumpTableIndex(index) => MachOperand::JumpTableIndex(*index),
            Self::IncomingArg(offset) => MachOperand::IncomingArg(*offset),
        }
    }
}

/// Cache-format projection of a replacement [`MachInst`].
///
/// The cache format stores opcode + operands only. Replay never decodes a
/// blob into an instruction: it rebuilds the replacement with the matcher and
/// applies it only if its projection equals the recorded blob, so the
/// projection must be injective on opcodes and operands
/// (`exact_module_symbol_projection_preserves_binding` round-trips it). The
/// rebuilt instruction carries the `proof` and `source_loc` of the
/// instruction it replaces.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MachInstBlob {
    pub opcode: String,
    pub operands: Vec<MachOperandBlob>,
}

impl MachInstBlob {
    fn from_inst(inst: &MachInst) -> Self {
        Self {
            opcode: format!("{:?}", inst.opcode),
            operands: inst
                .operands
                .iter()
                .map(MachOperandBlob::from_operand)
                .collect(),
        }
    }
}

/// A single CEGIS rewrite proof recorded in the cache.
///
/// `inst_index` is the flat [`MachFunction::insts`] index that was verified
/// equivalent to `replacement`. `window_len` records the source window consumed
/// by the rewrite. A cache hit skips CEGIS: it re-runs the layer's matcher at
/// `inst_index` and applies the rewrite only if the matcher admits a window of
/// `window_len` and rebuilds exactly `replacement`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProvenRewrite {
    /// Instruction index in `MachFunction::insts`.
    pub inst_index: u32,
    /// Proof hash from [`CegisResult::Equivalent::proof_hash`].
    pub proof_hash: u64,
    /// Number of CEGIS iterations used to prove equivalence.
    pub iterations: u32,
    /// Number of source instructions consumed by this rewrite.
    pub window_len: u32,
    /// Serialized replacement body. A cache hit applies it only if the
    /// matcher, run on the current body, rebuilds exactly this body.
    pub replacement: Vec<MachInstBlob>,
    /// Which payload layer produced this rewrite (used for stats and splices).
    pub layer: RewriteLayer,
}

/// Whether a cache entry represents a complete search of every candidate the
/// configured policy was entitled to inspect.
///
/// Only [`Self::Complete`] may be published or replayed. The other variants
/// are retained as typed internal outcomes so a deadline, query timeout,
/// verifier failure, or panic cannot be mistaken for a proven negative result.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum CegisSearchCompletion {
    /// Search has not reached a publishable terminal state.
    #[default]
    NotCompleted,
    /// Every candidate was considered and every query reached a definitive
    /// result.
    Complete,
    /// The per-function wall-clock budget had elapsed when a further
    /// candidate needed a solver-backed verification.
    DeadlineExceeded,
    /// A solver query timed out or exhausted its iteration budget.
    QueryIncomplete,
    /// The verifier returned an operational error.
    VerifierError,
    /// The verifier panicked and the pass contained the unwind.
    VerifierPanicked,
}

impl CegisSearchCompletion {
    fn record(&mut self, outcome: Self) {
        if *self == Self::Complete && outcome != Self::Complete {
            *self = outcome;
        }
    }

    /// Whether this outcome is safe to persist and replay as a complete search.
    pub const fn is_complete(self) -> bool {
        matches!(self, Self::Complete)
    }
}

/// Typed terminal result of one CEGIS pass invocation.
///
/// An incomplete search never exposes mutations: cache misses run against a
/// private working copy and publish it only after every layer reaches
/// [`CegisSearchCompletion::Complete`]. The legacy [`MachinePass`] boolean API
/// maps `Disabled` and `Incomplete` to `false`.
#[must_use = "an incomplete CEGIS transaction must be handled explicitly"]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CegisRunOutcome {
    /// The configured budget was zero, so the pass did not run.
    Disabled,
    /// Every candidate received a definitive result and mutations, if any,
    /// were committed atomically.
    Complete {
        /// Whether the committed result changed the machine function.
        committed: bool,
    },
    /// Deadline/query/verifier failure aborted the transaction.
    Incomplete {
        /// Fail-closed reason reported by the search.
        completion: CegisSearchCompletion,
    },
}

impl CegisRunOutcome {
    /// Whether a complete transaction changed the machine function.
    pub const fn committed(self) -> bool {
        matches!(self, Self::Complete { committed: true })
    }

    /// The incomplete reason, if the transaction was rolled back.
    pub const fn incomplete_reason(self) -> Option<CegisSearchCompletion> {
        match self {
            Self::Incomplete { completion } => Some(completion),
            Self::Disabled | Self::Complete { .. } => None,
        }
    }
}

/// Serializable cache entry stored under the per-function cache key.
///
/// Encoded by [`crate::cegis_cache_codec`], which owns the byte layout and the
/// fail-closed reader. Format version is bumped whenever fields OR the layout
/// change; older cache entries are rejected by the decoder (equivalent to a
/// cache miss).
///
/// The `Serialize`/`Deserialize` derives on this type and its components are
/// **not** the cache format any more. They are retained for two reasons: the
/// acceptance differential in `tests/cegis_cache_codec.rs` compares this
/// codec against the previous `rmp-serde` encoding, which needs them; and
/// harnesses roundtrip these types through JSON. Do not route the cache
/// through them.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CegisCacheEntry {
    /// Format version. Bump when fields change.
    pub version: u32,
    /// Typed completion state. Only `Complete` entries are publishable.
    pub completion: CegisSearchCompletion,
    /// All rewrites proven equivalent on this function.
    pub proven_rewrites: Vec<ProvenRewrite>,
    /// Number of candidate sites attempted.
    pub attempted: u64,
    /// Number of sites where equivalence was proven (== proven_rewrites.len()).
    pub verified: u64,
    /// Number of sites rejected (not equivalent / timeout / error).
    pub rejected: u64,
}

impl CegisCacheEntry {
    /// Format version.
    ///
    /// History:
    /// - v1: Layer A only; no replay.
    /// - v2: Layer B added (two-instruction window fusion); still no replay —
    ///   cache hits silently skipped rewrites, causing un-replayed mutation
    ///   and phantom verification counts (#491).
    /// - v3: `ProvenRewrite` gained a `layer` tag and the cache-hit path now
    ///   replays rewrites via `apply_cached_rewrite` (#491). Stats increments
    ///   on replay reflect rewrites actually applied this run, not cached
    ///   counts.
    /// - v4: `ProvenRewrite` gained `window_len` and serialized
    ///   `replacement: Vec<MachInstBlob>` so replay applies the cached body
    ///   directly instead of re-running the matcher (#492).
    /// - v5: Layer C added constant-mask materialization fusion for bit-reverse
    ///   idioms (#854). Empty v4 entries must be invalidated so newly-covered
    ///   functions are re-enumerated instead of replaying a stale no-op.
    /// - v6: the payload format changed from MessagePack (`rmp-serde`) to the
    ///   in-tree [`crate::cegis_cache_codec`]. No field changed. This is a pure
    ///   wire-format break: `rmp-serde` was the last third-party normal
    ///   dependency edge keeping `rmp-serde`/`rmp` — and one of the edges
    ///   keeping `serde` — in the shipping closure, so every proof over a unit
    ///   that reaches this cache was conditional on code Trust does not own.
    ///   v5 blobs do not carry the v6 magic and are rejected structurally,
    ///   before any field is parsed.
    /// - v7: entries carry an explicit completion state. This invalidates v6
    ///   entries because the old writer cached partial/empty prefixes after a
    ///   deadline, query timeout, verifier error, or panic.
    ///
    /// Older entries are silently rejected as a miss; this is semantics-
    /// preserving because the pass simply re-runs enumeration on the next
    /// invocation.
    pub const VERSION: u32 = 7;

    /// Fresh empty entry with the current version.
    pub fn empty() -> Self {
        Self {
            version: Self::VERSION,
            completion: CegisSearchCompletion::Complete,
            ..Default::default()
        }
    }

    fn search_in_progress() -> Self {
        Self {
            version: Self::VERSION,
            completion: CegisSearchCompletion::NotCompleted,
            ..Default::default()
        }
    }

    /// Encode to cache bytes.
    ///
    /// Fails if the search is incomplete or if a sequence exceeds the `u32`
    /// wire length prefix. The one caller that writes to a backend drops the
    /// put on an error rather than failing the compilation.
    pub fn encode(&self) -> Result<Vec<u8>, CacheCodecError> {
        if !self.completion.is_complete() {
            return Err(CacheCodecError::IncompleteSearch {
                completion: self.completion,
            });
        }
        crate::cegis_cache_codec::encode_entry(self)
    }

    /// Decode from cache bytes. Returns `None` for anything the caller must
    /// treat as a miss: wrong magic, wrong [`Self::VERSION`], an unknown tag, a
    /// short read, a non-UTF-8 opcode or symbol, or trailing bytes.
    ///
    /// This is the fail-closed side of a read that carries proof authority — a
    /// hit replays recorded rewrites **without** re-running CEGIS — so every
    /// ambiguity resolves to a miss. See [`crate::cegis_cache_codec`].
    pub fn decode(bytes: &[u8]) -> Option<Self> {
        let entry = crate::cegis_cache_codec::decode_entry(bytes)?;
        entry.completion.is_complete().then_some(entry)
    }
}

// ---------------------------------------------------------------------------
// Stats
// ---------------------------------------------------------------------------

/// Runtime statistics for a single [`CegisSuperoptPass`] execution.
///
/// These are the canonical observability counters for the CEGIS pass. Fields
/// are grouped into four categories:
///
/// - **Coverage** (`functions_seen`, cache hit/miss/put counts).
/// - **Per-layer work** (`layer_a_candidates`, `layer_a_committed`,
///   `layer_b_candidates`, `layer_b_committed`). `candidates` and `verified`
///   are roll-ups across all layers and are retained for backwards
///   compatibility with the #486 Layer A acceptance criteria.
/// - **Timing** (`total_wall_ms`, `solver_ms`). Wall time is measured from
///   the first call to [`CegisSuperoptPass::run`] for this function; solver
///   time is the cumulative sum of elapsed time inside solver calls.
/// - **Failure modes** (`rejected`, `budget_exhausted`, `timeouts`,
///   `verifier_errors`, `panics`). Each failure is counted in exactly one
///   bucket: a candidate that timed out bumps `timeouts` + `rejected`; a
///   verifier error bumps `verifier_errors` + `rejected`; a panic bumps
///   `panics` + `rejected`. Plain "not equivalent" / cost-not-profitable
///   rejections bump `rejected` only.
///
/// The struct derives `Serialize`/`Deserialize` so that harnesses can
/// roundtrip stats through JSON for weekly-report ingestion (#486 §10).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CegisPassStats {
    /// Number of functions the pass ran on (regardless of result).
    pub functions_seen: u64,
    /// Number of cache hits (result was read from the cache).
    pub cache_hits: u64,
    /// Number of cache misses (CEGIS actually ran).
    pub cache_misses: u64,
    /// Number of cache puts after a successful verification pass.
    pub cache_puts: u64,
    /// Number of decoded cache entries refused on replay because a recorded
    /// rewrite is not one the matchers admit and rebuild exactly on the
    /// current body. Each is also a miss: the function is searched again and
    /// a complete search rewrites the entry.
    #[serde(default)]
    pub cache_stale: u64,
    /// Number of functions skipped, with no cache lookup and no search,
    /// because their block schedule lists an instruction id more than once
    /// (`schedule_repeats_an_instruction`).
    #[serde(default)]
    pub repeated_schedule_skips: u64,
    /// Number of candidate rewrite sites considered (all layers).
    pub candidates: u64,
    /// Number of candidate sites proven equivalent (all layers).
    pub verified: u64,
    /// Number of candidate sites rejected (not equivalent / timeout / error).
    pub rejected: u64,
    /// Number of searches stopped because the wall-clock budget had elapsed
    /// before a further solver-backed verification could start.
    pub budget_exhausted: u64,
    /// Number of solver calls made (across all CegisLoop instances).
    pub solver_calls: u64,
    /// Number of verifier panics caught and contained.
    pub panics: u64,
    /// Number of Layer A candidate sites considered (single-instruction
    /// rewrites such as `MulRR x, Movz #0` → `Movz #0`).
    pub layer_a_candidates: u64,
    /// Number of Layer A rewrites actually committed (proven equivalent AND
    /// strictly cost-better, OR replayed from the cache). Strict subset of
    /// `layer_a_candidates` on the cold path; independent on the hot path.
    pub layer_a_committed: u64,
    /// Number of Layer B candidate sites considered (two-instruction window
    /// fusion such as `Movz+AddRR` → `AddRI`).
    pub layer_b_candidates: u64,
    /// Number of Layer B rewrites actually committed.
    pub layer_b_committed: u64,
    /// Total wall-clock time spent in the pass across all invocations this
    /// pass instance has seen, in milliseconds. Measured around the entire
    /// `run_inner` body, so it includes cache lookups, replay, and CEGIS.
    pub total_wall_ms: u64,
    /// Cumulative time spent inside `CegisLoop::verify` (i.e. wall time
    /// elapsed across SMT / concrete-eval work), in milliseconds. Strict
    /// subset of `total_wall_ms` on any single invocation.
    pub solver_ms: u64,
    /// Number of candidate sites whose CEGIS query returned a solver timeout
    /// ([`CegisResult::Timeout`] or [`CegisResult::MaxIterationsReached`]).
    /// Subset of `rejected`.
    pub timeouts: u64,
    /// Number of candidate sites whose CEGIS query returned a verifier error
    /// ([`CegisResult::Error`]). Distinct from `timeouts` and from
    /// "not equivalent" rejections. Subset of `rejected`.
    pub verifier_errors: u64,
}

/// Test-only controls for deterministic CEGIS payload failure-mode coverage.
///
/// These hooks keep the runtime configuration surface unchanged while letting
/// integration tests drive budget, cost-gate, and verifier-error paths without
/// depending on wall-clock sleeps or external solver behavior.
#[doc(hidden)]
#[derive(Debug, Clone, Default)]
pub struct CegisSuperoptTestHooks {
    /// The budget reads as elapsed before the first solver-backed
    /// verification.
    pub force_expired_deadline: bool,
    /// The budget reads as elapsed once this many solver-backed verifications
    /// have been admitted, as if the last of them had run past it.
    pub force_deadline_after_verifications: Option<u32>,
    pub force_layer_a_equal_cost: bool,
    pub force_layer_b_equal_cost: bool,
    pub verifier_result: Option<CegisResult>,
    /// Corrupt every matched replacement before its obligation is built, as
    /// a matcher bug would. The mutation control for the obligations: each
    /// corrupted rewrite must be refuted, never committed.
    pub corrupt_replacement: Option<ReplacementMutation>,
}

/// A deliberate matcher bug, applied by
/// [`CegisSuperoptTestHooks::corrupt_replacement`].
#[doc(hidden)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReplacementMutation {
    /// The wrong immediate: an `AddRI` or `Movz` immediate with its low bit
    /// flipped, or an `AndRI` mask rotated right by one bit (still a logical
    /// immediate).
    Immediate,
    /// The wrong register: the replacement reads the constant register the
    /// rewrite removes (or, for Layer A, keeps) instead of its source.
    SourceRegister,
    /// The wrong operation: `AddRI` and `AndRI` swapped.
    Operation,
}

impl ReplacementMutation {
    fn apply(self, replacement: &mut MachInst, constant_register: Option<&MachOperand>) {
        let width = replacement
            .operands
            .first()
            .and_then(MachOperand::as_vreg)
            .and_then(|vreg| gpr_width(vreg.class))
            .unwrap_or(64);
        let opcode = replacement.opcode;
        match (self, opcode, replacement.operands.as_mut_slice()) {
            (Self::Immediate, AArch64Opcode::AndRI, [_, _, MachOperand::Imm(imm)]) => {
                let mask = (*imm as u64) & mask_u64(width);
                *imm = (((mask >> 1) | (mask << (width - 1))) & mask_u64(width)) as i64;
            }
            (Self::Immediate, AArch64Opcode::AddRI, [_, _, MachOperand::Imm(imm)])
            | (Self::Immediate, AArch64Opcode::Movz, [_, MachOperand::Imm(imm), ..]) => {
                *imm ^= 1;
            }
            (Self::SourceRegister, AArch64Opcode::AddRI | AArch64Opcode::AndRI, [_, source, _]) => {
                if let Some(constant) = constant_register {
                    *source = constant.clone();
                }
            }
            (Self::Operation, AArch64Opcode::AddRI, _) => {
                replacement.opcode = AArch64Opcode::AndRI;
            }
            (Self::Operation, AArch64Opcode::AndRI, _) => {
                replacement.opcode = AArch64Opcode::AddRI;
            }
            // Layer A's `Movz dst, #0` has no source register or operation
            // to get wrong.
            _ => {}
        }
    }
}

impl CegisSuperoptTestHooks {
    fn affects_execution(&self) -> bool {
        self.force_expired_deadline
            || self.force_deadline_after_verifications.is_some()
            || self.force_layer_a_equal_cost
            || self.force_layer_b_equal_cost
            || self.verifier_result.is_some()
            || self.corrupt_replacement.is_some()
    }

    /// Apply [`Self::corrupt_replacement`], if set, to a matched
    /// `replacement` whose window materializes `constant_register`.
    fn corrupt(&self, replacement: &mut MachInst, constant_register: Option<&MachOperand>) {
        if let Some(mutation) = self.corrupt_replacement {
            mutation.apply(replacement, constant_register);
        }
    }

    fn write_cache_identity(&self, h: &mut StableHasher) {
        if !self.affects_execution() {
            h.write_u8(0);
            return;
        }

        h.write_u8(1);
        h.write_u8(u8::from(self.force_expired_deadline));
        match self.force_deadline_after_verifications {
            None => h.write_u8(0),
            Some(started) => {
                h.write_u8(1);
                h.write_u32(started);
            }
        }
        h.write_u8(u8::from(self.force_layer_a_equal_cost));
        h.write_u8(u8::from(self.force_layer_b_equal_cost));
        match self.verifier_result.as_ref() {
            None => h.write_u8(0),
            Some(CegisResult::Equivalent {
                proof_hash,
                iterations,
            }) => {
                h.write_u8(1);
                h.write_u64(*proof_hash);
                h.write_u64(u64::try_from(*iterations).unwrap_or(u64::MAX));
            }
            Some(CegisResult::NotEquivalent {
                counterexample,
                found_by_concrete,
            }) => {
                h.write_u8(2);
                h.write_u8(u8::from(*found_by_concrete));
                let mut values = counterexample.values.iter().collect::<Vec<_>>();
                values.sort_unstable_by_key(|(left, _)| *left);
                h.write_u64(u64::try_from(values.len()).unwrap_or(u64::MAX));
                for (name, value) in values {
                    h.write_str(name);
                    h.write_u64(*value);
                }
            }
            Some(CegisResult::Timeout) => h.write_u8(3),
            Some(CegisResult::MaxIterationsReached { counterexamples }) => {
                h.write_u8(4);
                h.write_u64(u64::try_from(*counterexamples).unwrap_or(u64::MAX));
            }
            Some(CegisResult::Error(message)) => {
                h.write_u8(5);
                h.write_str(message);
            }
        }
        match self.corrupt_replacement {
            None => h.write_u8(0),
            Some(mutation) => {
                h.write_u8(1);
                h.write_u8(mutation as u8);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Solver budget
// ---------------------------------------------------------------------------

/// Per-function budget for solver-backed verifications.
///
/// The budget bounds solver work, the only part of a search whose cost is not
/// linear in the function: the structural walk that matches candidates keeps
/// its facts in [`IndexedWalkFacts`] and always runs to the end. The clock
/// starts when the search admits its first solver-backed verification, and a
/// further verification is admitted only while `budget` has not elapsed since
/// then. A query already running is bounded by `per_query_ms`, not by this
/// budget.
///
/// Consequently a search whose every candidate received a definitive verdict
/// is complete however long its final query ran. A function with at most one
/// solver-backed candidate therefore reaches the same outcome at any machine
/// load as long as that query finishes within `per_query_ms`. That limit is
/// wall-clock time too: it covers the whole verification exchange, including
/// waiting for the solver and the Clean replay, and a query that exceeds it
/// ends the search as [`CegisSearchCompletion::QueryIncomplete`]. Once a
/// function has two or more such candidates, whether a later one may start
/// also depends on measured query time. Only deterministic fuel would remove
/// either dependence, which is why the outer schedule stays in the cache key.
struct SolverBudget {
    budget: Duration,
    clock_started: Option<Instant>,
    admitted: u32,
    /// Test control: the budget reads as elapsed once this many
    /// verifications have been admitted.
    elapsed_after: Option<u32>,
}

impl SolverBudget {
    fn new(budget_sec: u64, hooks: &CegisSuperoptTestHooks) -> Self {
        let elapsed_after = if hooks.force_expired_deadline {
            Some(0)
        } else {
            hooks.force_deadline_after_verifications
        };
        Self {
            budget: Duration::from_secs(budget_sec),
            clock_started: None,
            admitted: 0,
            elapsed_after,
        }
    }

    /// Admit one more solver-backed verification, or report that the budget
    /// has elapsed. The first admission starts the clock.
    fn admit_verification(&mut self) -> bool {
        if self
            .elapsed_after
            .is_some_and(|limit| self.admitted >= limit)
        {
            return false;
        }
        let now = Instant::now();
        let clock_started = *self.clock_started.get_or_insert(now);
        if now.saturating_duration_since(clock_started) >= self.budget {
            return false;
        }
        self.admitted = self.admitted.saturating_add(1);
        true
    }
}

// ---------------------------------------------------------------------------
// Structural walk facts
// ---------------------------------------------------------------------------

/// A constant a block prefix materializes into a vreg, and the move-wide
/// instructions that built it.
type MaterializedConst = (u64, Vec<InstId>);

/// The structural questions the layer matchers ask while a search walks a
/// function, and the events that keep the answers current.
///
/// [`DirectWalkFacts`] answers by scanning the function, so each answer costs
/// time proportional to the function and a walk that asks once per
/// instruction is quadratic. [`IndexedWalkFacts`] answers in amortized
/// constant time from indexes the walk keeps current, which makes the walk
/// linear. The two must agree on every question: the `indexed_walk_facts_*`
/// tests run whole searches under each and require the same candidates,
/// verdict order, cache entry and final function.
trait WalkFacts {
    /// Reads of `vreg` in the instruction arena, as [`count_vreg_uses`]
    /// counts them.
    fn vreg_uses(&self, func: &MachFunction, vreg: VReg) -> u64;

    /// [`CegisSuperoptPass::materialized_wide_const_before`] for the block
    /// the walk has entered.
    fn materialized_wide_const_before(
        &mut self,
        func: &MachFunction,
        block_id: BlockId,
        target_id: InstId,
        target: VReg,
        width: u32,
    ) -> Option<MaterializedConst>;

    /// The walk replaced the arena body `old` of `inst_id` with `new`.
    fn replaced(&mut self, inst_id: InstId, old: &MachInst, new: &MachInst);

    /// A walk that asks [`Self::materialized_wide_const_before`] enters
    /// `block_id`, whose schedule is `schedule`. It must then report each
    /// scheduled instruction to [`Self::passed`] in order, and must not change
    /// the schedule until it leaves the block.
    fn enter_block(&mut self, block_id: BlockId, schedule: &[InstId]);

    /// The walk is done with the next scheduled instruction, whose current
    /// body is `inst`.
    fn passed(&mut self, inst_id: InstId, inst: &MachInst);
}

/// Walk facts answered by scanning the function for each question.
///
/// Cache replay validates one recorded rewrite at a time, where a single scan
/// is cheaper than building an index; the tests also use this as the
/// reference for [`IndexedWalkFacts`].
struct DirectWalkFacts;

impl WalkFacts for DirectWalkFacts {
    fn vreg_uses(&self, func: &MachFunction, vreg: VReg) -> u64 {
        u64::from(count_vreg_uses(func, vreg))
    }

    fn materialized_wide_const_before(
        &mut self,
        func: &MachFunction,
        block_id: BlockId,
        target_id: InstId,
        target: VReg,
        width: u32,
    ) -> Option<MaterializedConst> {
        CegisSuperoptPass::materialized_wide_const_before(func, block_id, target_id, target, width)
    }

    fn replaced(&mut self, _inst_id: InstId, _old: &MachInst, _new: &MachInst) {}

    fn enter_block(&mut self, _block_id: BlockId, _schedule: &[InstId]) {}

    fn passed(&mut self, _inst_id: InstId, _inst: &MachInst) {}
}

/// Register width the Layer B and C matchers accept for a class.
fn gpr_width(class: RegClass) -> Option<u32> {
    match class {
        RegClass::Gpr32 => Some(32),
        RegClass::Gpr64 => Some(64),
        _ => None,
    }
}

/// The part of an instruction that [`CegisSuperoptPass::materialized_wide_const_before`]
/// reads: the vreg ids it defines, and its opcode and operands if it is a
/// move-wide.
type MaterializerView<'a> = (Vec<u32>, Option<(AArch64Opcode, &'a [MachOperand])>);

fn materializer_view(inst: &MachInst) -> MaterializerView<'_> {
    let move_wide = matches!(
        inst.opcode,
        AArch64Opcode::Movz | AArch64Opcode::Movn | AArch64Opcode::Movk
    )
    .then_some((inst.opcode, inst.operands.as_slice()));
    (defined_ids(inst), move_wide)
}

/// The distinct vreg ids `inst` defines, in ascending order.
fn defined_ids(inst: &MachInst) -> Vec<u32> {
    let mut ids = Vec::new();
    for_each_vreg_def(inst, |vreg| ids.push(vreg.id));
    ids.sort_unstable();
    ids.dedup();
    ids
}

/// Where the materializer scan stands for one vreg of the current block.
/// A vreg without an entry holds no known constant.
#[derive(Debug, Clone)]
enum MaterializerChain {
    /// A `Movz` or `Movn` and the `Movk`s after it built `value`, already
    /// masked to the register width.
    Built { value: u64, ids: Vec<InstId> },
    /// The scan met a move-wide it cannot model and answers `None` for this
    /// vreg for the rest of the block.
    Refused,
}

/// Walk facts kept current in amortized constant time per instruction.
///
/// Use counts cover the whole arena and follow each body a walk replaces.
/// Materializer chains cover the block being walked: for each GPR vreg, the
/// state [`CegisSuperoptPass::materialized_wide_const_before`] reaches after
/// scanning the instructions passed so far. A walk rewrites only the
/// instruction it is at, before passing it, so a passed body changes only
/// where a schedule repeats an instruction id. The direct scan stops at an
/// id's first occurrence, so a later occurrence reuses the answer recorded
/// there. If a walk changes a passed body in a way the scan would see, the
/// rest of the block falls back to [`DirectWalkFacts`]; Layer C's only rewrite
/// (`AndRR` to `AndRI`, same operand 0) never does. The pass itself never
/// searches a schedule that repeats an id (`schedule_repeats_an_instruction`);
/// the facts still handle one, so the walk tests can hold them to the direct
/// scans on any layout.
struct IndexedWalkFacts {
    uses: HashMap<u32, u64>,
    block: Option<BlockId>,
    chains: HashMap<VReg, MaterializerChain>,
    /// Instruction ids the current block schedules more than once.
    repeated: HashSet<InstId>,
    passed_repeated: HashSet<InstId>,
    first_occurrence_answers: HashMap<(InstId, VReg), Option<MaterializedConst>>,
    /// A passed body changed in a way the scan would see.
    stale: bool,
    /// Queries answered by a direct scan; the tests require none outside the
    /// fallback cases above.
    #[cfg(test)]
    direct_fallbacks: usize,
}

impl IndexedWalkFacts {
    fn for_search(func: &MachFunction) -> Self {
        let mut facts = Self {
            uses: HashMap::new(),
            block: None,
            chains: HashMap::new(),
            repeated: HashSet::new(),
            passed_repeated: HashSet::new(),
            first_occurrence_answers: HashMap::new(),
            stale: false,
            #[cfg(test)]
            direct_fallbacks: 0,
        };
        for inst in &func.insts {
            facts.count_reads(inst);
        }
        facts
    }

    fn count_reads(&mut self, inst: &MachInst) {
        for_each_vreg_read(inst, |vreg| *self.uses.entry(vreg.id).or_insert(0) += 1);
    }

    fn uncount_reads(&mut self, inst: &MachInst) {
        for_each_vreg_read(inst, |vreg| {
            let count = self.uses.entry(vreg.id).or_insert(0);
            debug_assert!(*count > 0, "replaced body was not counted");
            *count = count.saturating_sub(1);
        });
    }

    fn direct_scan(
        &mut self,
        func: &MachFunction,
        block_id: BlockId,
        target_id: InstId,
        target: VReg,
        width: u32,
    ) -> Option<MaterializedConst> {
        #[cfg(test)]
        {
            self.direct_fallbacks += 1;
        }
        DirectWalkFacts.materialized_wide_const_before(func, block_id, target_id, target, width)
    }

    /// Apply one scan step of [`CegisSuperoptPass::materialized_wide_const_before`]
    /// for every GPR vreg the instruction defines.
    fn step_chain(&mut self, inst_id: InstId, inst: &MachInst) {
        let exact = inst.operands.first().and_then(MachOperand::as_vreg);
        for id in defined_ids(inst) {
            // The matchers ask only about Gpr32/Gpr64 targets, and a target's
            // class fixes the width its scan uses. A write to the id under
            // any class is a definition of each of them.
            for class in [RegClass::Gpr32, RegClass::Gpr64] {
                let target = VReg::new(id, class);
                if matches!(self.chains.get(&target), Some(MaterializerChain::Refused)) {
                    continue;
                }
                let next = if exact == Some(target) {
                    self.move_wide_step(inst_id, inst, target)
                } else {
                    None
                };
                match next {
                    Some(chain) => {
                        self.chains.insert(target, chain);
                    }
                    None => {
                        self.chains.remove(&target);
                    }
                }
            }
        }
    }

    /// The chain state after `inst`, a definition of `target` at operand 0,
    /// or `None` when `inst` is not a move-wide and forgets the constant.
    fn move_wide_step(
        &mut self,
        inst_id: InstId,
        inst: &MachInst,
        target: VReg,
    ) -> Option<MaterializerChain> {
        let width = gpr_width(target.class)?;
        let register_mask = mask_u64(width);
        let imm = CegisSuperoptPass::move_wide_imm16(inst);
        let shift = CegisSuperoptPass::move_wide_shift(inst, width);
        Some(match inst.opcode {
            AArch64Opcode::Movz | AArch64Opcode::Movn => match (imm, shift) {
                (Some(imm), Some(shift)) => {
                    let field = imm << shift;
                    let value = if inst.opcode == AArch64Opcode::Movz {
                        field
                    } else {
                        !field
                    };
                    MaterializerChain::Built {
                        value: value & register_mask,
                        ids: vec![inst_id],
                    }
                }
                _ => MaterializerChain::Refused,
            },
            AArch64Opcode::Movk => match (imm, shift, self.chains.remove(&target)) {
                (Some(imm), Some(shift), Some(MaterializerChain::Built { value, mut ids })) => {
                    let field_mask = 0xFFFFu64 << shift;
                    ids.push(inst_id);
                    MaterializerChain::Built {
                        value: ((value & !field_mask) | (imm << shift)) & register_mask,
                        ids,
                    }
                }
                _ => MaterializerChain::Refused,
            },
            _ => return None,
        })
    }
}

impl WalkFacts for IndexedWalkFacts {
    fn vreg_uses(&self, _func: &MachFunction, vreg: VReg) -> u64 {
        self.uses.get(&vreg.id).copied().unwrap_or(0)
    }

    fn materialized_wide_const_before(
        &mut self,
        func: &MachFunction,
        block_id: BlockId,
        target_id: InstId,
        target: VReg,
        width: u32,
    ) -> Option<MaterializedConst> {
        if self.stale || self.block != Some(block_id) || gpr_width(target.class) != Some(width) {
            return self.direct_scan(func, block_id, target_id, target, width);
        }
        if self.passed_repeated.contains(&target_id) {
            return match self.first_occurrence_answers.get(&(target_id, target)) {
                Some(answer) => answer.clone(),
                None => self.direct_scan(func, block_id, target_id, target, width),
            };
        }
        let answer = match self.chains.get(&target) {
            Some(MaterializerChain::Built { value, ids }) => Some((*value, ids.clone())),
            Some(MaterializerChain::Refused) | None => None,
        };
        if self.repeated.contains(&target_id) {
            self.first_occurrence_answers
                .insert((target_id, target), answer.clone());
        }
        answer
    }

    fn replaced(&mut self, inst_id: InstId, old: &MachInst, new: &MachInst) {
        self.uncount_reads(old);
        self.count_reads(new);
        if self.passed_repeated.contains(&inst_id)
            && materializer_view(old) != materializer_view(new)
        {
            self.stale = true;
        }
    }

    fn enter_block(&mut self, block_id: BlockId, schedule: &[InstId]) {
        self.block = Some(block_id);
        self.stale = false;
        self.chains.clear();
        self.repeated.clear();
        self.passed_repeated.clear();
        self.first_occurrence_answers.clear();
        let mut scheduled = HashSet::with_capacity(schedule.len());
        for &id in schedule {
            if !scheduled.insert(id) {
                self.repeated.insert(id);
            }
        }
    }

    fn passed(&mut self, inst_id: InstId, inst: &MachInst) {
        if self.repeated.contains(&inst_id) {
            self.passed_repeated.insert(inst_id);
        }
        self.step_chain(inst_id, inst);
    }
}

// ---------------------------------------------------------------------------
// The pass
// ---------------------------------------------------------------------------

/// CEGIS-driven superoptimization pass.
///
/// This is a thin wrapper around [`crate::CegisLoop`] that threads a
/// per-function solver budget and a shared compilation cache. On a cache hit
/// it skips all solver work. On a miss it walks the function instructions and
/// invokes `CegisLoop::verify` for each candidate rewrite site (if any),
/// failing closed when a candidate needs a verification after the budget has
/// elapsed (see `SolverBudget`).
///
/// The first payload layer rewrites `MulRR x, (Movz #0)` to `Movz #0` when the
/// verifier proves equivalence and the replacement is strictly cheaper.
pub struct CegisSuperoptPass {
    config: CegisSuperoptConfig,
    stats: CegisPassStats,
    test_hooks: CegisSuperoptTestHooks,
    failed_proof_counterexamples: FailedProofCounterexampleCorpus,
    failed_proof_counterexample_scope: Option<(SourceRegionIdentity, TargetAbiLayoutIdentity)>,
    // Deterministic adversarial control used only by transaction tests. It is
    // private and separately keyed so it cannot carry production authority.
    test_incomplete_after_first_commit: bool,
    /// Per-candidate verdicts and an event log for the walk-equivalence tests.
    #[cfg(test)]
    test_walk_script: Option<WalkScript>,
}

/// Deterministic per-candidate verdicts for unit tests, with a log of every
/// matched candidate and verdict in walk order.
#[cfg(test)]
struct WalkScript {
    verdict: Box<dyn FnMut(RewriteLayer, InstId) -> CegisResult + Send>,
    events: Vec<String>,
}

impl CegisSuperoptPass {
    /// Create a new pass with the given configuration.
    pub fn new(config: CegisSuperoptConfig) -> Self {
        Self {
            config,
            stats: CegisPassStats::default(),
            test_hooks: CegisSuperoptTestHooks::default(),
            failed_proof_counterexamples: FailedProofCounterexampleCorpus::empty(),
            failed_proof_counterexample_scope: None,
            test_incomplete_after_first_commit: false,
            #[cfg(test)]
            test_walk_script: None,
        }
    }

    /// Install fuel-only failed-proof counterexamples without enabling
    /// consumption.
    ///
    /// Seeds are ignored until
    /// [`Self::with_failed_proof_counterexamples_for_scope`] supplies an exact
    /// source/target scope.
    pub fn with_failed_proof_counterexamples(
        mut self,
        corpus: FailedProofCounterexampleCorpus,
    ) -> Self {
        self.failed_proof_counterexamples = corpus;
        self
    }

    /// Install fuel-only failed-proof counterexamples for one exact
    /// source/target scope.
    ///
    /// Seeded runs bypass normal cache reads and writes so seed-influenced
    /// results never populate or replay under the ordinary function cache key.
    pub fn with_failed_proof_counterexamples_for_scope(
        mut self,
        corpus: FailedProofCounterexampleCorpus,
        source_region: SourceRegionIdentity,
        target: TargetAbiLayoutIdentity,
    ) -> Self {
        self.failed_proof_counterexamples = corpus;
        self.failed_proof_counterexample_scope = Some((source_region, target));
        self
    }

    /// Install deterministic test controls for payload failure-mode coverage.
    #[doc(hidden)]
    pub fn with_test_hooks(mut self, hooks: CegisSuperoptTestHooks) -> Self {
        self.test_hooks = hooks;
        self
    }

    /// Force the first proven mutation to terminate as an incomplete query.
    ///
    /// This exists only for deterministic adversarial transaction tests. Its
    /// cache identity is disjoint from production and all other hook states.
    #[doc(hidden)]
    pub fn with_test_incomplete_after_first_commit(mut self) -> Self {
        self.test_incomplete_after_first_commit = true;
        self
    }

    /// Return the collected statistics.
    pub fn stats(&self) -> &CegisPassStats {
        &self.stats
    }

    /// Compute the deterministic per-function cache key.
    ///
    /// Hashes:
    /// - CEGIS key/search/payload schema identity
    /// - wall-clock/query budgets and effective outer-executor schedule
    /// - function name (framed)
    /// - number of instructions (framed)
    /// - each instruction's opcode Debug repr + operand count
    /// - block layout (entry + block_order + each live block's instruction ids)
    /// - opt_level, target_triple, cpu, features
    ///
    /// The resulting key is the same structure used by
    /// [`trust_cg_opt::CacheKey`] so callers can share a single on-disk cache
    /// between whole-module and per-function entries.
    pub fn compute_function_key(&self, func: &MachFunction) -> CacheKey {
        let mut h = StableHasher::new();
        h.write_str("trust-cg.verify.aarch64-cegis-function-cache");
        h.write_str(env!("CARGO_PKG_VERSION"));
        h.write_u32(CEGIS_SEARCH_SEMANTICS_REVISION);
        h.write_u32(CEGIS_SEARCH_SCHEDULE_VERSION);
        h.write_u32(CegisCacheEntry::VERSION);
        h.write_u64(self.config.budget_sec);
        h.write_u64(self.config.per_query_ms);
        h.write_u32(self.config.search_schedule.effective_parallelism());
        // `with_test_hooks` is public so integration tests can exercise the
        // cache protocol.  A forced `Equivalent` result must never publish
        // under the production key, where a later compiler could replay it as
        // real proof authority.  Keep active hooks in a disjoint, exact
        // namespace so two different synthetic outcomes cannot alias either.
        self.test_hooks.write_cache_identity(&mut h);
        // Preserve the production key when this test-only control is absent;
        // active controls still receive a disjoint namespace.
        if self.test_incomplete_after_first_commit {
            h.write_str("test:incomplete-after-first-commit");
        }
        h.write_str(&func.name);
        h.write_u64(func.insts.len() as u64);
        for inst in &func.insts {
            // Debug repr of the opcode enum is stable within a compiler
            // version. This matches what the cache key version field gates.
            let op = format!("{:?}", inst.opcode);
            h.write_str(&op);
            h.write_u64(inst.operands.len() as u64);
            for operand in &inst.operands {
                // Using Debug is coarse but deterministic within a compiler
                // build. Fine-grained operand hashing is left for a future
                // key-version bump (see CACHE_KEY_VERSION in trust-cg-opt).
                let s = format!("{:?}", operand);
                h.write_str(&s);
            }
        }
        h.write_u64(func.blocks.len() as u64);
        h.write_u64(func.entry.0 as u64);
        h.write_u64(func.block_order.len() as u64);
        for b in &func.block_order {
            h.write_u64(b.0 as u64);
            let block = func.block(*b);
            h.write_u64(block.insts.len() as u64);
            for inst in &block.insts {
                h.write_u64(inst.0 as u64);
            }
        }
        let module_hash = h.finish128();
        CacheKey::new(
            module_hash,
            self.config.opt_level,
            self.config.target_triple.clone(),
            self.config.cpu.clone(),
            self.config.features.clone(),
        )
    }

    /// Match a Layer A candidate: `MulRR dst, src1, src2` whose `src2` is
    /// defined, according to `def_map`, by a shift-zero `Movz src2, #0`.
    ///
    /// Returns the register width, the `Movz`'s id (the rewrite keeps it) and
    /// the `Movz dst, #0` that replaces the `MulRR`.
    fn match_layer_a_candidate(
        func: &MachFunction,
        inst: &MachInst,
        def_map: &HashMap<u32, trust_cg_ir::InstId>,
    ) -> Option<(u32, InstId, MachInst)> {
        if inst.opcode != AArch64Opcode::MulRR || inst.operands.len() < 3 {
            return None;
        }

        let dst = inst.operands.first()?.as_vreg()?;
        let src1 = inst.operands.get(1)?.as_vreg()?;
        let src2 = inst.operands.get(2)?.as_vreg()?;
        let def_id = def_map.get(&src2.id)?;
        let def_inst = func.inst(*def_id);

        if def_inst.opcode != AArch64Opcode::Movz {
            return None;
        }
        if def_inst.operands.first()?.as_vreg()? != src2 {
            return None;
        }

        let width = if src1.class == RegClass::Gpr32 {
            32
        } else if src1.class == RegClass::Gpr64 {
            64
        } else {
            return None;
        };
        if Self::move_wide_shift(def_inst, width)? != 0 || Self::move_wide_imm16(def_inst)? != 0 {
            return None;
        }
        let mut replacement = MachInst::new(
            AArch64Opcode::Movz,
            vec![MachOperand::VReg(dst), MachOperand::Imm(0)],
        );
        replacement.proof = inst.proof;
        replacement.source_loc = inst.source_loc;

        Some((width, *def_id, replacement))
    }

    fn enumerate_and_verify_layer_a(
        &mut self,
        func: &mut MachFunction,
        facts: &mut impl WalkFacts,
        budget: &mut SolverBudget,
        failed_proof_scope: Option<(&SourceRegionIdentity, &TargetAbiLayoutIdentity)>,
    ) -> (bool, CegisCacheEntry, CegisSearchCompletion, bool) {
        let mut entry = CegisCacheEntry::search_in_progress();
        let mut committed = false;
        let mut completion = CegisSearchCompletion::Complete;
        let mut used_failed_proof_seed = false;

        if ProvenRuleDb::seed_layer_a().is_empty() {
            return (false, entry, completion, false);
        }

        let cost_model = AppleSiliconCostModel::new(CostModelGen::M1);
        let mut cegis = CegisLoop::new(1, self.config.per_query_ms);

        'blocks: for block_id in func.block_order.clone() {
            let inst_ids = func.block(block_id).insts.clone();
            let mut def_map = HashMap::new();

            for inst_id in inst_ids {
                let inst = func.inst(inst_id).clone();
                if let Some((_width, zero_id, mut replacement)) =
                    Self::match_layer_a_candidate(func, &inst, &def_map)
                {
                    self.test_hooks
                        .corrupt(&mut replacement, func.inst(zero_id).operands.first());
                    self.note_candidate(RewriteLayer::A, inst_id, &[], &replacement);
                    self.stats.candidates += 1;
                    self.stats.layer_a_candidates += 1;
                    entry.attempted += 1;

                    let src_cost = cost_model.latency(AArch64Opcode::MulRR) as i32;
                    let tgt_cost = if self.test_hooks.force_layer_a_equal_cost {
                        src_cost
                    } else {
                        cost_model.latency(AArch64Opcode::Movz) as i32
                    };
                    // The kept `Movz` runs before the `MulRR` it feeds and
                    // before the `Movz dst, #0` that replaces it.
                    let zero = func.inst(zero_id);
                    let obligation =
                        Self::layer_obligation(&[zero, &inst], &[zero, &replacement], &inst);
                    if tgt_cost >= src_cost || obligation.is_none() {
                        // Not cheaper, or no obligation to discharge: rejected
                        // without a verification.
                        self.stats.rejected += 1;
                        entry.rejected += 1;
                    } else if !budget.admit_verification() {
                        // Any earlier incompleteness already ended the walk, so
                        // the budget is why this candidate stays unverified.
                        completion = CegisSearchCompletion::DeadlineExceeded;
                        break 'blocks;
                    } else if let Some(obligation) = obligation {
                        let result = self.verify_obligation(
                            &mut cegis,
                            RewriteLayer::A,
                            inst_id,
                            &obligation,
                            failed_proof_scope,
                            &mut used_failed_proof_seed,
                        );

                        match result {
                            Ok(CegisResult::Equivalent {
                                proof_hash,
                                iterations,
                            }) => {
                                let replacement_blob = MachInstBlob::from_inst(&replacement);
                                facts.replaced(inst_id, &inst, &replacement);
                                *func.inst_mut(inst_id) = replacement;
                                entry.verified += 1;
                                self.stats.verified += 1;
                                self.stats.layer_a_committed += 1;
                                entry.proven_rewrites.push(ProvenRewrite {
                                    inst_index: inst_id.0,
                                    proof_hash,
                                    iterations: iterations as u32,
                                    window_len: 1,
                                    replacement: vec![replacement_blob],
                                    layer: RewriteLayer::A,
                                });
                                committed = true;
                                if self.test_incomplete_after_first_commit {
                                    completion.record(CegisSearchCompletion::QueryIncomplete);
                                }
                            }
                            Ok(CegisResult::NotEquivalent { .. }) => {
                                self.stats.rejected += 1;
                                entry.rejected += 1;
                            }
                            Ok(CegisResult::Timeout | CegisResult::MaxIterationsReached { .. }) => {
                                completion.record(CegisSearchCompletion::QueryIncomplete);
                                self.stats.timeouts += 1;
                                self.stats.rejected += 1;
                                entry.rejected += 1;
                            }
                            Ok(CegisResult::Error(message)) => {
                                completion.record(CegisSearchCompletion::VerifierError);
                                if crate::diag::solve_trace_enabled() {
                                    eprintln!(
                                        "TCG_SOLVE_TRACE cegis_error layer=A message={message}"
                                    );
                                }
                                self.stats.verifier_errors += 1;
                                self.stats.rejected += 1;
                                entry.rejected += 1;
                            }
                            Err(_) => {
                                completion.record(CegisSearchCompletion::VerifierPanicked);
                                self.stats.panics += 1;
                                self.stats.rejected += 1;
                                entry.rejected += 1;
                            }
                        }
                    }
                }

                if !completion.is_complete() {
                    break 'blocks;
                }

                record_defs(&mut def_map, inst_id, func.inst(inst_id));
            }
        }

        if completion == CegisSearchCompletion::DeadlineExceeded {
            self.stats.budget_exhausted += 1;
        }
        self.stats.solver_calls += cegis.stats_solver_calls();

        (committed, entry, completion, used_failed_proof_seed)
    }

    /// Match a Layer B two-instruction window.
    ///
    /// Pattern:
    /// ```text
    /// Movz  v,   #imm          (earlier in same block, only use of v)
    /// AddRR dst, src, v        (current instruction)
    /// ```
    /// Replacement (single instruction):
    /// ```text
    /// AddRI dst, src, imm
    /// ```
    ///
    /// The matcher returns `(width, movz_inst_id, replacement)` on a
    /// successful match. `movz_inst_id` identifies the Movz to splice out of
    /// the block, and `replacement` is the new `AddRI` body that will
    /// overwrite the current `AddRR` instruction. The existing `AddRR`'s
    /// `InstId` (and therefore its destination `VReg`) is preserved; only the
    /// opcode and operand shape change. SSA is preserved because:
    ///
    /// 1. The `AddRR` keeps its original `dst` VReg — consumers of `dst`
    ///    elsewhere in the function are unaffected.
    /// 2. The `Movz`'s `dst` VReg becomes dead after the splice. The
    ///    matcher requires exactly one read of it (the current `AddRR`), so
    ///    no other consumer is left dangling.
    /// 3. The `AddRR`'s `src` operand is kept verbatim.
    ///
    /// Constraints enforced:
    /// - `Movz` must be a proof-covered shift-zero form (implicit or explicit)
    ///   and the latest definition of `v` before the `AddRR`, by every def
    ///   position of the shared operand-role model.
    /// - Its immediate must fit `ADD`'s unshifted 12-bit field, the only
    ///   `AddRI` form the encoder emits.
    /// - The Movz result VReg must be read exactly once in the function, at
    ///   every use position of the shared operand-role model (operand 0 of a
    ///   compare or store is a read).
    /// - The register class of AddRR's `dst`, `src`, and `v` must agree
    ///   (Gpr32 or Gpr64).
    fn match_layer_b_candidate(
        func: &MachFunction,
        add_inst: &MachInst,
        def_map: &HashMap<u32, trust_cg_ir::InstId>,
        facts: &impl WalkFacts,
    ) -> Option<(u32, trust_cg_ir::InstId, MachInst)> {
        if add_inst.opcode != AArch64Opcode::AddRR || add_inst.operands.len() < 3 {
            return None;
        }

        let dst = add_inst.operands.first()?.as_vreg()?;
        let src = add_inst.operands.get(1)?.as_vreg()?;
        let movz_vreg = add_inst.operands.get(2)?.as_vreg()?;

        if dst.class != src.class || dst.class != movz_vreg.class {
            return None;
        }
        let width = if dst.class == RegClass::Gpr32 {
            32
        } else if dst.class == RegClass::Gpr64 {
            64
        } else {
            return None;
        };

        let movz_id = *def_map.get(&movz_vreg.id)?;
        let movz_inst = func.inst(movz_id);

        if movz_inst.opcode != AArch64Opcode::Movz {
            return None;
        }
        if movz_inst.operands.first()?.as_vreg()? != movz_vreg {
            return None;
        }
        if Self::move_wide_shift(movz_inst, width)? != 0 {
            return None;
        }
        let imm = i64::try_from(Self::move_wide_imm16(movz_inst)?).ok()?;
        // `AddRI` is emitted as `ADD #imm12` with no shift.
        obligation::encode_add_imm(imm)?;

        // Single-use check: the `AddRR`'s operand 2 must be the only read of
        // the Movz destination anywhere, operand 0 of a compare or store
        // included, or splicing the Movz out leaves a read of nothing.
        if facts.vreg_uses(func, movz_vreg) != 1 {
            return None;
        }

        let mut replacement = MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::VReg(dst),
                MachOperand::VReg(src),
                MachOperand::Imm(imm),
            ],
        );
        replacement.proof = add_inst.proof;
        replacement.source_loc = add_inst.source_loc;

        Some((width, movz_id, replacement))
    }

    /// Enumerate Layer B candidates in `func` and commit rewrites that pass
    /// both the cost gate and CEGIS verification. Mirrors
    /// [`Self::enumerate_and_verify_layer_a`] but operates on two-instruction
    /// windows with SSA-preserving splice semantics.
    fn enumerate_and_verify_layer_b(
        &mut self,
        func: &mut MachFunction,
        facts: &mut impl WalkFacts,
        budget: &mut SolverBudget,
        entry: &mut CegisCacheEntry,
        failed_proof_scope: Option<(&SourceRegionIdentity, &TargetAbiLayoutIdentity)>,
    ) -> (bool, CegisSearchCompletion, bool) {
        let mut committed = false;
        let mut completion = CegisSearchCompletion::Complete;
        let mut used_failed_proof_seed = false;

        if ProvenRuleDb::seed_layer_b().is_empty() {
            return (false, completion, false);
        }

        let cost_model = AppleSiliconCostModel::new(CostModelGen::M1);
        let mut cegis = CegisLoop::new(1, self.config.per_query_ms);

        'blocks: for block_id in func.block_order.clone() {
            let inst_ids = func.block(block_id).insts.clone();
            let mut def_map: HashMap<u32, trust_cg_ir::InstId> = HashMap::new();
            let mut to_remove: Vec<trust_cg_ir::InstId> = Vec::new();

            for inst_id in inst_ids {
                let inst = func.inst(inst_id).clone();
                if let Some((_width, movz_id, mut replacement)) =
                    Self::match_layer_b_candidate(func, &inst, &def_map, facts)
                {
                    self.test_hooks
                        .corrupt(&mut replacement, func.inst(movz_id).operands.first());
                    self.note_candidate(RewriteLayer::B, inst_id, &[movz_id], &replacement);
                    self.stats.candidates += 1;
                    self.stats.layer_b_candidates += 1;
                    entry.attempted += 1;

                    // Cost gate: sum of source latencies strictly greater
                    // than replacement latency.
                    let src_cost = cost_model.latency(AArch64Opcode::Movz) as i32
                        + cost_model.latency(AArch64Opcode::AddRR) as i32;
                    let tgt_cost = if self.test_hooks.force_layer_b_equal_cost {
                        src_cost
                    } else {
                        cost_model.latency(AArch64Opcode::AddRI) as i32
                    };
                    let obligation = Self::layer_obligation(
                        &[func.inst(movz_id), &inst],
                        &[&replacement],
                        &inst,
                    );
                    if tgt_cost >= src_cost || obligation.is_none() {
                        // Not cheaper, or no obligation to discharge: rejected
                        // without a verification.
                        self.stats.rejected += 1;
                        entry.rejected += 1;
                    } else if !budget.admit_verification() {
                        completion = CegisSearchCompletion::DeadlineExceeded;
                        break 'blocks;
                    } else if let Some(obligation) = obligation {
                        let result = self.verify_obligation(
                            &mut cegis,
                            RewriteLayer::B,
                            inst_id,
                            &obligation,
                            failed_proof_scope,
                            &mut used_failed_proof_seed,
                        );

                        match result {
                            Ok(CegisResult::Equivalent {
                                proof_hash,
                                iterations,
                            }) => {
                                let replacement_blob = MachInstBlob::from_inst(&replacement);
                                facts.replaced(inst_id, &inst, &replacement);
                                *func.inst_mut(inst_id) = replacement;
                                to_remove.push(movz_id);
                                entry.verified += 1;
                                self.stats.verified += 1;
                                self.stats.layer_b_committed += 1;
                                entry.proven_rewrites.push(ProvenRewrite {
                                    inst_index: inst_id.0,
                                    proof_hash,
                                    iterations: iterations as u32,
                                    window_len: 2,
                                    replacement: vec![replacement_blob],
                                    layer: RewriteLayer::B,
                                });
                                committed = true;
                                if self.test_incomplete_after_first_commit {
                                    completion.record(CegisSearchCompletion::QueryIncomplete);
                                }
                            }
                            Ok(CegisResult::NotEquivalent { .. }) => {
                                self.stats.rejected += 1;
                                entry.rejected += 1;
                            }
                            Ok(CegisResult::Timeout | CegisResult::MaxIterationsReached { .. }) => {
                                completion.record(CegisSearchCompletion::QueryIncomplete);
                                self.stats.timeouts += 1;
                                self.stats.rejected += 1;
                                entry.rejected += 1;
                            }
                            Ok(CegisResult::Error(message)) => {
                                completion.record(CegisSearchCompletion::VerifierError);
                                if crate::diag::solve_trace_enabled() {
                                    eprintln!(
                                        "TCG_SOLVE_TRACE cegis_error layer=B message={message}"
                                    );
                                }
                                self.stats.verifier_errors += 1;
                                self.stats.rejected += 1;
                                entry.rejected += 1;
                            }
                            Err(_) => {
                                completion.record(CegisSearchCompletion::VerifierPanicked);
                                self.stats.panics += 1;
                                self.stats.rejected += 1;
                                entry.rejected += 1;
                            }
                        }
                    }
                }

                if !completion.is_complete() {
                    break 'blocks;
                }

                // Update def_map with the CURRENT body (possibly just
                // rewritten from AddRR to AddRI — both define `dst`).
                record_defs(&mut def_map, inst_id, func.inst(inst_id));
            }

            // Apply pending splices: drop spliced-out insts from the block
            // schedule. The arena entries remain (orphaned) but are no
            // longer scheduled; regalloc / codegen will not emit them.
            if !to_remove.is_empty() {
                let remove_set: std::collections::HashSet<_> = to_remove.into_iter().collect();
                func.block_mut(block_id)
                    .insts
                    .retain(|id| !remove_set.contains(id));
            }
        }

        if completion == CegisSearchCompletion::DeadlineExceeded {
            self.stats.budget_exhausted += 1;
        }
        self.stats.solver_calls += cegis.stats_solver_calls();

        (committed, completion, used_failed_proof_seed)
    }

    fn move_wide_shift(inst: &MachInst, width: u32) -> Option<u32> {
        let shift = match inst.opcode {
            AArch64Opcode::Movz | AArch64Opcode::Movn => match inst.operands.as_slice() {
                [_, _] => 0,
                [_, _, MachOperand::Imm(shift)] => *shift,
                _ => return None,
            },
            AArch64Opcode::Movk => match inst.operands.as_slice() {
                [_, _, MachOperand::Imm(shift)] => *shift,
                _ => return None,
            },
            _ => return None,
        };
        if shift < 0 || shift % 16 != 0 {
            return None;
        }
        let shift = shift as u32;
        if shift >= width
            || (matches!(inst.opcode, AArch64Opcode::Movz | AArch64Opcode::Movn) && shift != 0)
        {
            None
        } else {
            Some(shift)
        }
    }

    fn move_wide_imm16(inst: &MachInst) -> Option<u64> {
        let imm = inst.operands.get(1)?.as_imm()?;
        if !(0..=0xFFFF).contains(&imm) {
            return None;
        }
        Some(imm as u64)
    }

    /// The constant `target` holds just before `target_id` in `block_id`, and
    /// the move-wide instructions that built it, if a `Movz` or `Movn` of
    /// `target` followed by `Movk`s of `target` is its latest definition.
    ///
    /// The scan follows definitions by the shared operand-role model: any
    /// other write to `target`'s id, at any operand position and under any
    /// register class, forgets the constant; a read of `target` does not.
    /// A move-wide of `target` the scan cannot model, or a `Movk` with no
    /// known constant under it, makes the answer `None` for the rest of the
    /// block.
    fn materialized_wide_const_before(
        func: &MachFunction,
        block_id: trust_cg_ir::BlockId,
        target_id: InstId,
        target: VReg,
        width: u32,
    ) -> Option<(u64, Vec<InstId>)> {
        let mut value: Option<u64> = None;
        let mut materializer_ids = Vec::new();
        let register_mask = mask_u64(width);

        for &inst_id in &func.block(block_id).insts {
            if inst_id == target_id {
                break;
            }

            let inst = func.inst(inst_id);
            if !defines_vreg_id(inst, target.id) {
                continue;
            }
            let exact_move_wide =
                inst.operands.first().and_then(MachOperand::as_vreg) == Some(target);

            match inst.opcode {
                AArch64Opcode::Movz if exact_move_wide => {
                    let imm = Self::move_wide_imm16(inst)?;
                    let shift = Self::move_wide_shift(inst, width)?;
                    value = Some((imm << shift) & register_mask);
                    materializer_ids.clear();
                    materializer_ids.push(inst_id);
                }
                AArch64Opcode::Movn if exact_move_wide => {
                    let imm = Self::move_wide_imm16(inst)?;
                    let shift = Self::move_wide_shift(inst, width)?;
                    value = Some((!(imm << shift)) & register_mask);
                    materializer_ids.clear();
                    materializer_ids.push(inst_id);
                }
                AArch64Opcode::Movk if exact_move_wide => {
                    let imm = Self::move_wide_imm16(inst)?;
                    let shift = Self::move_wide_shift(inst, width)?;
                    let current = value?;
                    let field_mask = 0xFFFFu64 << shift;
                    value = Some(((current & !field_mask) | (imm << shift)) & register_mask);
                    materializer_ids.push(inst_id);
                }
                _ => {
                    value = None;
                    materializer_ids.clear();
                }
            }
        }

        let value = value? & register_mask;
        if materializer_ids.is_empty() {
            return None;
        }
        Some((value, materializer_ids))
    }

    /// Match a Layer C constant-mask fusion candidate.
    ///
    /// Pattern:
    /// ```text
    /// Movz/Movn/Movk* mask, #...
    /// AndRR dst, src, mask
    /// ```
    /// Replacement:
    /// ```text
    /// AndRI dst, src, #mask
    /// ```
    ///
    /// This targets the `revertBits.c` O2 shape from #844/#854, where every
    /// bit-swap stage materializes masks such as `0x55555555`,
    /// `0x33333333`, and `0x0f0f0f0f` before an `AndRR`. The replacement is
    /// admitted only when the materialized mask is a real AArch64 logical
    /// immediate and the `AndRR` is the only reader of the mask vreg outside
    /// the chain, so the materializer chain can be removed from the block
    /// schedule.
    fn match_layer_c_and_imm_candidate(
        func: &MachFunction,
        block_id: trust_cg_ir::BlockId,
        and_id: InstId,
        facts: &mut impl WalkFacts,
    ) -> Option<LayerCAndImmCandidate> {
        let and_inst = func.inst(and_id);
        if and_inst.opcode != AArch64Opcode::AndRR || and_inst.operands.len() < 3 {
            return None;
        }

        let dst = and_inst.operands.first()?.as_vreg()?;
        let src = and_inst.operands.get(1)?.as_vreg()?;
        let mask_vreg = and_inst.operands.get(2)?.as_vreg()?;
        if dst.class != src.class || dst.class != mask_vreg.class {
            return None;
        }

        let width = match dst.class {
            RegClass::Gpr32 => 32,
            RegClass::Gpr64 => 64,
            _ => return None,
        };

        let (mask, materializer_ids) =
            facts.materialized_wide_const_before(func, block_id, and_id, mask_vreg, width)?;
        obligation::encode_logical_imm(mask as i64, width)?;

        // The chain leaves the schedule with the rewrite, taking its own reads
        // of the mask (each `Movk` reads the halfwords it keeps) with it. The
        // `AndRR`'s mask operand must then be the only read left.
        let chain_reads: u64 = materializer_ids
            .iter()
            .map(|id| u64::from(vreg_reads_in(func.inst(*id), mask_vreg.id)))
            .sum();
        if facts.vreg_uses(func, mask_vreg) != chain_reads + 1 {
            return None;
        }

        let mut replacement = MachInst::new(
            AArch64Opcode::AndRI,
            vec![
                MachOperand::VReg(dst),
                MachOperand::VReg(src),
                MachOperand::Imm(mask as i64),
            ],
        );
        replacement.proof = and_inst.proof;
        replacement.source_loc = and_inst.source_loc;

        Some(LayerCAndImmCandidate {
            materializer_ids,
            replacement,
        })
    }

    fn enumerate_and_verify_layer_c(
        &mut self,
        func: &mut MachFunction,
        facts: &mut impl WalkFacts,
        budget: &mut SolverBudget,
        entry: &mut CegisCacheEntry,
        failed_proof_scope: Option<(&SourceRegionIdentity, &TargetAbiLayoutIdentity)>,
    ) -> (bool, CegisSearchCompletion, bool) {
        let mut committed = false;
        let mut completion = CegisSearchCompletion::Complete;
        let mut used_failed_proof_seed = false;

        if ProvenRuleDb::seed_layer_c().is_empty() {
            return (false, completion, false);
        }

        let cost_model = AppleSiliconCostModel::new(CostModelGen::M1);
        let mut cegis = CegisLoop::new(1, self.config.per_query_ms);

        'blocks: for block_id in func.block_order.clone() {
            let inst_ids = func.block(block_id).insts.clone();
            let mut to_remove: Vec<InstId> = Vec::new();
            // The matcher asks for the constant a mask vreg holds before each
            // `AndRR`; the facts follow the walk so that answer is not a scan
            // of the block prefix. Spliced materializers leave the schedule
            // only after the block, as the facts require.
            facts.enter_block(block_id, &inst_ids);

            for inst_id in inst_ids {
                'candidate: {
                    let Some(mut candidate) =
                        Self::match_layer_c_and_imm_candidate(func, block_id, inst_id, facts)
                    else {
                        break 'candidate;
                    };
                    let mask_register = func.inst(inst_id).operands.get(2);
                    self.test_hooks
                        .corrupt(&mut candidate.replacement, mask_register);

                    self.note_candidate(
                        RewriteLayer::C,
                        inst_id,
                        &candidate.materializer_ids,
                        &candidate.replacement,
                    );
                    self.stats.candidates += 1;
                    entry.attempted += 1;

                    let source_materializer_cost: i32 = candidate
                        .materializer_ids
                        .iter()
                        .map(|id| cost_model.latency(func.inst(*id).opcode) as i32)
                        .sum();
                    let src_cost =
                        source_materializer_cost + cost_model.latency(AArch64Opcode::AndRR) as i32;
                    let tgt_cost = cost_model.latency(AArch64Opcode::AndRI) as i32;
                    // The chain in schedule order, then the `AndRR` it feeds.
                    let and_inst = func.inst(inst_id);
                    let mut original: Vec<&MachInst> = candidate
                        .materializer_ids
                        .iter()
                        .map(|id| func.inst(*id))
                        .collect();
                    original.push(and_inst);
                    let obligation =
                        Self::layer_obligation(&original, &[&candidate.replacement], and_inst);
                    let Some(obligation) = obligation.filter(|_| tgt_cost < src_cost) else {
                        // Not cheaper, or no obligation to discharge: rejected
                        // without a verification.
                        self.stats.rejected += 1;
                        entry.rejected += 1;
                        break 'candidate;
                    };
                    if !budget.admit_verification() {
                        completion = CegisSearchCompletion::DeadlineExceeded;
                        break 'blocks;
                    }

                    let result = self.verify_obligation(
                        &mut cegis,
                        RewriteLayer::C,
                        inst_id,
                        &obligation,
                        failed_proof_scope,
                        &mut used_failed_proof_seed,
                    );

                    match result {
                        Ok(CegisResult::Equivalent {
                            proof_hash,
                            iterations,
                        }) => {
                            let replacement_blob = MachInstBlob::from_inst(&candidate.replacement);
                            let source =
                                std::mem::replace(func.inst_mut(inst_id), candidate.replacement);
                            facts.replaced(inst_id, &source, func.inst(inst_id));
                            to_remove.extend(candidate.materializer_ids.iter().copied());
                            entry.verified += 1;
                            self.stats.verified += 1;
                            entry.proven_rewrites.push(ProvenRewrite {
                                inst_index: inst_id.0,
                                proof_hash,
                                iterations: iterations as u32,
                                window_len: 1 + candidate.materializer_ids.len() as u32,
                                replacement: vec![replacement_blob],
                                layer: RewriteLayer::C,
                            });
                            committed = true;
                            if self.test_incomplete_after_first_commit {
                                completion.record(CegisSearchCompletion::QueryIncomplete);
                            }
                        }
                        Ok(CegisResult::NotEquivalent { .. }) => {
                            self.stats.rejected += 1;
                            entry.rejected += 1;
                        }
                        Ok(CegisResult::Timeout | CegisResult::MaxIterationsReached { .. }) => {
                            completion.record(CegisSearchCompletion::QueryIncomplete);
                            self.stats.timeouts += 1;
                            self.stats.rejected += 1;
                            entry.rejected += 1;
                        }
                        Ok(CegisResult::Error(message)) => {
                            completion.record(CegisSearchCompletion::VerifierError);
                            if crate::diag::solve_trace_enabled() {
                                eprintln!("TCG_SOLVE_TRACE cegis_error layer=C message={message}");
                            }
                            self.stats.verifier_errors += 1;
                            self.stats.rejected += 1;
                            entry.rejected += 1;
                        }
                        Err(_) => {
                            completion.record(CegisSearchCompletion::VerifierPanicked);
                            self.stats.panics += 1;
                            self.stats.rejected += 1;
                            entry.rejected += 1;
                        }
                    }
                }

                if !completion.is_complete() {
                    break 'blocks;
                }
                facts.passed(inst_id, func.inst(inst_id));
            }

            if !to_remove.is_empty() {
                let remove_set: std::collections::HashSet<_> = to_remove.into_iter().collect();
                func.block_mut(block_id)
                    .insts
                    .retain(|id| !remove_set.contains(id));
            }
        }

        if completion == CegisSearchCompletion::DeadlineExceeded {
            self.stats.budget_exhausted += 1;
        }
        self.stats.solver_calls += cegis.stats_solver_calls();

        (committed, completion, used_failed_proof_seed)
    }

    /// Apply a single cached rewrite to `func` from the serialized replacement
    /// body recorded in [`ProvenRewrite`].
    ///
    /// The cache has no MAC: anyone who can write its root can change a
    /// recorded body, and the codec checks only the format. Replay therefore
    /// re-runs the search's own matcher on the current body and applies the
    /// rewrite only where that matcher still admits the window, with the
    /// window length it implies, and rebuilds exactly the recorded body: the
    /// same opcode and the same operands, every register id and class and
    /// every immediate. Anything else leaves `func` untouched, and the caller
    /// treats the entry as stale and searches again. Replay thus splices out
    /// exactly the materializers the matcher would, under the same
    /// reaching-definition and single-read rules, and writes only a body the
    /// matcher builds. Cache blobs can also outlive matcher hardening; an
    /// older entry must not, for example, normalize away a now-non-emittable
    /// shifted `Movz`.
    ///
    /// What replay does not repeat is the equivalence proof: a replayed body
    /// is the matcher's own candidate, which the search admits only after the
    /// solver proves it.
    ///
    /// Returns `true` if the rewrite was applied. Bad indices, recorded bodies
    /// other than the matcher's, and windows the matcher no longer admits are
    /// treated as unapplied rewrites rather than hard pass failures.
    fn apply_cached_rewrite(func: &mut MachFunction, rewrite: &ProvenRewrite) -> bool {
        let target_id = trust_cg_ir::InstId(rewrite.inst_index);
        if (target_id.0 as usize) >= func.insts.len() {
            return false;
        }
        let [recorded] = rewrite.replacement.as_slice() else {
            return false;
        };
        let Some(block_id) = func
            .block_order
            .iter()
            .copied()
            .find(|b| func.block(*b).insts.contains(&target_id))
        else {
            return false;
        };

        let target = func.inst(target_id);
        let matched = match rewrite.layer {
            RewriteLayer::A => {
                let def_map = block_prefix_defs(func, block_id, target_id);
                Self::match_layer_a_candidate(func, target, &def_map)
                    .map(|(_, _, replacement)| (Vec::new(), replacement))
            }
            RewriteLayer::B => {
                let def_map = block_prefix_defs(func, block_id, target_id);
                Self::match_layer_b_candidate(func, target, &def_map, &DirectWalkFacts)
                    .map(|(_, movz_id, replacement)| (vec![movz_id], replacement))
            }
            RewriteLayer::C => Self::match_layer_c_and_imm_candidate(
                func,
                block_id,
                target_id,
                &mut DirectWalkFacts,
            )
            .map(|candidate| (candidate.materializer_ids, candidate.replacement)),
        };
        let Some((remove_ids, rebuilt)) = matched else {
            return false;
        };
        if rewrite.window_len as usize != 1 + remove_ids.len() {
            return false;
        }
        // Fail closed before any splice: the recorded body must be exactly
        // the one the matcher builds on the current body.
        if MachInstBlob::from_inst(&rebuilt) != *recorded {
            return false;
        }

        // The matchers copy `proof` and `source_loc` from the rewritten
        // instruction, which the recorded blob does not carry.
        *func.inst_mut(target_id) = rebuilt;
        if !remove_ids.is_empty() {
            let remove_set: HashSet<_> = remove_ids.into_iter().collect();
            func.block_mut(block_id)
                .insts
                .retain(|id| !remove_set.contains(id));
        }
        true
    }

    fn add_failed_proof_counterexample_seeds(
        &self,
        cegis: &mut CegisLoop,
        failed_proof_scope: Option<(&SourceRegionIdentity, &TargetAbiLayoutIdentity)>,
        vars: &[(String, u32)],
    ) -> usize {
        let Some((source_region, target)) = failed_proof_scope else {
            return 0;
        };
        let variable_names = vars
            .iter()
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        let inputs = self.failed_proof_counterexamples.concrete_inputs_for_scope(
            source_region,
            target,
            &variable_names,
        );
        let count = inputs.len();
        for input in inputs {
            cegis.add_seed(input);
        }
        count
    }

    fn failed_proof_counterexample_scope_for_func(
        &self,
        func: &MachFunction,
    ) -> Option<(&SourceRegionIdentity, &TargetAbiLayoutIdentity)> {
        let (source_region, target) = self.failed_proof_counterexample_scope.as_ref()?;
        if self.failed_proof_counterexamples.is_empty()
            || source_region.function_symbol.as_deref() != Some(func.name.as_str())
            || !target_matches_config(target, &self.config)
        {
            return None;
        }
        Some((source_region, target))
    }

    /// Replay all cached rewrites in order. Returns
    /// `(committed, applied_a, applied_b, applied_other)` where the per-layer
    /// `applied_*` counters record how many rewrites actually mutated the
    /// function this run. Per-layer counts let the caller bump
    /// `layer_a_committed` and `layer_b_committed` separately on cache hits;
    /// newer families without dedicated public counters still contribute to
    /// the roll-up candidate/verified counters via `applied_other`.
    ///
    /// Layer A rewrites must be replayed before Layer B, because Layer B may
    /// reference instructions whose def/use graph depends on Layer A's
    /// rewrites having been applied first (same ordering the cold path uses).
    fn replay_cached_rewrites(
        func: &mut MachFunction,
        entry: &CegisCacheEntry,
    ) -> (bool, u64, u64, u64) {
        let mut applied_a: u64 = 0;
        let mut applied_b: u64 = 0;
        let mut applied_other: u64 = 0;
        let mut committed = false;

        // Sort rewrites: Layer A first, then Layer B, then Layer C. Within a layer,
        // preserve recorded order (which mirrors cold-path enumeration order).
        let mut layer_a: Vec<&ProvenRewrite> = Vec::new();
        let mut layer_b: Vec<&ProvenRewrite> = Vec::new();
        let mut layer_c: Vec<&ProvenRewrite> = Vec::new();
        for r in &entry.proven_rewrites {
            match r.layer {
                RewriteLayer::A => layer_a.push(r),
                RewriteLayer::B => layer_b.push(r),
                RewriteLayer::C => layer_c.push(r),
            }
        }

        for r in layer_a.into_iter() {
            if Self::apply_cached_rewrite(func, r) {
                applied_a += 1;
                committed = true;
            }
        }
        for r in layer_b.into_iter() {
            if Self::apply_cached_rewrite(func, r) {
                applied_b += 1;
                committed = true;
            }
        }
        for r in layer_c.into_iter() {
            if Self::apply_cached_rewrite(func, r) {
                applied_other += 1;
                committed = true;
            }
        }

        (committed, applied_a, applied_b, applied_other)
    }

    /// Walk Layers A, B and C over `search_func`, the transaction's private
    /// copy, under one [`SolverBudget`].
    ///
    /// Returns whether any layer rewrote `search_func`, the cache entry, the
    /// search completion and whether failed-proof seeds were used. `facts`
    /// must describe `search_func` as it is on entry.
    fn search_layers(
        &mut self,
        search_func: &mut MachFunction,
        facts: &mut impl WalkFacts,
        failed_proof_scope: Option<(&SourceRegionIdentity, &TargetAbiLayoutIdentity)>,
    ) -> (bool, CegisCacheEntry, CegisSearchCompletion, bool) {
        let mut budget = SolverBudget::new(self.config.budget_sec, &self.test_hooks);
        let (committed_a, mut entry, completion_a, used_seed_a) =
            self.enumerate_and_verify_layer_a(search_func, facts, &mut budget, failed_proof_scope);
        let mut completion = completion_a;
        let mut used_failed_proof_seed = used_seed_a;
        // Layer B runs after Layer A so that any Layer-A-rewrites are
        // visible to the window enumerator (e.g. a MulRR->Movz collapse
        // could unblock a subsequent two-inst fusion).
        let (committed_b, completion_b, used_seed_b) = if !completion_a.is_complete() {
            (false, completion_a, false)
        } else {
            self.enumerate_and_verify_layer_b(
                search_func,
                facts,
                &mut budget,
                &mut entry,
                failed_proof_scope,
            )
        };
        completion.record(completion_b);
        used_failed_proof_seed |= used_seed_b;
        let (committed_c, completion_c, used_seed_c) = if !completion.is_complete() {
            (false, completion, false)
        } else {
            self.enumerate_and_verify_layer_c(
                search_func,
                facts,
                &mut budget,
                &mut entry,
                failed_proof_scope,
            )
        };
        completion.record(completion_c);
        used_failed_proof_seed |= used_seed_c;
        entry.completion = completion;
        (
            committed_a || committed_b || committed_c,
            entry,
            completion,
            used_failed_proof_seed,
        )
    }

    /// The obligation for a rewrite of `consumer`: its destination must hold
    /// the same value after `original` as after `replacement`.
    fn layer_obligation(
        original: &[&MachInst],
        replacement: &[&MachInst],
        consumer: &MachInst,
    ) -> Option<RewriteObligation> {
        let observed = consumer.operands.first()?.as_vreg()?;
        window_obligation(original, replacement, observed)
    }

    /// Discharge one admitted obligation with fresh counterexample state.
    ///
    /// Counterexamples from prior candidates are cleared so a counterexample
    /// to a different obligation cannot trigger a spurious `NotEquivalent`
    /// fast-path rejection here (#493); statistics accumulate across
    /// candidates (`clear_counterexamples`, not `reset`).
    fn verify_obligation(
        &mut self,
        cegis: &mut CegisLoop,
        layer: RewriteLayer,
        inst_id: InstId,
        obligation: &RewriteObligation,
        failed_proof_scope: Option<(&SourceRegionIdentity, &TargetAbiLayoutIdentity)>,
        used_failed_proof_seed: &mut bool,
    ) -> std::thread::Result<CegisResult> {
        cegis.clear_counterexamples();
        cegis.add_edge_case_seeds(&obligation.vars);
        if self.add_failed_proof_counterexample_seeds(cegis, failed_proof_scope, &obligation.vars)
            > 0
        {
            *used_failed_proof_seed = true;
        }
        self.run_verification(
            cegis,
            layer,
            inst_id,
            &obligation.source,
            &obligation.target,
            &obligation.vars,
        )
    }

    /// Run one admitted solver-backed verification of `src` against `tgt`.
    ///
    /// The elapsed time goes to `stats.solver_ms`: `CegisLoop::verify` does
    /// concrete evaluation and possibly several solver queries, and #486
    /// attributes everything that is not enumeration or mutation to the
    /// solver.
    fn run_verification(
        &mut self,
        cegis: &mut CegisLoop,
        layer: RewriteLayer,
        inst_id: InstId,
        src: &SmtExpr,
        tgt: &SmtExpr,
        vars: &[(String, u32)],
    ) -> std::thread::Result<CegisResult> {
        let solver_start = Instant::now();
        let result = if let Some(result) = self.scripted_verdict(layer, inst_id) {
            Ok(result)
        } else if let Some(result) = self.test_hooks.verifier_result.clone() {
            Ok(result)
        } else {
            catch_unwind(AssertUnwindSafe(|| cegis.verify(src, tgt, vars)))
        };
        self.stats.solver_ms = self
            .stats
            .solver_ms
            .saturating_add(solver_start.elapsed().as_millis() as u64);
        result
    }

    #[cfg(not(test))]
    #[inline]
    fn scripted_verdict(&mut self, _layer: RewriteLayer, _inst_id: InstId) -> Option<CegisResult> {
        None
    }

    #[cfg(test)]
    fn scripted_verdict(&mut self, layer: RewriteLayer, inst_id: InstId) -> Option<CegisResult> {
        let script = self.test_walk_script.as_mut()?;
        let result = (script.verdict)(layer, inst_id);
        script
            .events
            .push(format!("verdict {layer:?} {inst_id:?} {result:?}"));
        Some(result)
    }

    /// Record a matched candidate in the test walk script, if any.
    #[cfg(not(test))]
    #[inline]
    fn note_candidate(
        &mut self,
        _layer: RewriteLayer,
        _inst_id: InstId,
        _window: &[InstId],
        _replacement: &MachInst,
    ) {
    }

    #[cfg(test)]
    fn note_candidate(
        &mut self,
        layer: RewriteLayer,
        inst_id: InstId,
        window: &[InstId],
        replacement: &MachInst,
    ) {
        if let Some(script) = self.test_walk_script.as_mut() {
            script.events.push(format!(
                "candidate {layer:?} {inst_id:?} window={window:?} replacement={:?}",
                MachInstBlob::from_inst(replacement)
            ));
        }
    }

    /// Run one transactional CEGIS search and return its typed terminal state.
    ///
    /// Cache misses execute against a private clone. A deadline, query
    /// timeout, verifier error, or caught verifier panic drops that clone, so
    /// neither the legacy boolean API nor an artifact owner can observe a
    /// timing-dependent prefix of rewrites.
    pub fn run_with_outcome(&mut self, func: &mut MachFunction) -> CegisRunOutcome {
        if !self.config.is_enabled() {
            return CegisRunOutcome::Disabled;
        }
        self.stats.functions_seen += 1;

        // Wall-clock the entire pass body (cache lookup + replay OR
        // enumeration + CEGIS + cache put) so that #486's `total_wall_ms`
        // reflects the full cost observed by the pipeline. `solver_ms` is
        // accumulated independently inside enumerate_and_verify_layer_{a,b}
        // and represents a strict subset of `total_wall_ms`.
        let wall_start = Instant::now();

        // Snapshot pre-invocation counters so the trace event can report the
        // delta attributable to THIS call (rather than the running totals
        // across all functions the pass instance has seen).
        let candidates_before = self.stats.candidates;
        let verified_before = self.stats.verified;
        let rejected_before = self.stats.rejected;
        let layer_a_candidates_before = self.stats.layer_a_candidates;
        let layer_a_committed_before = self.stats.layer_a_committed;
        let layer_b_candidates_before = self.stats.layer_b_candidates;
        let layer_b_committed_before = self.stats.layer_b_committed;
        let timeouts_before = self.stats.timeouts;
        let verifier_errors_before = self.stats.verifier_errors;
        let panics_before = self.stats.panics;
        let solver_ms_before = self.stats.solver_ms;
        let solver_calls_before = self.stats.solver_calls;

        let key = self.compute_function_key(func);
        let failed_proof_scope_owned = self
            .failed_proof_counterexample_scope_for_func(func)
            .map(|(source_region, target)| (source_region.clone(), target.clone()));
        let failed_proof_scope = failed_proof_scope_owned
            .as_ref()
            .map(|(source_region, target)| (source_region, target));
        let cache_disabled_by_failed_proof_fuel = failed_proof_scope.is_some();

        // Cache hit / miss outcome for trace reporting.
        let mut from_cache = false;
        let mut committed = false;
        let mut invocation_completion = CegisSearchCompletion::Complete;
        let mut used_failed_proof_seed = false;

        // A schedule that lists an instruction id twice is left alone: no
        // cache lookup, no search and no put. An in-place rewrite of that id
        // would also change its other occurrence.
        let repeated_schedule = schedule_repeats_an_instruction(func);
        if repeated_schedule {
            self.stats.repeated_schedule_skips += 1;
        }

        // Cache hit path --------------------------------------------------
        let mut used_cache = false;
        if !repeated_schedule
            && !cache_disabled_by_failed_proof_fuel
            && let Some(backend) = self.config.cache.as_ref()
            && let Some(bytes) = backend.get(&key)
            && let Some(entry) = CegisCacheEntry::decode(&bytes)
        {
            let before_replay = func.clone();
            // Replay the cached rewrites so the function actually mutates.
            // Only bump `verified` / layer-committed by the number of
            // rewrites we actually applied this run (not `entry.verified`,
            // which would be a phantom count — see #491).
            let (c, applied_a, applied_b, applied_other) =
                Self::replay_cached_rewrites(func, &entry);
            let applied = applied_a + applied_b + applied_other;
            if applied == entry.proven_rewrites.len() as u64 {
                self.stats.cache_hits += 1;
                from_cache = true;
                used_cache = true;
                committed = c;
                self.stats.verified += applied;
                self.stats.candidates += applied;
                self.stats.layer_a_committed += applied_a;
                self.stats.layer_a_candidates += applied_a;
                self.stats.layer_b_committed += applied_b;
                self.stats.layer_b_candidates += applied_b;
                // `rejected` is a cold-path outcome (CEGIS said no / timeout /
                // error). Replay never "rejects" — it either applies or can't
                // find the site. We therefore do NOT re-credit `entry.rejected`
                // on a hit; the observability is about work done this run.
            } else {
                // A stale or tampered plan: some recorded rewrite is not one
                // the matchers admit and rebuild exactly on this body. Treat
                // it as a miss. Restore any partial replay before re-running
                // enumeration on the current function body; a complete search
                // then overwrites the entry.
                self.stats.cache_stale += 1;
                *func = before_replay;
            }
        }

        if !used_cache && !repeated_schedule {
            // Cache miss path ---------------------------------------------
            self.stats.cache_misses += 1;

            // Transaction boundary: all speculative rewrites stay private
            // until every layer has completed definitively. Cloning once on a
            // cache miss is small beside solver work and removes wall-clock
            // scheduling from the emitted artifact.
            let mut search_func = func.clone();
            let mut facts = IndexedWalkFacts::for_search(&search_func);
            let (speculative_committed, entry, completion, used_seed) =
                self.search_layers(&mut search_func, &mut facts, failed_proof_scope);
            used_failed_proof_seed |= used_seed;
            invocation_completion = completion;

            if completion.is_complete() {
                *func = search_func;
                committed = speculative_committed;

                // Persist only a COMPLETE search (which may legitimately have
                // an empty rewrite plan). Seeded failed-proof runs skip normal
                // cache writes because the key does not encode their corpus.
                if !cache_disabled_by_failed_proof_fuel
                    && !used_failed_proof_seed
                    && let Some(backend) = self.config.cache.as_ref()
                {
                    match entry.encode() {
                        Ok(bytes) => {
                            backend.put(&key, &bytes);
                            self.stats.cache_puts += 1;
                        }
                        Err(_) => {
                            // A codec failure costs reuse but cannot change the
                            // already-proven transaction.
                        }
                    }
                }
            } else {
                // The working copy is dropped unchanged. Keep proof-attempt
                // statistics, but do not count speculative layer mutations as
                // commits to the caller-visible function.
                committed = false;
                self.stats.layer_a_committed = layer_a_committed_before;
                self.stats.layer_b_committed = layer_b_committed_before;
            }
        }

        // Update wall-clock stats BEFORE emitting the trace event so that
        // the event's payload reflects final numbers for this invocation.
        let wall_ms = wall_start.elapsed().as_millis() as u64;
        self.stats.total_wall_ms = self.stats.total_wall_ms.saturating_add(wall_ms);

        // Emit a single structured trace event summarising this invocation
        // (issue #486 / #492 §10). The event name slot carries the full
        // stats payload encoded as `key=value` pairs so it round-trips
        // through `CompilationTrace::to_json` without needing new enum
        // variants. Downstream tooling can parse the payload with a trivial
        // regex; the goal is discoverability under `targo --unverified run -- --trace`
        // more than typed access.
        if let Some(trace) = self.config.trace.as_ref() {
            // Per-invocation deltas (since we only ever accumulate).
            let d_candidates = self.stats.candidates - candidates_before;
            let d_verified = self.stats.verified - verified_before;
            let d_rejected = self.stats.rejected - rejected_before;
            let d_layer_a_candidates = self.stats.layer_a_candidates - layer_a_candidates_before;
            let d_layer_a_committed = self.stats.layer_a_committed - layer_a_committed_before;
            let d_layer_b_candidates = self.stats.layer_b_candidates - layer_b_candidates_before;
            let d_layer_b_committed = self.stats.layer_b_committed - layer_b_committed_before;
            let d_timeouts = self.stats.timeouts - timeouts_before;
            let d_verifier_errors = self.stats.verifier_errors - verifier_errors_before;
            let d_panics = self.stats.panics - panics_before;
            let d_solver_ms = self.stats.solver_ms - solver_ms_before;
            let d_solver_calls = self.stats.solver_calls - solver_calls_before;

            let payload = format!(
                "CegisSuperoptPass{{func={func},cache={cache},wall_ms={wall_ms},solver_ms={solver_ms},candidates={candidates},verified={verified},rejected={rejected},layer_a_candidates={lac},layer_a_committed={laco},layer_b_candidates={lbc},layer_b_committed={lbco},timeouts={timeouts},verifier_errors={verr},panics={panics},solver_calls={calls},committed={committed}}}",
                func = func.name,
                cache = if from_cache { "hit" } else { "miss" },
                wall_ms = wall_ms,
                solver_ms = d_solver_ms,
                candidates = d_candidates,
                verified = d_verified,
                rejected = d_rejected,
                lac = d_layer_a_candidates,
                laco = d_layer_a_committed,
                lbc = d_layer_b_candidates,
                lbco = d_layer_b_committed,
                timeouts = d_timeouts,
                verr = d_verifier_errors,
                panics = d_panics,
                calls = d_solver_calls,
                committed = committed,
            );

            // Rule IDs: 486 (Applied) and 486 (Rejected) are stable
            // sentinel values tied to issue #486. They are intentionally
            // the same so post-processing can filter by "rule=486" and
            // then discriminate on EventKind (Applied vs Rejected).
            let (kind, justification) = if committed {
                (
                    EventKind::Applied {
                        rule: RuleId(486),
                        before: Vec::new(),
                        after: Vec::new(),
                    },
                    Justification::SolverProved {
                        proof_hash: d_verified,
                    },
                )
            } else {
                (
                    EventKind::Rejected {
                        rule: RuleId(486),
                        reason: if repeated_schedule {
                            "skipped: the schedule repeats an instruction id".to_string()
                        } else if from_cache {
                            "cache-hit: no rewrites replayed".to_string()
                        } else if !invocation_completion.is_complete() {
                            format!("incomplete CEGIS transaction: {invocation_completion:?}")
                        } else if d_candidates == 0 {
                            "no candidate sites matched".to_string()
                        } else {
                            "all candidates rejected by cost gate or CEGIS".to_string()
                        },
                    },
                    Justification::CostModel {
                        before: d_candidates as f64,
                        after: d_verified as f64,
                    },
                )
            };

            trace.emit(TracePassId::new(payload), kind, Vec::new(), justification);
        }

        if invocation_completion.is_complete() {
            CegisRunOutcome::Complete { committed }
        } else {
            CegisRunOutcome::Incomplete {
                completion: invocation_completion,
            }
        }
    }
}

impl MachinePass for CegisSuperoptPass {
    fn name(&self) -> &str {
        "CegisSuperoptPass"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        self.run_with_outcome(func).committed()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::failed_proof_reducer::{
        FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA,
        FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA_VERSION, FAILED_PROOF_REDUCER_PARENT_ISSUE,
        FailedProofCounterexampleCorpus, FailedProofCounterexampleSeed,
    };
    use crate::rewrite_admission::CounterexampleValue;
    use std::sync::Arc;
    use trust_cg_opt::{CacheBackend, CacheKey, InMemoryCache};

    #[test]
    fn exact_module_symbol_projection_preserves_binding() {
        let exact = MachOperand::ExactModuleSymbol("same_name".into());
        let ordinary = MachOperand::Symbol("same_name".into());
        let exact_blob = MachOperandBlob::from_operand(&exact);
        let ordinary_blob = MachOperandBlob::from_operand(&ordinary);
        assert_ne!(exact_blob, ordinary_blob);
        assert_eq!(exact_blob.to_operand(), exact);
        assert_eq!(ordinary_blob.to_operand(), ordinary);
    }

    // Build a minimally-valid MachFunction for tests via the public
    // constructor. We only need the name + insts + blocks + block_order
    // + entry fields for the pass to compute a cache key.
    fn empty_func(name: &str) -> MachFunction {
        use trust_cg_ir::function::Signature;
        MachFunction::new(name.to_string(), Signature::new(vec![], vec![]))
    }

    fn make_config(cache: Option<Arc<dyn CacheBackend>>, budget_sec: u64) -> CegisSuperoptConfig {
        CegisSuperoptConfig {
            budget_sec,
            per_query_ms: 1000,
            target_triple: "aarch64-apple-darwin".to_string(),
            cpu: "apple-m1".to_string(),
            features: vec!["neon".to_string(), "fp-armv8".to_string()],
            opt_level: 2,
            search_schedule: CegisSearchScheduleIdentity::serial(),
            cache,
            trace: None,
        }
    }

    fn failed_proof_scope_for_func(
        function_symbol: &str,
    ) -> (SourceRegionIdentity, TargetAbiLayoutIdentity) {
        let source_region = SourceRegionIdentity::new(
            "trust-cg-stable128:cegis-pass-fuel",
            "trust-cg-stable128-v1",
            "cegis_pass_test",
        )
        .with_kernel_name("cegis_pass_test")
        .with_function_symbol(function_symbol)
        .with_region_label("layer-a");
        let target = TargetAbiLayoutIdentity::aarch64(
            "aarch64-apple-darwin",
            "aapcs64",
            "e-m:o-i64:64-i128:128-n32:64-S128",
            "apple-m1",
            vec!["fp-armv8".to_string(), "neon".to_string()],
        );
        (source_region, target)
    }

    fn failed_proof_corpus_for_scope(
        source_region: &SourceRegionIdentity,
        target: &TargetAbiLayoutIdentity,
    ) -> FailedProofCounterexampleCorpus {
        FailedProofCounterexampleCorpus {
            schema: FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA.to_string(),
            schema_version: FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA_VERSION,
            parent_issue: FAILED_PROOF_REDUCER_PARENT_ISSUE,
            seeds: vec![FailedProofCounterexampleSeed {
                schema: FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA.to_string(),
                schema_version: FAILED_PROOF_COUNTEREXAMPLE_CORPUS_SCHEMA_VERSION,
                parent_issue: FAILED_PROOF_REDUCER_PARENT_ISSUE,
                seed_id: "trust-cg-failed-proof-cx-seed:test".to_string(),
                source_region: source_region.clone(),
                target: target.clone(),
                values: vec![CounterexampleValue {
                    name: "x".to_string(),
                    value: 7,
                }],
                found_by_concrete: true,
            }],
        }
    }

    fn v32(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }

    #[test]
    fn layer_b_rejects_nonzero_shift_movz() {
        let mut func = empty_func("shifted_layer_b");
        let block = func.entry;
        let movz = func.push_inst(MachInst::new(
            AArch64Opcode::Movz,
            vec![v32(1), MachOperand::Imm(1), MachOperand::Imm(16)],
        ));
        func.append_inst(block, movz);
        let add = MachInst::new(AArch64Opcode::AddRR, vec![v32(2), v32(0), v32(1)]);
        let def_map = HashMap::from([(1, movz)]);
        assert!(
            CegisSuperoptPass::match_layer_b_candidate(&func, &add, &def_map, &DirectWalkFacts)
                .is_none(),
            "an optimizer rewrite must not hide an encoder-invalid shifted Movz"
        );
    }

    #[test]
    fn move_wide_parser_accepts_explicit_zero_but_rejects_shifted_bases() {
        let movz_zero = MachInst::new(
            AArch64Opcode::Movz,
            vec![v32(0), MachOperand::Imm(7), MachOperand::Imm(0)],
        );
        assert_eq!(CegisSuperoptPass::move_wide_shift(&movz_zero, 32), Some(0));

        for opcode in [AArch64Opcode::Movz, AArch64Opcode::Movn] {
            let shifted = MachInst::new(
                opcode,
                vec![v32(0), MachOperand::Imm(0), MachOperand::Imm(16)],
            );
            assert_eq!(CegisSuperoptPass::move_wide_shift(&shifted, 32), None);
        }

        let malformed_extra = MachInst::new(
            AArch64Opcode::Movz,
            vec![
                v32(0),
                MachOperand::Imm(7),
                MachOperand::Imm(0),
                MachOperand::Imm(0),
            ],
        );
        assert_eq!(
            CegisSuperoptPass::move_wide_shift(&malformed_extra, 32),
            None
        );
    }

    #[test]
    fn test_config_disabled_default() {
        let cfg = CegisSuperoptConfig::default();
        assert!(!cfg.is_enabled());
        assert_eq!(cfg.budget_sec, 0);
    }

    #[test]
    fn test_disabled_pass_is_noop() {
        let mut pass = CegisSuperoptPass::new(CegisSuperoptConfig::default());
        let mut func = empty_func("noop");
        assert!(!pass.run(&mut func));
        assert_eq!(pass.stats().functions_seen, 0);
        assert_eq!(pass.stats().cache_hits, 0);
        assert_eq!(pass.stats().cache_misses, 0);
    }

    #[test]
    fn test_enabled_pass_records_miss_then_hit() {
        let cache: Arc<dyn CacheBackend> = Arc::new(InMemoryCache::new());
        let cfg = make_config(Some(cache.clone()), 1);

        // First run: cache miss, put.
        let mut pass = CegisSuperoptPass::new(cfg.clone());
        let mut func = empty_func("f");
        let _ = pass.run(&mut func);
        assert_eq!(pass.stats().functions_seen, 1);
        assert_eq!(pass.stats().cache_misses, 1);
        assert_eq!(pass.stats().cache_hits, 0);
        assert_eq!(pass.stats().cache_puts, 1);

        // Second run on an identical function: cache hit.
        let mut pass2 = CegisSuperoptPass::new(cfg);
        let mut func2 = empty_func("f");
        let _ = pass2.run(&mut func2);
        assert_eq!(pass2.stats().functions_seen, 1);
        assert_eq!(pass2.stats().cache_hits, 1);
        assert_eq!(pass2.stats().cache_misses, 0);
    }

    #[test]
    fn test_failed_proof_seeded_run_does_not_populate_normal_cache_key() {
        let cache: Arc<dyn CacheBackend> = Arc::new(InMemoryCache::new());
        let cfg = make_config(Some(cache.clone()), 1);
        let (source_region, target) = failed_proof_scope_for_func("seeded");
        let corpus = failed_proof_corpus_for_scope(&source_region, &target);

        let mut seeded_pass = CegisSuperoptPass::new(cfg.clone())
            .with_failed_proof_counterexamples_for_scope(
                corpus,
                source_region.clone(),
                target.clone(),
            );
        let mut seeded_func = empty_func("seeded");
        let _ = seeded_pass.run(&mut seeded_func);
        assert_eq!(seeded_pass.stats().functions_seen, 1);
        assert_eq!(seeded_pass.stats().cache_hits, 0);
        assert_eq!(seeded_pass.stats().cache_misses, 1);
        assert_eq!(
            seeded_pass.stats().cache_puts,
            0,
            "failed-proof fuel must not populate the normal function cache key"
        );

        let mut unseeded_pass = CegisSuperoptPass::new(cfg);
        let mut unseeded_func = empty_func("seeded");
        let _ = unseeded_pass.run(&mut unseeded_func);
        assert_eq!(unseeded_pass.stats().cache_hits, 0);
        assert_eq!(unseeded_pass.stats().cache_misses, 1);
    }

    #[test]
    fn test_key_is_deterministic_across_instances() {
        let cfg = make_config(None, 1);
        let p1 = CegisSuperoptPass::new(cfg.clone());
        let p2 = CegisSuperoptPass::new(cfg);
        let f1 = empty_func("same");
        let f2 = empty_func("same");
        let k1 = p1.compute_function_key(&f1);
        let k2 = p2.compute_function_key(&f2);
        assert_eq!(k1, k2);
    }

    #[test]
    fn test_key_differs_with_function_name() {
        let cfg = make_config(None, 1);
        let pass = CegisSuperoptPass::new(cfg);
        let f1 = empty_func("alpha");
        let f2 = empty_func("beta");
        assert_ne!(
            pass.compute_function_key(&f1),
            pass.compute_function_key(&f2)
        );
    }

    #[test]
    fn test_key_differs_with_features() {
        let mut cfg_a = make_config(None, 1);
        let mut cfg_b = make_config(None, 1);
        cfg_b.features.push("extra-feature".to_string());
        let pa = CegisSuperoptPass::new(cfg_a.clone());
        let pb = CegisSuperoptPass::new(cfg_b.clone());
        let f = empty_func("f");
        assert_ne!(pa.compute_function_key(&f), pb.compute_function_key(&f));
        // And feature order does NOT matter (sort+dedup inside CacheKey::new).
        cfg_a.features = vec!["b".to_string(), "a".to_string()];
        cfg_b.features = vec!["a".to_string(), "b".to_string()];
        let pa = CegisSuperoptPass::new(cfg_a);
        let pb = CegisSuperoptPass::new(cfg_b);
        assert_eq!(pa.compute_function_key(&f), pb.compute_function_key(&f));
    }

    #[test]
    fn test_key_separates_every_bounded_search_policy_input() {
        let func = empty_func("bounded-policy");
        let baseline = make_config(None, 1);
        let baseline_key = CegisSuperoptPass::new(baseline.clone()).compute_function_key(&func);

        let mut different_budget = baseline.clone();
        different_budget.budget_sec = 2;
        assert_ne!(
            baseline_key,
            CegisSuperoptPass::new(different_budget).compute_function_key(&func),
            "the per-function wall budget can change the discovered prefix"
        );

        let mut different_query_timeout = baseline.clone();
        different_query_timeout.per_query_ms += 1;
        assert_ne!(
            baseline_key,
            CegisSuperoptPass::new(different_query_timeout).compute_function_key(&func),
            "the per-query timeout can change whether a candidate completes"
        );

        let mut different_schedule = baseline;
        different_schedule.search_schedule =
            CegisSearchScheduleIdentity::with_effective_parallelism(4);
        assert_ne!(
            baseline_key,
            CegisSuperoptPass::new(different_schedule).compute_function_key(&func),
            "outer executor contention can change a wall-clock-bounded result"
        );

        assert_ne!(CEGIS_SEARCH_SEMANTICS_REVISION, 0);
        assert_ne!(CEGIS_SEARCH_SCHEDULE_VERSION, 0);
    }

    #[test]
    fn test_hooks_cannot_publish_under_a_production_cache_key() {
        let func = empty_func("test-hook-cache-authority");
        let config = make_config(None, 10);
        let production_key = CegisSuperoptPass::new(config.clone()).compute_function_key(&func);
        let hooked_key = CegisSuperoptPass::new(config)
            .with_test_hooks(CegisSuperoptTestHooks {
                verifier_result: Some(CegisResult::Equivalent {
                    proof_hash: 1,
                    iterations: 1,
                }),
                ..Default::default()
            })
            .compute_function_key(&func);

        assert_ne!(
            production_key, hooked_key,
            "a forced verifier result must not carry production cache authority"
        );
    }

    #[test]
    fn budget_test_controls_have_disjoint_cache_namespaces() {
        let func = empty_func("budget-control-cache-namespace");
        let config = make_config(None, 10);
        let key = |hooks: CegisSuperoptTestHooks| {
            CegisSuperoptPass::new(config.clone())
                .with_test_hooks(hooks)
                .compute_function_key(&func)
        };
        let keys = [
            CegisSuperoptPass::new(config.clone()).compute_function_key(&func),
            key(CegisSuperoptTestHooks {
                force_expired_deadline: true,
                ..Default::default()
            }),
            key(CegisSuperoptTestHooks {
                force_deadline_after_verifications: Some(0),
                ..Default::default()
            }),
            key(CegisSuperoptTestHooks {
                force_deadline_after_verifications: Some(1),
                ..Default::default()
            }),
        ];
        for (i, left) in keys.iter().enumerate() {
            for right in &keys[i + 1..] {
                assert_ne!(left, right, "budget controls must not share a key");
            }
        }
    }

    /// A corrupted-replacement control is never committed, but its cache
    /// entry must still never be served to production or to another control.
    #[test]
    fn replacement_mutation_controls_have_disjoint_cache_namespaces() {
        let func = empty_func("mutation-control-cache-namespace");
        let config = make_config(None, 10);
        let mut keys = vec![CegisSuperoptPass::new(config.clone()).compute_function_key(&func)];
        for mutation in [
            ReplacementMutation::Immediate,
            ReplacementMutation::SourceRegister,
            ReplacementMutation::Operation,
        ] {
            keys.push(
                CegisSuperoptPass::new(config.clone())
                    .with_test_hooks(CegisSuperoptTestHooks {
                        corrupt_replacement: Some(mutation),
                        ..Default::default()
                    })
                    .compute_function_key(&func),
            );
        }
        for (i, left) in keys.iter().enumerate() {
            for right in &keys[i + 1..] {
                assert_ne!(left, right, "mutation controls must not share a key");
            }
        }
    }

    #[test]
    fn solver_budget_clock_starts_at_the_first_verification() {
        let mut budget = SolverBudget::new(60, &CegisSuperoptTestHooks::default());
        assert!(
            budget.clock_started.is_none(),
            "matching candidates must not start the budget clock"
        );
        assert!(
            budget.admit_verification(),
            "the first verification always starts"
        );
        let started = budget
            .clock_started
            .expect("the first admission starts the clock");
        assert!(
            budget.admit_verification(),
            "a verification inside the budget starts"
        );

        // Move the clock start back by the whole budget instead of sleeping.
        budget.clock_started = Some(
            started
                .checked_sub(Duration::from_secs(60))
                .expect("the monotonic clock has a minute of history"),
        );
        assert!(
            !budget.admit_verification(),
            "no verification starts once the budget has elapsed"
        );
        assert_eq!(budget.admitted, 2);
    }

    #[test]
    fn solver_budget_test_controls_elapse_after_the_requested_admissions() {
        let mut expired = SolverBudget::new(
            10,
            &CegisSuperoptTestHooks {
                force_expired_deadline: true,
                ..Default::default()
            },
        );
        assert!(!expired.admit_verification());
        assert_eq!(expired.admitted, 0);

        let mut after_one = SolverBudget::new(
            10,
            &CegisSuperoptTestHooks {
                force_deadline_after_verifications: Some(1),
                ..Default::default()
            },
        );
        assert!(after_one.admit_verification());
        assert!(!after_one.admit_verification());
        assert_eq!(after_one.admitted, 1);
    }

    #[test]
    fn test_cache_entry_roundtrip() {
        let entry = CegisCacheEntry {
            version: CegisCacheEntry::VERSION,
            completion: CegisSearchCompletion::Complete,
            proven_rewrites: vec![ProvenRewrite {
                inst_index: 3,
                proof_hash: 0xDEAD_BEEF,
                iterations: 1,
                window_len: 1,
                replacement: vec![MachInstBlob::from_inst(&MachInst::new(
                    AArch64Opcode::Movz,
                    vec![
                        MachOperand::VReg(VReg::new(7, RegClass::Gpr32)),
                        MachOperand::Imm(0),
                    ],
                ))],
                layer: RewriteLayer::A,
            }],
            attempted: 10,
            verified: 1,
            rejected: 9,
        };
        let bytes = entry.encode().expect("encode");
        let decoded = CegisCacheEntry::decode(&bytes).expect("decode");
        assert_eq!(decoded, entry);
    }

    #[test]
    fn test_cache_entry_wrong_version_rejected() {
        let entry = CegisCacheEntry {
            version: 999,
            completion: CegisSearchCompletion::Complete,
            ..Default::default()
        };
        let bytes = entry.encode().expect("encode");
        assert!(CegisCacheEntry::decode(&bytes).is_none());
    }

    #[test]
    fn test_cache_entry_older_versions_rejected() {
        // v1-v3 entries predate the serialized replacement-body format.
        // v4 predates the #854 Layer C matcher; stale empty entries must not
        // suppress newly-covered bit-reverse mask candidates.
        // v5 predates the `cegis_cache_codec` wire format. v6 predates the
        // explicit completion outcome and could carry an ambiguous partial
        // prefix. Note this loop can
        // only exercise the *version field* gate, because the current encoder
        // is the only one available here; a genuine v5 MessagePack blob is
        // rejected on the magic instead, and that is covered by
        // `tests/cegis_cache_codec.rs::a_real_v5_messagepack_blob_is_a_miss`.
        for old_version in [1u32, 2u32, 3u32, 4u32, 5u32, 6u32] {
            let entry = CegisCacheEntry {
                version: old_version,
                completion: CegisSearchCompletion::Complete,
                ..Default::default()
            };
            let bytes = entry.encode().expect("encode");
            assert!(
                CegisCacheEntry::decode(&bytes).is_none(),
                "v{} cache entries must be rejected at the current VERSION",
                old_version,
            );
        }
    }

    #[test]
    fn test_pass_name() {
        let p = CegisSuperoptPass::new(CegisSuperoptConfig::default());
        assert_eq!(p.name(), "CegisSuperoptPass");
    }

    #[test]
    fn test_pass_without_cache_still_runs() {
        let cfg = make_config(None, 1);
        let mut pass = CegisSuperoptPass::new(cfg);
        let mut func = empty_func("nocache");
        let _ = pass.run(&mut func);
        assert_eq!(pass.stats().functions_seen, 1);
        assert_eq!(pass.stats().cache_misses, 1);
        assert_eq!(pass.stats().cache_puts, 0); // no backend
    }

    #[test]
    fn test_cache_key_round_trip_through_backend() {
        let cache = InMemoryCache::new();
        let key = CacheKey::new(
            0x12345678_ABCDEF00_u128,
            2,
            "aarch64-apple-darwin".to_string(),
            "apple-m1".to_string(),
            vec!["neon".to_string()],
        );
        let entry = CegisCacheEntry::empty();
        let bytes = entry.encode().unwrap();
        cache.put(&key, &bytes);
        let got = cache.get(&key).expect("hit");
        let decoded = CegisCacheEntry::decode(&got).expect("decode");
        assert_eq!(decoded, entry);
    }
}

#[cfg(test)]
#[path = "cegis_pass_walk_tests.rs"]
mod walk_tests;

#[cfg(test)]
#[path = "cegis_pass_operand_uses_tests.rs"]
mod operand_uses_tests;

#[cfg(test)]
#[path = "cegis_pass_replay_tests.rs"]
mod replay_tests;
