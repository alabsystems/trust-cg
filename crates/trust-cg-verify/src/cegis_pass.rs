// trust-cg-verify/cegis_pass.rs - CEGIS superopt pass wrapper
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Wraps the `CegisLoop` primitive as a `MachinePass` so callers can request
// CEGIS-based superoptimization from the optimization pipeline with a
// per-function wall-clock budget. Results (whether the candidate rewrite was
// proven equivalent or rejected) are keyed into the shared compilation cache
// under a per-function hash derived from (instructions + target triple + cpu
// + features). Repeat compilations reuse cached outcomes so that expensive
// CEGIS searches are paid for only once per input tuple.
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
//!    the stored rewrites (skip all solver work).
//! 3. On a miss: walk instructions, identify candidate rewrite sites, and
//!    call [`crate::CegisLoop::verify`] with a per-query timeout derived
//!    from `per_query_ms`. The total wall clock spent in this pass is
//!    capped by `budget_sec`.
//! 4. On successful equivalence proofs, record rewrites in
//!    [`CegisCacheEntry`], serialize via `rmp-serde`, and store under the
//!    function hash.
//!
//! The first payload layer recognizes one hand-seeded single-instruction
//! rewrite: `MulRR x, (Movz #0)` within a block can become `Movz #0` when the
//! replacement is strictly cheaper and CEGIS proves equivalence.

use std::collections::HashMap;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};
use trust_cg_ir::cost_model::{AppleSiliconCostModel, CostModel, CostModelGen};
use trust_cg_ir::provenance::PassId as TracePassId;
use trust_cg_ir::trace::{CompilationTrace, EventKind, Justification, RuleId};
use trust_cg_ir::{
    AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, PReg, RegClass, SpecialReg, VReg,
};
use trust_cg_opt::{CacheBackend, CacheKey, MachinePass, StableHasher};

use crate::cegis::{CegisLoop, CegisResult};
use crate::failed_proof_reducer::FailedProofCounterexampleCorpus;
use crate::rewrite_admission::{SourceRegionIdentity, TargetAbiLayoutIdentity};
use crate::smt::SmtExpr;
use crate::synthesis::ProvenRuleDb;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Count how many instructions in `func` read `target` as a VReg operand.
///
/// "Uses" are any operand after the first that match the VReg id. The
/// leading operand is treated as the definition (conventional for our
/// `MachInst` layout where `operands[0]` is the destination). This matches
/// the assumption used by the Layer A / Layer B matchers.
fn count_vreg_uses(func: &MachFunction, target: VReg) -> u32 {
    let mut uses: u32 = 0;
    for inst in &func.insts {
        // Skip the destination slot (operand 0) — that is a def, not a use.
        for operand in inst.operands.iter().skip(1) {
            if let Some(v) = operand.as_vreg()
                && v.id == target.id
            {
                uses = uses.saturating_add(1);
            }
        }
    }
    uses
}

/// Low-`width` bitmask for constant immediates fed into the SMT evaluator.
fn mask_u64(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

fn rotate_right_within(value: u64, rotation: u32, width: u32) -> u64 {
    let rotation = rotation % width;
    let mask = mask_u64(width);
    if rotation == 0 {
        value & mask
    } else {
        ((value >> rotation) | (value << (width - rotation))) & mask
    }
}

fn replicate_logical_element(pattern: u64, element_width: u32, register_width: u32) -> u64 {
    let mut out = 0;
    let mut shift = 0;
    while shift < register_width {
        out |= pattern << shift;
        shift += element_width;
    }
    out & mask_u64(register_width)
}

fn is_aarch64_logical_immediate(raw: u64, register_width: u32) -> bool {
    let register_mask = mask_u64(register_width);
    let raw = raw & register_mask;
    if raw == 0 || raw == register_mask {
        return false;
    }

    let element_widths: &[u32] = if register_width == 64 {
        &[2, 4, 8, 16, 32, 64]
    } else {
        &[2, 4, 8, 16, 32]
    };

    for &element_width in element_widths {
        for ones_len in 1..element_width {
            let ones = mask_u64(ones_len);
            for rotation in 0..element_width {
                let element = rotate_right_within(ones, rotation, element_width);
                let candidate = replicate_logical_element(element, element_width, register_width);
                if candidate == raw {
                    return true;
                }
            }
        }
    }

    false
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

/// Configuration for [`CegisSuperoptPass`].
///
/// The pass is effectively disabled when `budget_sec == 0`, which is the
/// default. The CLI flag `--cegis-superopt=<secs>` sets this field to a
/// non-zero value.
#[derive(Clone)]
pub struct CegisSuperoptConfig {
    /// Total per-function wall-clock budget in seconds. `0` disables the pass.
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

#[derive(Debug, Clone)]
struct LayerCAndImmCandidate {
    width: u32,
    materializer_ids: Vec<InstId>,
    replacement: MachInst,
    mask: u64,
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
            MachOperand::JumpTableIndex(index) => Self::JumpTableIndex(*index),
            MachOperand::IncomingArg(offset) => Self::IncomingArg(*offset),
        }
    }

    fn to_operand(&self) -> MachOperand {
        match self {
            Self::VReg { id, class } => MachOperand::VReg(VReg::new(*id, (*class).into())),
            Self::PReg { encoding } => MachOperand::PReg(PReg::new(*encoding)),
            Self::Imm(imm) => MachOperand::Imm(*imm),
            Self::FImmBits(bits) => MachOperand::FImm(f64::from_bits(*bits)),
            Self::Block(block) => MachOperand::Block(trust_cg_ir::BlockId(*block)),
            Self::StackSlot(slot) => MachOperand::StackSlot(trust_cg_ir::StackSlotId(*slot)),
            Self::FrameIndex(frame) => MachOperand::FrameIndex(trust_cg_ir::FrameIdx(*frame)),
            Self::MemOp {
                base_encoding,
                offset,
            } => MachOperand::MemOp {
                base: PReg::new(*base_encoding),
                offset: *offset,
            },
            Self::Special(reg) => MachOperand::Special((*reg).into()),
            Self::Symbol(symbol) => MachOperand::Symbol(symbol.clone()),
            Self::JumpTableIndex(index) => MachOperand::JumpTableIndex(*index),
            Self::IncomingArg(offset) => MachOperand::IncomingArg(*offset),
        }
    }
}

/// `rmp-serde` friendly projection of a replacement [`MachInst`].
///
/// The cache format stores opcode + operands only. On replay the first rebuilt
/// replacement instruction inherits `proof` and `source_loc` from the first
/// source instruction, matching the design's replay contract.
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

    fn to_inst(&self) -> Option<MachInst> {
        let opcode = Self::opcode_from_name(&self.opcode)?;
        let operands = self
            .operands
            .iter()
            .map(MachOperandBlob::to_operand)
            .collect();
        Some(MachInst::new(opcode, operands))
    }

    fn opcode_from_name(name: &str) -> Option<AArch64Opcode> {
        // Keep this list aligned with the opcodes emitted by CEGIS replacements.
        match name {
            "AddRI" => Some(AArch64Opcode::AddRI),
            "AndRI" => Some(AArch64Opcode::AndRI),
            "Movz" => Some(AArch64Opcode::Movz),
            _ => None,
        }
    }
}

/// A single CEGIS rewrite proof recorded in the cache.
///
/// `inst_index` is the flat [`MachFunction::insts`] index that was verified
/// equivalent to `replacement`. `window_len` records the source window consumed
/// by the rewrite. Cache hits replay the serialized replacement body directly,
/// so repeat compilations avoid both CEGIS and matcher reconstruction.
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
    /// Serialized replacement body applied on cache hits.
    pub replacement: Vec<MachInstBlob>,
    /// Which payload layer produced this rewrite (used for stats and splices).
    pub layer: RewriteLayer,
}

/// Serializable cache entry stored under the per-function cache key.
///
/// Encoded as MessagePack via `rmp-serde`. Format version is bumped whenever
/// fields are added; older cache entries are discarded by the consumer when
/// version changes (equivalent to a cache miss).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CegisCacheEntry {
    /// Format version. Bump when fields change.
    pub version: u32,
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
    ///
    /// Older entries are silently rejected as a miss; this is semantics-
    /// preserving because the pass simply re-runs enumeration on the next
    /// invocation.
    pub const VERSION: u32 = 5;

    /// Fresh empty entry with the current version.
    pub fn empty() -> Self {
        Self {
            version: Self::VERSION,
            ..Default::default()
        }
    }

    /// Encode to MessagePack bytes.
    pub fn encode(&self) -> Result<Vec<u8>, rmp_serde::encode::Error> {
        rmp_serde::to_vec(self)
    }

    /// Decode from MessagePack bytes. Returns `None` if the version mismatches
    /// (treated as a cache miss by callers).
    pub fn decode(bytes: &[u8]) -> Option<Self> {
        let entry: Self = rmp_serde::from_slice(bytes).ok()?;
        if entry.version != Self::VERSION {
            return None;
        }
        Some(entry)
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
    /// Number of candidate rewrite sites considered (all layers).
    pub candidates: u64,
    /// Number of candidate sites proven equivalent (all layers).
    pub verified: u64,
    /// Number of candidate sites rejected (not equivalent / timeout / error).
    pub rejected: u64,
    /// Number of times the wall-clock budget was exhausted mid-function.
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
    pub force_expired_deadline: bool,
    pub force_layer_a_equal_cost: bool,
    pub force_layer_b_equal_cost: bool,
    pub verifier_result: Option<CegisResult>,
}

// ---------------------------------------------------------------------------
// The pass
// ---------------------------------------------------------------------------

/// CEGIS-driven superoptimization pass.
///
/// This is a thin wrapper around [`crate::CegisLoop`] that threads a
/// per-function time budget and a shared compilation cache. On a cache hit it
/// skips all solver work. On a miss it walks the function instructions and
/// invokes `CegisLoop::verify` for each candidate rewrite site (if any),
/// aborting early when the budget is exhausted.
///
/// The first payload layer rewrites `MulRR x, (Movz #0)` to `Movz #0` when the
/// verifier proves equivalence and the replacement is strictly cheaper.
pub struct CegisSuperoptPass {
    config: CegisSuperoptConfig,
    stats: CegisPassStats,
    test_hooks: CegisSuperoptTestHooks,
    failed_proof_counterexamples: FailedProofCounterexampleCorpus,
    failed_proof_counterexample_scope: Option<(SourceRegionIdentity, TargetAbiLayoutIdentity)>,
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

    /// Return the collected statistics.
    pub fn stats(&self) -> &CegisPassStats {
        &self.stats
    }

    /// Compute the deterministic per-function cache key.
    ///
    /// Hashes:
    /// - function name (framed)
    /// - number of instructions (framed)
    /// - each instruction's opcode Debug repr + operand count
    /// - block layout (entry + block_order)
    /// - opt_level, target_triple, cpu, features
    ///
    /// The resulting key is the same structure used by
    /// [`trust_cg_opt::CacheKey`] so callers can share a single on-disk cache
    /// between whole-module and per-function entries.
    pub fn compute_function_key(&self, func: &MachFunction) -> CacheKey {
        let mut h = StableHasher::new();
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

    fn match_layer_a_candidate(
        func: &MachFunction,
        inst: &MachInst,
        def_map: &HashMap<u32, trust_cg_ir::InstId>,
    ) -> Option<(u32, MachInst)> {
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

        Some((width, replacement))
    }

    fn enumerate_and_verify_layer_a(
        &mut self,
        func: &mut MachFunction,
        deadline: Instant,
        failed_proof_scope: Option<(&SourceRegionIdentity, &TargetAbiLayoutIdentity)>,
    ) -> (bool, CegisCacheEntry, bool, bool) {
        let mut entry = CegisCacheEntry::empty();
        let mut committed = false;
        let mut used_failed_proof_seed = false;

        if ProvenRuleDb::seed_layer_a().is_empty() {
            return (false, entry, false, false);
        }

        let cost_model = AppleSiliconCostModel::new(CostModelGen::M1);
        let mut cegis = CegisLoop::new(1, self.config.per_query_ms);
        let mut exhausted = false;

        'blocks: for block_id in func.block_order.clone() {
            let inst_ids = func.block(block_id).insts.clone();
            let mut def_map = HashMap::new();

            for inst_id in inst_ids {
                if Instant::now() >= deadline {
                    exhausted = true;
                    break 'blocks;
                }

                let inst = func.inst(inst_id).clone();
                if let Some((width, replacement)) =
                    Self::match_layer_a_candidate(func, &inst, &def_map)
                {
                    self.stats.candidates += 1;
                    self.stats.layer_a_candidates += 1;
                    entry.attempted += 1;

                    let src_cost = cost_model.latency(AArch64Opcode::MulRR) as i32;
                    let tgt_cost = if self.test_hooks.force_layer_a_equal_cost {
                        src_cost
                    } else {
                        cost_model.latency(AArch64Opcode::Movz) as i32
                    };
                    if tgt_cost >= src_cost {
                        self.stats.rejected += 1;
                        entry.rejected += 1;
                    } else {
                        let vars = vec![("x".to_string(), width)];
                        let src = SmtExpr::var("x", width).bvmul(SmtExpr::bv_const(0, width));
                        let tgt = SmtExpr::bv_const(0, width);
                        // Clear counterexamples from prior candidates so a
                        // CX proving a different obligation cannot trigger a
                        // spurious `NotEquivalent` fast-path rejection here
                        // (#493). Stats accumulate across candidates via
                        // `clear_counterexamples` (not `reset`).
                        cegis.clear_counterexamples();
                        cegis.add_edge_case_seeds(&vars);
                        if self.add_failed_proof_counterexample_seeds(
                            &mut cegis,
                            failed_proof_scope,
                            &vars,
                        ) > 0
                        {
                            used_failed_proof_seed = true;
                        }

                        // Wall-clock the solver call so we can populate
                        // `stats.solver_ms`. CegisLoop::verify does concrete
                        // eval + potentially several ay queries; we attribute
                        // the entire elapsed duration to "solver" since that
                        // is what the #486 acceptance criterion wants
                        // (anything that is not pure enumeration/mutation).
                        let solver_start = Instant::now();
                        let result = if let Some(result) = self.test_hooks.verifier_result.clone() {
                            Ok(result)
                        } else {
                            catch_unwind(AssertUnwindSafe(|| cegis.verify(&src, &tgt, &vars)))
                        };
                        self.stats.solver_ms = self
                            .stats
                            .solver_ms
                            .saturating_add(solver_start.elapsed().as_millis() as u64);

                        match result {
                            Ok(CegisResult::Equivalent {
                                proof_hash,
                                iterations,
                            }) => {
                                let replacement_blob = MachInstBlob::from_inst(&replacement);
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
                            }
                            Ok(CegisResult::NotEquivalent { .. }) => {
                                self.stats.rejected += 1;
                                entry.rejected += 1;
                            }
                            Ok(CegisResult::Timeout | CegisResult::MaxIterationsReached { .. }) => {
                                self.stats.timeouts += 1;
                                self.stats.rejected += 1;
                                entry.rejected += 1;
                            }
                            Ok(CegisResult::Error(_)) => {
                                self.stats.verifier_errors += 1;
                                self.stats.rejected += 1;
                                entry.rejected += 1;
                            }
                            Err(_) => {
                                self.stats.panics += 1;
                                self.stats.rejected += 1;
                                entry.rejected += 1;
                            }
                        }
                    }
                }

                let current_inst = func.inst(inst_id);
                if current_inst.produces_value()
                    && let Some(dst) = current_inst.operands.first().and_then(MachOperand::as_vreg)
                {
                    def_map.insert(dst.id, inst_id);
                }
            }
        }

        if exhausted {
            self.stats.budget_exhausted += 1;
        }
        self.stats.solver_calls += cegis.stats_solver_calls();

        (committed, entry, exhausted, used_failed_proof_seed)
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
    /// 2. The `Movz`'s `dst` VReg becomes dead after the splice. We verified
    ///    above that it has exactly one use (the current `AddRR`), so no
    ///    other consumer is left dangling.
    /// 3. The `AddRR`'s `src` operand is kept verbatim.
    ///
    /// Constraints enforced:
    /// - `Movz` must be a proof-covered shift-zero form (implicit or explicit)
    ///   and its immediate must be non-negative and fit in `u32::MAX`
    ///   (downstream encoders further restrict to ADD's 12-bit imm field,
    ///   but that is a concern for codegen, not for the semantic proof).
    /// - The Movz result VReg must be used exactly once in the function.
    /// - The register class of AddRR's `dst`, `src`, and `v` must agree
    ///   (Gpr32 or Gpr64).
    fn match_layer_b_candidate(
        func: &MachFunction,
        add_inst: &MachInst,
        def_map: &HashMap<u32, trust_cg_ir::InstId>,
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
        if imm < 0 || imm > u32::MAX as i64 {
            return None;
        }

        // Single-use check: if any other instruction in the function reads
        // the Movz destination, we cannot splice it out.
        if count_vreg_uses(func, movz_vreg) != 1 {
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
        deadline: Instant,
        entry: &mut CegisCacheEntry,
        failed_proof_scope: Option<(&SourceRegionIdentity, &TargetAbiLayoutIdentity)>,
    ) -> (bool, bool) {
        let mut committed = false;
        let mut used_failed_proof_seed = false;

        if ProvenRuleDb::seed_layer_b().is_empty() {
            return (false, false);
        }

        let cost_model = AppleSiliconCostModel::new(CostModelGen::M1);
        let mut cegis = CegisLoop::new(1, self.config.per_query_ms);
        let mut exhausted = false;

        'blocks: for block_id in func.block_order.clone() {
            let inst_ids = func.block(block_id).insts.clone();
            let mut def_map: HashMap<u32, trust_cg_ir::InstId> = HashMap::new();
            let mut to_remove: Vec<trust_cg_ir::InstId> = Vec::new();

            for inst_id in inst_ids {
                if Instant::now() >= deadline {
                    exhausted = true;
                    break 'blocks;
                }

                let inst = func.inst(inst_id).clone();
                if let Some((width, movz_id, replacement)) =
                    Self::match_layer_b_candidate(func, &inst, &def_map)
                {
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
                    if tgt_cost >= src_cost {
                        self.stats.rejected += 1;
                        entry.rejected += 1;
                    } else {
                        let imm_val = func
                            .inst(movz_id)
                            .operands
                            .get(1)
                            .and_then(MachOperand::as_imm)
                            .unwrap_or(0);
                        let imm_u = (imm_val as u64) & mask_u64(width);

                        let vars = vec![("y".to_string(), width)];
                        let src_expr =
                            SmtExpr::var("y", width).bvadd(SmtExpr::bv_const(imm_u, width));
                        let tgt_expr =
                            SmtExpr::var("y", width).bvadd(SmtExpr::bv_const(imm_u, width));
                        // Scope CX state to this candidate (#493). Different
                        // `imm` values per candidate mean each `src_expr`
                        // uses a distinct constant; leaving prior CXs in
                        // place would let them reject this obligation on
                        // the concrete fast path.
                        cegis.clear_counterexamples();
                        cegis.add_edge_case_seeds(&vars);
                        if self.add_failed_proof_counterexample_seeds(
                            &mut cegis,
                            failed_proof_scope,
                            &vars,
                        ) > 0
                        {
                            used_failed_proof_seed = true;
                        }

                        let solver_start = Instant::now();
                        let result = if let Some(result) = self.test_hooks.verifier_result.clone() {
                            Ok(result)
                        } else {
                            catch_unwind(AssertUnwindSafe(|| {
                                cegis.verify(&src_expr, &tgt_expr, &vars)
                            }))
                        };
                        self.stats.solver_ms = self
                            .stats
                            .solver_ms
                            .saturating_add(solver_start.elapsed().as_millis() as u64);

                        match result {
                            Ok(CegisResult::Equivalent {
                                proof_hash,
                                iterations,
                            }) => {
                                let replacement_blob = MachInstBlob::from_inst(&replacement);
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
                            }
                            Ok(CegisResult::NotEquivalent { .. }) => {
                                self.stats.rejected += 1;
                                entry.rejected += 1;
                            }
                            Ok(CegisResult::Timeout | CegisResult::MaxIterationsReached { .. }) => {
                                self.stats.timeouts += 1;
                                self.stats.rejected += 1;
                                entry.rejected += 1;
                            }
                            Ok(CegisResult::Error(_)) => {
                                self.stats.verifier_errors += 1;
                                self.stats.rejected += 1;
                                entry.rejected += 1;
                            }
                            Err(_) => {
                                self.stats.panics += 1;
                                self.stats.rejected += 1;
                                entry.rejected += 1;
                            }
                        }
                    }
                }

                // Update def_map with the CURRENT body (possibly just
                // rewritten from AddRR to AddRI — both produce `dst`).
                let current_inst = func.inst(inst_id);
                if current_inst.produces_value()
                    && let Some(dst) = current_inst.operands.first().and_then(MachOperand::as_vreg)
                {
                    def_map.insert(dst.id, inst_id);
                }
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

        if exhausted {
            self.stats.budget_exhausted += 1;
        }
        self.stats.solver_calls += cegis.stats_solver_calls();

        (committed, used_failed_proof_seed)
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
            let Some(dst) = inst.operands.first().and_then(MachOperand::as_vreg) else {
                continue;
            };
            if dst != target {
                continue;
            }

            match inst.opcode {
                AArch64Opcode::Movz => {
                    let imm = Self::move_wide_imm16(inst)?;
                    let shift = Self::move_wide_shift(inst, width)?;
                    value = Some((imm << shift) & register_mask);
                    materializer_ids.clear();
                    materializer_ids.push(inst_id);
                }
                AArch64Opcode::Movn => {
                    let imm = Self::move_wide_imm16(inst)?;
                    let shift = Self::move_wide_shift(inst, width)?;
                    value = Some((!(imm << shift)) & register_mask);
                    materializer_ids.clear();
                    materializer_ids.push(inst_id);
                }
                AArch64Opcode::Movk => {
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
    /// immediate and the mask vreg has exactly one read, so the materializer
    /// chain can be removed from the block schedule.
    fn match_layer_c_and_imm_candidate(
        func: &MachFunction,
        block_id: trust_cg_ir::BlockId,
        and_id: InstId,
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

        if count_vreg_uses(func, mask_vreg) != 1 {
            return None;
        }

        let (mask, materializer_ids) =
            Self::materialized_wide_const_before(func, block_id, and_id, mask_vreg, width)?;
        if !is_aarch64_logical_immediate(mask, width) {
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
            width,
            materializer_ids,
            replacement,
            mask,
        })
    }

    fn enumerate_and_verify_layer_c(
        &mut self,
        func: &mut MachFunction,
        deadline: Instant,
        entry: &mut CegisCacheEntry,
        failed_proof_scope: Option<(&SourceRegionIdentity, &TargetAbiLayoutIdentity)>,
    ) -> (bool, bool) {
        let mut committed = false;
        let mut used_failed_proof_seed = false;

        if ProvenRuleDb::seed_layer_c().is_empty() {
            return (false, false);
        }

        let cost_model = AppleSiliconCostModel::new(CostModelGen::M1);
        let mut cegis = CegisLoop::new(1, self.config.per_query_ms);
        let mut exhausted = false;

        'blocks: for block_id in func.block_order.clone() {
            let inst_ids = func.block(block_id).insts.clone();
            let mut to_remove: Vec<InstId> = Vec::new();

            for inst_id in inst_ids {
                if Instant::now() >= deadline {
                    exhausted = true;
                    break 'blocks;
                }

                let Some(candidate) =
                    Self::match_layer_c_and_imm_candidate(func, block_id, inst_id)
                else {
                    continue;
                };

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
                if tgt_cost >= src_cost {
                    self.stats.rejected += 1;
                    entry.rejected += 1;
                    continue;
                }

                let vars = vec![("x".to_string(), candidate.width)];
                let src_expr = SmtExpr::var("x", candidate.width)
                    .bvand(SmtExpr::bv_const(candidate.mask, candidate.width));
                let tgt_expr = SmtExpr::var("x", candidate.width)
                    .bvand(SmtExpr::bv_const(candidate.mask, candidate.width));
                cegis.clear_counterexamples();
                cegis.add_edge_case_seeds(&vars);
                if self.add_failed_proof_counterexample_seeds(&mut cegis, failed_proof_scope, &vars)
                    > 0
                {
                    used_failed_proof_seed = true;
                }

                let solver_start = Instant::now();
                let result = if let Some(result) = self.test_hooks.verifier_result.clone() {
                    Ok(result)
                } else {
                    catch_unwind(AssertUnwindSafe(|| {
                        cegis.verify(&src_expr, &tgt_expr, &vars)
                    }))
                };
                self.stats.solver_ms = self
                    .stats
                    .solver_ms
                    .saturating_add(solver_start.elapsed().as_millis() as u64);

                match result {
                    Ok(CegisResult::Equivalent {
                        proof_hash,
                        iterations,
                    }) => {
                        let replacement_blob = MachInstBlob::from_inst(&candidate.replacement);
                        *func.inst_mut(inst_id) = candidate.replacement;
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
                    }
                    Ok(CegisResult::NotEquivalent { .. }) => {
                        self.stats.rejected += 1;
                        entry.rejected += 1;
                    }
                    Ok(CegisResult::Timeout | CegisResult::MaxIterationsReached { .. }) => {
                        self.stats.timeouts += 1;
                        self.stats.rejected += 1;
                        entry.rejected += 1;
                    }
                    Ok(CegisResult::Error(_)) => {
                        self.stats.verifier_errors += 1;
                        self.stats.rejected += 1;
                        entry.rejected += 1;
                    }
                    Err(_) => {
                        self.stats.panics += 1;
                        self.stats.rejected += 1;
                        entry.rejected += 1;
                    }
                }
            }

            if !to_remove.is_empty() {
                let remove_set: std::collections::HashSet<_> = to_remove.into_iter().collect();
                func.block_mut(block_id)
                    .insts
                    .retain(|id| !remove_set.contains(id));
            }
        }

        if exhausted {
            self.stats.budget_exhausted += 1;
        }
        self.stats.solver_calls += cegis.stats_solver_calls();

        (committed, used_failed_proof_seed)
    }

    /// Apply a single cached rewrite to `func` from the serialized replacement
    /// body recorded in [`ProvenRewrite`].
    ///
    /// Returns `true` if the rewrite was applied. Bad indices or undecodable
    /// blobs are treated as unapplied rewrites rather than hard pass failures.
    fn apply_cached_rewrite(func: &mut MachFunction, rewrite: &ProvenRewrite) -> bool {
        let target_id = trust_cg_ir::InstId(rewrite.inst_index);
        if (target_id.0 as usize) >= func.insts.len() {
            return false;
        }
        if rewrite.window_len == 0 || rewrite.replacement.is_empty() {
            return false;
        }

        let Some(block_id) = func
            .block_order
            .iter()
            .copied()
            .find(|b| func.block(*b).insts.contains(&target_id))
        else {
            return false;
        };

        let source_inst = func.inst(target_id).clone();
        let mut rebuilt = Vec::with_capacity(rewrite.replacement.len());
        for blob in &rewrite.replacement {
            let Some(inst) = blob.to_inst() else {
                return false;
            };
            rebuilt.push(inst);
        }
        if let Some(first) = rebuilt.first_mut() {
            first.proof = source_inst.proof;
            first.source_loc = source_inst.source_loc;
        }

        let mut remove_ids = Vec::new();
        match rewrite.layer {
            RewriteLayer::A => {
                if !Self::cached_layer_a_source_is_valid(func, block_id, target_id) {
                    return false;
                }
            }
            RewriteLayer::B => {
                if let Some(movz_id) = Self::cached_layer_b_movz_id(func, block_id, target_id) {
                    remove_ids.push(movz_id);
                } else {
                    return false;
                }
            }
            RewriteLayer::C => {
                let Some(mut materializers) =
                    Self::cached_layer_c_materializer_ids(func, block_id, target_id)
                else {
                    return false;
                };
                remove_ids.append(&mut materializers);
            }
        }

        let first = rebuilt.remove(0);
        *func.inst_mut(target_id) = first;

        let mut inserted_ids = Vec::with_capacity(rebuilt.len());
        for inst in rebuilt {
            inserted_ids.push(func.push_inst(inst));
        }

        let block = func.block_mut(block_id);
        if let Some(pos) = block.insts.iter().position(|id| *id == target_id) {
            if rewrite.layer == RewriteLayer::A {
                let extra = rewrite.window_len.saturating_sub(1) as usize;
                if extra > 0 {
                    let end = (pos + 1 + extra).min(block.insts.len());
                    block.insts.drain(pos + 1..end);
                }
            }
            for (offset, new_id) in inserted_ids.into_iter().enumerate() {
                block.insts.insert(pos + 1 + offset, new_id);
            }
        } else {
            return false;
        }

        if !remove_ids.is_empty() {
            let remove_set: std::collections::HashSet<_> = remove_ids.into_iter().collect();
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

    /// Find the producer Movz that Layer B's cold path spliced out.
    ///
    /// The replacement body itself comes from the cache blob; this helper only
    /// recovers the source instruction to remove from the block schedule.
    fn cached_layer_b_movz_id(
        func: &MachFunction,
        block_id: trust_cg_ir::BlockId,
        target_id: trust_cg_ir::InstId,
    ) -> Option<trust_cg_ir::InstId> {
        let inst = func.inst(target_id);
        if inst.opcode != AArch64Opcode::AddRR || inst.operands.len() < 3 {
            return None;
        }
        let movz_vreg = inst.operands.get(2)?.as_vreg()?;

        let mut def_map = HashMap::new();
        for &inst_id in &func.block(block_id).insts {
            if inst_id == target_id {
                break;
            }
            let inst = func.inst(inst_id);
            if inst.produces_value()
                && let Some(dst) = inst.operands.first().and_then(MachOperand::as_vreg)
            {
                def_map.insert(dst.id, inst_id);
            }
        }
        let movz_id = *def_map.get(&movz_vreg.id)?;
        let movz_inst = func.inst(movz_id);
        if movz_inst.opcode != AArch64Opcode::Movz {
            return None;
        }
        if movz_inst.operands.first()?.as_vreg()? != movz_vreg {
            return None;
        }
        let width = match movz_vreg.class {
            RegClass::Gpr32 => 32,
            RegClass::Gpr64 => 64,
            _ => return None,
        };
        Self::move_wide_imm16(movz_inst)?;
        if Self::move_wide_shift(movz_inst, width)? != 0 {
            return None;
        }
        if count_vreg_uses(func, movz_vreg) != 1 {
            return None;
        }
        Some(movz_id)
    }

    /// Revalidate Layer A's source window before replaying a cache entry.
    ///
    /// Cache blobs can outlive matcher hardening.  In particular, an older
    /// entry must not normalize away a now-non-emittable shifted `Movz`.
    fn cached_layer_a_source_is_valid(
        func: &MachFunction,
        block_id: trust_cg_ir::BlockId,
        target_id: trust_cg_ir::InstId,
    ) -> bool {
        let mut def_map = HashMap::new();
        for &inst_id in &func.block(block_id).insts {
            if inst_id == target_id {
                break;
            }
            let inst = func.inst(inst_id);
            if inst.produces_value()
                && let Some(dst) = inst.operands.first().and_then(MachOperand::as_vreg)
            {
                def_map.insert(dst.id, inst_id);
            }
        }
        Self::match_layer_a_candidate(func, func.inst(target_id), &def_map).is_some()
    }

    fn cached_layer_c_materializer_ids(
        func: &MachFunction,
        block_id: trust_cg_ir::BlockId,
        target_id: InstId,
    ) -> Option<Vec<InstId>> {
        Self::match_layer_c_and_imm_candidate(func, block_id, target_id)
            .map(|candidate| candidate.materializer_ids)
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

    /// Body of `run` split out so that it can be unit-tested without needing
    /// to implement `MachinePass` in tests.
    fn run_inner(&mut self, func: &mut MachFunction) -> bool {
        if !self.config.is_enabled() {
            return false;
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
        let mut used_failed_proof_seed = false;

        // Cache hit path --------------------------------------------------
        let mut used_cache = false;
        if !cache_disabled_by_failed_proof_fuel
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
                // Treat stale cache plans as misses. Restore any partial replay
                // before re-running enumeration on the current function body.
                *func = before_replay;
            }
        }

        if !used_cache {
            // Cache miss path ---------------------------------------------
            self.stats.cache_misses += 1;

            let deadline = if self.test_hooks.force_expired_deadline {
                Instant::now()
            } else {
                Instant::now() + Duration::from_secs(self.config.budget_sec)
            };
            let (committed_a, mut entry, exhausted_a, used_seed_a) =
                self.enumerate_and_verify_layer_a(func, deadline, failed_proof_scope);
            used_failed_proof_seed |= used_seed_a;
            // Layer B runs after Layer A so that any Layer-A-rewrites are
            // visible to the window enumerator (e.g. a MulRR->Movz collapse
            // could unblock a subsequent two-inst fusion).
            let (committed_b, used_seed_b) = if exhausted_a {
                (false, false)
            } else {
                self.enumerate_and_verify_layer_b(func, deadline, &mut entry, failed_proof_scope)
            };
            used_failed_proof_seed |= used_seed_b;
            let (committed_c, used_seed_c) = if exhausted_a {
                (false, false)
            } else {
                self.enumerate_and_verify_layer_c(func, deadline, &mut entry, failed_proof_scope)
            };
            used_failed_proof_seed |= used_seed_c;
            committed = committed_a || committed_b || committed_c;

            // Persist the (possibly empty) entry so repeat runs see a cache
            // hit. Seeded failed-proof runs deliberately skip normal cache
            // writes because the function cache key does not encode the
            // counterexample corpus identity.
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
                        // Serialization should never fail for a well-formed
                        // entry; if it does, drop the put silently — the pass
                        // is still semantically correct, just slower next time.
                    }
                }
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
        // regex; the goal is discoverability under `cargo run -- --trace`
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
                        reason: if from_cache {
                            "cache-hit: no rewrites replayed".to_string()
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

        committed
    }
}

impl MachinePass for CegisSuperoptPass {
    fn name(&self) -> &str {
        "CegisSuperoptPass"
    }

    fn run(&mut self, func: &mut MachFunction) -> bool {
        self.run_inner(func)
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
            CegisSuperoptPass::match_layer_b_candidate(&func, &add, &def_map).is_none(),
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
    fn test_cache_entry_roundtrip() {
        let entry = CegisCacheEntry {
            version: CegisCacheEntry::VERSION,
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
        for old_version in [1u32, 2u32, 3u32, 4u32] {
            let entry = CegisCacheEntry {
                version: old_version,
                ..Default::default()
            };
            let bytes = entry.encode().expect("encode");
            assert!(
                CegisCacheEntry::decode(&bytes).is_none(),
                "v{} cache entries must be rejected after VERSION=4 bump",
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
