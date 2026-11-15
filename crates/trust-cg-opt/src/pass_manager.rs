// trust-cg-opt - Pass manager framework
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Pass manager framework for running optimization passes on machine functions.
//!
//! The `MachinePass` trait defines the interface for all optimization passes.
//! `PassManager` runs a sequence of passes, optionally iterating to fixed point.
//!
//! # Architecture
//!
//! Each pass operates on a `MachFunction` from `trust-cg-ir` and returns `true`
//! if it made any modifications. The pass manager can run passes once or
//! iterate the entire sequence until no pass reports changes (fixed point).
//!
//! ```text
//! PassManager { passes: [DCE, ConstFold, CopyProp, RotateIdiom] }
//!     │
//!     ├── run_once(func)   → runs each pass in order, once
//!     └── run_to_fixpoint(func, max_iters) → repeats until stable
//! ```

use std::hash::{Hash, Hasher};
use std::time::Instant;

use serde::{Deserialize, Serialize};
use trust_cg_ir::{BlockId, MachFunction, MachIdRefusal, MachOperand, ProvenanceMap};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
use crate::pass_validation::{
    FunctionInterfaceDigest, PassValidationConfig, PassValidationHook, PassValidationSummary,
};
use crate::proof_opts::{OptCertificate, ProofOptimizationMetadata};

/// Local result status for a certified pass run recorded by `trust-cg-opt`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CertifiedPassRunStatus {
    /// The pass-local checker accepted every emitted obligation.
    Verified,
    /// The pass-local checker rejected at least one obligation or the pass
    /// observed an unsupported candidate in certified mode.
    Failed,
}

impl CertifiedPassRunStatus {
    /// Stable lowercase status string used in JSON attachments.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Verified => "verified",
            Self::Failed => "failed",
        }
    }

    /// Whether this status can be consumed by a certified compile.
    pub fn is_verified(self) -> bool {
        matches!(self, Self::Verified)
    }
}

/// Pass-local checker identity for one certified pass run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertifiedPassCheckerRecord {
    /// Checker family. This stays neutral: `trust-cg-opt` does not depend on
    /// `trust-cg-verify` or Lean.
    pub kind: String,
    /// Human-readable checker id.
    pub name: String,
    /// Checker version.
    pub version: String,
    /// Local checker status for this run.
    pub status: CertifiedPassRunStatus,
}

/// Neutral certified pass execution record emitted by `trust-cg-opt`.
///
/// This record is intentionally verify-crate agnostic. Codegen may convert it
/// into a checker-backed chain later, but opt only records the local
/// pass-certified result, stable obligation hash, and pass-specific JSON
/// summary.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CertifiedPassRunRecord {
    /// Record schema version.
    pub format_version: String,
    /// Certified pass identity used by downstream chain entries.
    pub pass_name: String,
    /// Certified pass implementation version.
    pub pass_version: u32,
    /// Stable pass instance id for this certified wrapper.
    pub pass_instance_id: String,
    /// Function this pass execution transformed or checked.
    pub function_name: String,
    /// Whether this pass reported an IR change.
    pub changed: bool,
    /// Pass-local certified result.
    pub status: CertifiedPassRunStatus,
    /// Number of pass-local certificates emitted by this run.
    pub certificate_count: usize,
    /// Number of pass-local certification failures emitted by this run.
    pub failure_count: usize,
    /// Stable aggregate obligation hash for the pass run.
    pub obligation_hash: String,
    /// Pass-local checker identity and status.
    pub local_checker: CertifiedPassCheckerRecord,
    /// Pass-specific neutral JSON summary.
    pub summary: serde_json::Value,
}

impl CertifiedPassRunRecord {
    /// Whether this run can be converted into a production certified chain
    /// entry. Both the run and its local checker must be verified and the pass
    /// must have reported no certification failures.
    pub fn is_verified(&self) -> bool {
        self.status.is_verified()
            && self.local_checker.status.is_verified()
            && self.failure_count == 0
    }
}

/// Lightweight observability for cached analysis reuse.
/// Counters saturate at u32::MAX; they never authorize an analysis cache hit.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct AnalysisCacheStats {
    /// Number of dominator tree computations performed by this cache.
    pub domtree_computations: u32,
    /// Number of loop analysis computations performed by this cache.
    pub loop_analysis_computations: u32,
    /// Changed passes whose CFG fingerprint stayed stable.
    pub cfg_preservations: u32,
    /// Invalidation requests from the driver or a stale graph detected at lookup.
    pub cfg_invalidations: u32,
}

/// Cached analysis results shared across passes within an iteration.
///
/// Avoids redundant recomputation of dominator trees and loop analysis
/// when multiple passes need them within a single fixpoint iteration.
/// Every lookup compares the exact graph inputs used by these analyses. A
/// changed entry, layout, block domain, or predecessor/successor list invalidates
/// both results, including direct reuse with another function. Non-CFG edits
/// preserve them. Returned analyses are snapshots: callers must not assume an
/// already-borrowed result updates when they subsequently mutate the function.
pub struct AnalysisCache {
    cfg: Option<AnalysisCfg>,
    domtree: Option<DomTree>,
    loop_analysis: Option<LoopAnalysis>,
    stats: AnalysisCacheStats,
}

/// Exact inputs read by DomTree and LoopAnalysis (not a digest or pointer key).
/// Instruction data is deliberately absent: those analyses read CFG metadata,
/// whose consistency with branch instructions is checked at other boundaries.
struct AnalysisCfg {
    entry: BlockId,
    block_order: Vec<BlockId>,
    blocks: Vec<(Vec<BlockId>, Vec<BlockId>)>,
}

impl AnalysisCfg {
    fn capture(func: &MachFunction) -> Self {
        Self {
            entry: func.entry,
            block_order: func.block_order.clone(),
            blocks: func
                .blocks
                .iter()
                .map(|block| (block.preds.to_vec(), block.succs.to_vec()))
                .collect(),
        }
    }

    fn matches(&self, func: &MachFunction) -> bool {
        self.entry == func.entry
            && self.block_order == func.block_order
            && self.blocks.len() == func.blocks.len()
            && self
                .blocks
                .iter()
                .zip(func.blocks.iter())
                .all(|((preds, succs), block)| {
                    preds.as_slice() == block.preds.as_slice()
                        && succs.as_slice() == block.succs.as_slice()
                })
    }
}

impl AnalysisCache {
    /// Create an empty analysis cache.
    pub fn new() -> Self {
        Self {
            cfg: None,
            domtree: None,
            loop_analysis: None,
            stats: AnalysisCacheStats::default(),
        }
    }

    fn ensure_current_cfg(&mut self, func: &MachFunction) {
        if self.cfg.as_ref().is_some_and(|cfg| cfg.matches(func)) {
            return;
        }
        if self.cfg.is_some() {
            self.invalidate();
        }
        self.cfg = Some(AnalysisCfg::capture(func));
    }

    /// Get the dominator tree, computing and caching it if necessary.
    pub fn domtree(&mut self, func: &MachFunction) -> &DomTree {
        self.ensure_current_cfg(func);
        self.domtree.get_or_insert_with(|| {
            let dom = DomTree::compute(func);
            self.stats.domtree_computations = self.stats.domtree_computations.saturating_add(1);
            dom
        })
    }

    /// Get the loop analysis, computing and caching it if necessary.
    /// This also ensures the dominator tree is cached.
    pub fn loop_analysis(&mut self, func: &MachFunction) -> &LoopAnalysis {
        self.domtree_and_loops(func).1
    }

    /// Both CFG analyses from one borrow, so a pass can hold the dominator
    /// tree and the loop analysis together while it mutates the function
    /// (the analyses belong to the cache, not to the function).
    pub fn domtree_and_loops(&mut self, func: &MachFunction) -> (&DomTree, &LoopAnalysis) {
        self.ensure_current_cfg(func);
        // Loop analysis consumes this exact graph's dominator tree. Filling
        // slots in place returns their references without a second lookup.
        let dom: &DomTree = self.domtree.get_or_insert_with(|| {
            self.stats.domtree_computations = self.stats.domtree_computations.saturating_add(1);
            DomTree::compute(func)
        });
        let loops: &LoopAnalysis = self.loop_analysis.get_or_insert_with(|| {
            self.stats.loop_analysis_computations =
                self.stats.loop_analysis_computations.saturating_add(1);
            LoopAnalysis::compute(func, dom)
        });
        (dom, loops)
    }

    /// Current cache reuse statistics.
    pub fn stats(&self) -> AnalysisCacheStats {
        self.stats
    }

    /// Record that a changed pass preserved the CFG, so analyses remain valid.
    pub fn preserve_for_unchanged_cfg(&mut self) {
        self.stats.cfg_preservations = self.stats.cfg_preservations.saturating_add(1);
    }

    /// Invalidate all cached analyses. Called when a pass changes the CFG.
    pub fn invalidate(&mut self) {
        self.cfg = None;
        self.domtree = None;
        self.loop_analysis = None;
        self.stats.cfg_invalidations = self.stats.cfg_invalidations.saturating_add(1);
    }
}

impl Default for AnalysisCache {
    fn default() -> Self {
        Self::new()
    }
}

/// A single optimization pass that transforms machine-level IR.
///
/// Passes must be idempotent: running a pass twice on unchanged input
/// should not modify anything on the second run.
pub trait MachinePass {
    /// Human-readable name for diagnostics and logging.
    fn name(&self) -> &str;

    /// Run the pass on a machine function.
    ///
    /// Returns `true` if the function was modified, `false` if unchanged.
    /// A pass returning `true` may enable further optimizations in
    /// subsequent passes.
    fn run(&mut self, func: &mut MachFunction) -> bool;

    /// Run the pass with access to cached analyses.
    ///
    /// Passes that need dominator trees or loop analysis should override
    /// this method to use the cache instead of recomputing from scratch.
    /// The default implementation ignores the cache and calls `run()`.
    fn run_with_analyses(
        &mut self,
        func: &mut MachFunction,
        _analyses: &mut AnalysisCache,
    ) -> bool {
        self.run(func)
    }

    /// Run the pass with access to a provenance map.
    ///
    /// Passes that can update instruction provenance should override this
    /// method when they do not need cached analyses. The default implementation
    /// preserves the existing [`MachinePass::run`] behavior.
    fn run_with_provenance(
        &mut self,
        func: &mut MachFunction,
        _provenance: &mut ProvenanceMap,
    ) -> bool {
        self.run(func)
    }

    /// Run the pass with access to both cached analyses and provenance.
    ///
    /// The pass manager's provenance-aware fixed-point APIs call this hook.
    /// Passes that already override [`MachinePass::run_with_analyses`] keep
    /// using their cached-analysis implementation until they opt in to
    /// provenance updates by overriding this method.
    fn run_with_analyses_and_provenance(
        &mut self,
        func: &mut MachFunction,
        analyses: &mut AnalysisCache,
        _provenance: &mut ProvenanceMap,
    ) -> bool {
        self.run_with_analyses(func, analyses)
    }

    /// Configure proof-optimization sidecar metadata.
    ///
    /// Most passes ignore this. `ProofOptimization` consumes it so the boxed
    /// production pipeline can receive #794 proof facts, source-region hashes,
    /// and product-gate rejection metadata without downcasting.
    fn set_proof_optimization_metadata(&mut self, _metadata: &ProofOptimizationMetadata) {}

    /// Drain proof-optimization certificates emitted by this pass run.
    ///
    /// The pass manager calls this after each boxed pass execution so callers
    /// can cite optimization certificate IDs and hashes from [`PassStats`].
    fn take_proof_optimization_certificates(&mut self) -> Vec<OptCertificate> {
        Vec::new()
    }

    /// Drain certified pass execution records emitted by this pass run.
    ///
    /// The default is empty so existing passes remain unaffected. Certified
    /// wrapper passes override this to expose neutral opt-side records without
    /// depending on `trust-cg-verify`.
    fn take_certified_pass_runs(&mut self) -> Vec<CertifiedPassRunRecord> {
        Vec::new()
    }

    /// Independent fail-closed re-check of any kernel-authorized guard
    /// eliminations performed by this pass run.
    ///
    /// Sentinel S4: this is the "different path" re-validation. The boxed proof
    /// pass runs inside a [`PassManager`] and is then dropped, so the pass
    /// manager queries this hook after each run and surfaces the verdict through
    /// [`PassStats::kernel_recheck`]. A production caller maps a rejection to a
    /// compile abort (parity with the x86 path, which owns its pass instance and
    /// calls the equivalent re-check inline).
    ///
    /// The default is `Ok(())` so passes that never gate on the kernel (the vast
    /// majority) are unaffected. `ProofOptimization` overrides this to re-derive
    /// each eliminated carrier's operand fingerprint and re-confirm discharge
    /// against the evidence.
    fn recheck_kernel_eliminations(&self) -> Result<(), String> {
        Ok(())
    }
}

/// Statistics collected during pass execution.
#[derive(Debug, Clone)]
pub struct PassStats {
    /// Number of times each pass was run.
    pub runs: Vec<(String, u32)>,
    /// Number of runs of each pass that reported a change, parallel to
    /// [`PassStats::runs`] (same names, same order, zero when the pass never
    /// changed the function). A pass absent from both lists was not
    /// scheduled.
    pub changed_runs: Vec<(String, u32)>,
    /// Total number of passes that reported changes.
    pub changes: u32,
    /// Number of fixed-point iterations.
    pub iterations: u32,
    /// Proof-guided optimization certificates emitted by boxed passes.
    pub proof_optimization_certificates: Vec<OptCertificate>,
    /// Neutral certified pass execution records emitted by boxed passes.
    pub certified_pass_runs: Vec<CertifiedPassRunRecord>,
    /// Sentinel S4 fail-closed verdict: the independent re-check of every
    /// kernel-authorized guard elimination performed across all boxed passes.
    ///
    /// `Ok(())` when no kernel-gated elimination occurred or all eliminations
    /// independently re-justified. The first rejection reason is retained and
    /// later rejections are ignored (the caller aborts on the first). A
    /// production caller must treat `Err` as a fatal compile error (parity with
    /// the x86 inline re-check).
    pub kernel_recheck: Result<(), String>,
    /// L10-P5 identity admission verdict. Every driver re-derives the
    /// function's live register/instruction/block/slot/jump-table IDs
    /// ([`MachFunction::admit_id_counters`]) before the first pass and after
    /// the last, and marks each pass entry so that the pass's first
    /// allocation re-derives them before issuing any ID
    /// ([`MachFunction::require_id_admission_before_allocation`]). It stops at
    /// the first refusal and names where it happened: no allocator then issues
    /// an ID inside a pass from a counter that was not re-derived after the
    /// pass began. A production caller must treat `Err` as a fatal compile
    /// error; no pass ran after the refused one.
    pub id_admission: Result<(), MachIdRefusal>,
    /// Per-pass translation-validation verdicts for this run
    /// ([`crate::pass_validation`]). Empty when validation is off.
    pub pass_validation: PassValidationSummary,
}

impl Default for PassStats {
    fn default() -> Self {
        Self {
            runs: Vec::new(),
            changed_runs: Vec::new(),
            changes: 0,
            iterations: 0,
            proof_optimization_certificates: Vec::new(),
            certified_pass_runs: Vec::new(),
            kernel_recheck: Ok(()),
            id_admission: Ok(()),
            pass_validation: PassValidationSummary::default(),
        }
    }
}

impl PassStats {
    /// Empty statistics for `passes`, every run and change count zero.
    fn for_passes(
        passes: &[Box<dyn MachinePass>],
        iterations: u32,
        validation: PassValidationConfig,
    ) -> Self {
        let names = || {
            passes
                .iter()
                .map(|pass| (pass.name().to_string(), 0))
                .collect()
        };
        Self {
            runs: names(),
            changed_runs: names(),
            iterations,
            pass_validation: PassValidationSummary::new(validation),
            ..Self::default()
        }
    }

    /// How many runs of the pass named `name` reported a change, or `None`
    /// when no pass of that name was scheduled.
    pub fn changed_run_count(&self, name: &str) -> Option<u32> {
        let mut found = None;
        for (pass, count) in &self.changed_runs {
            if pass == name {
                found = Some(found.unwrap_or(0) + count);
            }
        }
        found
    }

    /// Total number of individual pass executions across all iterations.
    ///
    /// For a single-iteration run this equals the number of registered passes.
    /// During fixpoint iteration it can be smaller than `passes * iterations`
    /// when the driver skips a deterministic pass that already declined the
    /// current, bit-identical function state.
    pub fn total_pass_runs(&self) -> usize {
        self.runs.iter().map(|(_, count)| *count as usize).sum()
    }

    /// The Sentinel S4 fail-closed re-check verdict for kernel-authorized
    /// guard eliminations across this run. `Ok(())` when no kernel-gated
    /// elimination occurred or all eliminations independently re-justified.
    pub fn kernel_recheck(&self) -> Result<(), String> {
        self.kernel_recheck.clone()
    }

    /// The L10-P5 identity-admission verdict for this run (see
    /// [`PassStats::id_admission`]).
    pub fn id_admission(&self) -> Result<(), MachIdRefusal> {
        self.id_admission.clone()
    }
}

/// L10-P5 admission before the first pass of a driver runs. The refusal names
/// the entry of the pass that would have run first.
fn admit_ids_at_entry(
    func: &mut MachFunction,
    passes: &[Box<dyn MachinePass>],
) -> Result<(), MachIdRefusal> {
    func.admit_id_counters_at(|| match passes.first() {
        Some(pass) => format!("entry of pass `{}`", pass.name()),
        None => "entry of an empty pass manager".to_string(),
    })
}

/// L10-P5: the verdict of `pass`'s allocation-time admission. Its entry
/// marked the function, so its first allocation re-derived every live
/// identity; a refusal there is sticky and is reported here, at the pass's
/// exit, before anything else reads the function.
fn admitted_pass_allocations(
    func: &MachFunction,
    pass: &dyn MachinePass,
    iteration: u32,
) -> Result<(), MachIdRefusal> {
    match func.id_admission_refusal() {
        None => Ok(()),
        Some(error) => Err(MachIdRefusal {
            function: func.name.clone(),
            boundary: format!(
                "the first allocation in pass `{}` (iteration {iteration})",
                pass.name()
            ),
            error,
        }),
    }
}

/// L10-P5 admission after the last pass of a driver ran: the function leaves
/// the pass manager re-derived, whichever passes allocated.
fn admit_ids_at_exit(
    func: &mut MachFunction,
    last: Option<&dyn MachinePass>,
) -> Result<(), MachIdRefusal> {
    func.admit_id_counters_at(|| match last {
        Some(pass) => format!("pass-manager exit (after pass `{}`)", pass.name()),
        None => "pass-manager exit".to_string(),
    })
}

/// Manages and executes a pipeline of optimization passes.
///
/// Passes are run in insertion order. The pass manager supports both
/// single-run and fixed-point iteration modes.
pub struct PassManager {
    passes: Vec<Box<dyn MachinePass>>,
    proof_optimization_metadata: ProofOptimizationMetadata,
    boundary_observer: Option<PassBoundaryObserver>,
    validation: PassValidationConfig,
    /// Record a [`crate::pass_validation::PassTransition`] for every run that
    /// changes the function's interface.
    transitions: Option<FunctionInterfaceDigest>,
}

/// A boundary the pass manager admitted (L10-P5), as reported to a
/// [`PassBoundaryObserver`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PassBoundary<'a> {
    /// Before the first pass, after the entry admission.
    Entry,
    /// After `pass` ran in `iteration` (1-based) and its allocations were
    /// admitted.
    AfterPass {
        /// The pass's name.
        pass: &'a str,
        /// The fixpoint iteration (1 for the single-run drivers).
        iteration: u32,
    },
    /// After the last pass, after the exit admission.
    Exit,
}

/// Read-only observer of every boundary a driver admitted: an audit and test
/// hook (the identity-freshness property tests use it). It runs only on
/// admitted boundaries and cannot change the function.
pub type PassBoundaryObserver = Box<dyn FnMut(&MachFunction, PassBoundary<'_>)>;

fn should_time_passes() -> bool {
    // Cached once: the env var is read a single time for the process lifetime, so
    // the hot path (timing OFF, the default) is a cheap atomic load rather than a
    // syscall per pass start/end.
    use std::sync::OnceLock;
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("TRUST_CG_TIME_PASSES").is_some())
}

fn function_shape(func: &MachFunction) -> (usize, usize) {
    let blocks = func.block_order.len();
    let insts = func
        .block_order
        .iter()
        .map(|&block_id| func.block(block_id).insts.len())
        .sum();
    (blocks, insts)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CfgFingerprint(u64);

/// Digest of the function's CFG shape.
///
/// The digest is only a hint for when the driver drops cached analyses eagerly:
/// [`AnalysisCache`] compares the exact graph inputs on every lookup, so a
/// spurious match or mismatch changes cache statistics, never an analysis.
/// That is why a fast non-cryptographic hasher is enough.
fn cfg_fingerprint(func: &MachFunction) -> CfgFingerprint {
    let mut hasher = crate::fast_hash::FxHasher::default();

    func.entry.hash(&mut hasher);
    func.block_order.hash(&mut hasher);
    func.blocks.len().hash(&mut hasher);

    for (idx, block) in func.blocks.iter().enumerate() {
        (idx as u32).hash(&mut hasher);
        block.preds.hash(&mut hasher);
        block.succs.hash(&mut hasher);
        cfg_terminators_hash(func, block.insts.as_slice(), &mut hasher);
    }

    CfgFingerprint(hasher.finish())
}

fn cfg_terminators_hash<H: Hasher>(
    func: &MachFunction,
    insts: &[trust_cg_ir::InstId],
    state: &mut H,
) {
    let mut count = 0usize;
    for &inst_id in insts {
        // A block naming an instruction past the arena is a function the
        // L10-P5 admission refuses by name; hashing a marker keeps this
        // fingerprint from panicking first.
        let Some(inst) = func.insts.get(inst_id.0 as usize) else {
            u32::MAX.hash(state);
            continue;
        };
        if !inst.is_branch() && !inst.is_terminator() {
            continue;
        }

        count += 1;
        inst.is_branch().hash(state);
        inst.is_unconditional_branch().hash(state);
        inst.is_conditional_branch().hash(state);
        inst.is_return().hash(state);
        inst.is_terminator().hash(state);
        (insts.last() == Some(&inst_id)).hash(state);

        let mut target_count = 0usize;
        for operand in &inst.operands {
            if let MachOperand::Block(target) = operand {
                target_count += 1;
                target.hash(state);
            }
        }
        target_count.hash(state);
    }
    count.hash(state);
}

/// Returns the AFTER fingerprint so driver loops can keep a cached "current"
/// fingerprint instead of recomputing one before every pass invocation.
///
/// The cached value is valid across a pass that reported `changed = false`
/// because such a pass did not mutate the function — the same contract the
/// eager scheme relied on, since the before-fingerprint was only ever consulted
/// for passes that reported `changed = true`. A false unchanged report can
/// leave this driver's fingerprint stale; analysis accessors independently
/// compare the exact graph before returning cached results.
fn update_cache_after_changed_pass(
    func: &MachFunction,
    cache: &mut AnalysisCache,
    before_cfg: CfgFingerprint,
) -> CfgFingerprint {
    let after_cfg = cfg_fingerprint(func);
    if before_cfg == after_cfg {
        cache.preserve_for_unchanged_cfg();
    } else {
        cache.invalidate();
    }
    after_cfg
}

/// Label for the per-pass BOOKKEEPING that used to be timed as part of the pass
/// body. `collect_*` fold into a `PassStats` that outlives the function, so a
/// cost proportional to module size was being charged to whichever pass happened
/// to run — making every pass look equally quadratic on a many-function module.
/// Timing it separately is what distinguishes "this pass is slow" from "the
/// per-run bookkeeping is slow".
fn bookkeeping_name(pass_name: &str) -> String {
    format!("{pass_name}::bookkeeping")
}

/// The `(pass, pass::bookkeeping)` label pair for one pass invocation, built
/// ONLY when a consumer is actually enabled.
///
/// Both labels are consumed exclusively by env-gated diagnostics: the per-pass
/// timing log (`TRUST_CG_TIME_PASSES`), the MIR dump (`TRUST_CG_DUMP_MIR`) and
/// the changed-claim checker (`TCG_DIAG_CHANGED`). Building them
/// unconditionally cost three heap allocations per pass invocation —
/// `pass.name().to_string()` plus two `format!("{name}::bookkeeping")` calls,
/// the second of which re-formatted a string the first had already built — on
/// EVERY compile, with every consumer off by default. An empty program runs
/// 1794 pass invocations across its 14 std-startup functions, so that is ~5.4k
/// allocations formatted and dropped without ever being read.
///
/// Returns empty strings when no consumer is enabled; `log_pass_start` returns
/// `None` in that case and `log_pass_end` short-circuits on it, and the dump /
/// diag `eprintln!`s are behind their own flags, so the labels are never
/// observed. Purely an allocation elision: no pass is run, skipped, or ordered
/// differently, so the emitted object is byte-identical.
fn pass_labels(pass: &dyn MachinePass, want: bool) -> (String, String) {
    if !want {
        return (String::new(), String::new());
    }
    let name = pass.name().to_string();
    let bk = bookkeeping_name(&name);
    (name, bk)
}

/// Cached `TCG_DIAG_CHANGED` flag: read the environment once per process so
/// the default-off path costs one branch per pass run, not a getenv.
fn diag_changed_enabled() -> bool {
    use std::sync::OnceLock;
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("TCG_DIAG_CHANGED").is_some())
}

/// Buffered sink for `[trust-cg-time-pass]` records.
///
/// This logger fires PER PASS, PER ITERATION, PER FUNCTION — with ~148 passes
/// in the O2 ladder that is thousands of events per compile, and each one did a
/// `function_shape` walk of the whole function plus an unbuffered `eprintln!`
/// write syscall. All of it landed inside the enclosing `opt-pass-manager` and
/// `optimization` phase timers.
///
/// That is why enabling `TRUST_CG_TIME_PASSES` alongside
/// `TRUST_CG_TIME_PIPELINE` once reported 167ms of phases inside a ~120ms
/// compile, including a fictional 147ms "opt-pass-manager". Records now
/// accumulate per thread and flush when the thread ends.
struct PassTimeLog {
    lines: Vec<String>,
}

impl PassTimeLog {
    fn flush(&mut self) {
        if self.lines.is_empty() {
            return;
        }
        use std::io::Write;
        let stderr = std::io::stderr();
        let mut out = stderr.lock();
        for line in self.lines.drain(..) {
            let _ = writeln!(out, "{line}");
        }
        let _ = out.flush();
    }
}

impl Drop for PassTimeLog {
    fn drop(&mut self) {
        self.flush();
    }
}

thread_local! {
    static PASS_TIME_LOG: std::cell::RefCell<PassTimeLog> =
        const { std::cell::RefCell::new(PassTimeLog { lines: Vec::new() }) };
}

fn pass_time_record(line: String) {
    PASS_TIME_LOG.with(|log| log.borrow_mut().lines.push(line));
}

/// Flush pass timings accumulated by the calling thread.
///
/// Reusable compiler worker threads call this at a task boundary because their
/// thread-local destructors do not run until the process exits.
#[doc(hidden)]
pub fn flush_current_thread_pass_time_log() {
    if should_time_passes() {
        PASS_TIME_LOG.with(|log| log.borrow_mut().flush());
    }
}

fn log_pass_start(func: &MachFunction, iteration: u32, pass_name: &str) -> Option<Instant> {
    if !should_time_passes() {
        return None;
    }
    // No `function_shape` here: it walks the whole function, once per pass per
    // iteration. The END record reports the post-pass shape, which is the
    // figure that actually says what the pass did.
    pass_time_record(format!(
        "[trust-cg-time-pass] start func={} iter={iteration} pass={pass_name}",
        func.name
    ));
    Some(Instant::now())
}

fn log_pass_end(
    func: &MachFunction,
    iteration: u32,
    pass_name: &str,
    changed: bool,
    start: Option<Instant>,
) {
    let Some(start) = start else {
        return;
    };
    // Clock first: the shape walk and the record below are instrumentation.
    let elapsed_us = start.elapsed().as_micros();
    let (blocks, insts) = function_shape(func);
    pass_time_record(format!(
        "[trust-cg-time-pass] end func={} iter={iteration} pass={pass_name} changed={changed} \
         elapsed_us={elapsed_us} blocks={blocks} insts={insts}",
        func.name
    ));
}

fn collect_proof_optimization_certificates(stats: &mut PassStats, pass: &mut dyn MachinePass) {
    stats
        .proof_optimization_certificates
        .extend(pass.take_proof_optimization_certificates());
}

fn collect_certified_pass_runs(stats: &mut PassStats, pass: &mut dyn MachinePass) {
    stats
        .certified_pass_runs
        .extend(pass.take_certified_pass_runs());
}

/// Sentinel S4: fold the boxed pass's independent re-check verdict into the
/// run-wide [`PassStats::kernel_recheck`]. The first rejection wins (the
/// production caller aborts the compile on it); subsequent verdicts cannot
/// clear an already-recorded rejection.
fn collect_kernel_recheck(stats: &mut PassStats, pass: &dyn MachinePass) {
    if stats.kernel_recheck.is_err() {
        return;
    }
    stats.kernel_recheck = pass.recheck_kernel_eliminations();
}

impl PassManager {
    /// Create an empty pass manager.
    pub fn new() -> Self {
        Self {
            passes: Vec::new(),
            proof_optimization_metadata: ProofOptimizationMetadata::new(),
            boundary_observer: None,
            validation: PassValidationConfig::off(),
            transitions: None,
        }
    }

    /// Validate every pass run under `config` ([`crate::pass_validation`]).
    /// The verdicts land in [`PassStats::pass_validation`]. A new pass
    /// manager validates nothing.
    pub fn set_pass_validation(&mut self, config: PassValidationConfig) {
        self.validation = config;
    }

    /// Validate every pass run under `config` (builder pattern).
    pub fn with_pass_validation(mut self, config: PassValidationConfig) -> Self {
        self.set_pass_validation(config);
        self
    }

    /// Record every run that changes the function's interface under
    /// `digest` in [`PassValidationSummary::transitions`], validating each for
    /// the record ([`crate::pass_validation`]'s transitions); `None` records
    /// none.
    pub fn set_transition_digest(&mut self, digest: Option<FunctionInterfaceDigest>) {
        self.transitions = digest;
    }

    /// Report every admitted boundary of later runs to `observer` (builder
    /// pattern).
    pub fn with_boundary_observer(mut self, observer: PassBoundaryObserver) -> Self {
        self.boundary_observer = Some(observer);
        self
    }

    /// Take the registered passes in pipeline order, e.g. to drive one pass
    /// of a built pipeline on its own.
    pub fn into_passes(self) -> Vec<Box<dyn MachinePass>> {
        self.passes
    }

    /// Add a pass to the end of the pipeline.
    pub fn add_pass(&mut self, mut pass: Box<dyn MachinePass>) {
        pass.set_proof_optimization_metadata(&self.proof_optimization_metadata);
        self.passes.push(pass);
    }

    /// Add a pass to the end of the pipeline (builder pattern).
    pub fn with_pass(mut self, mut pass: Box<dyn MachinePass>) -> Self {
        pass.set_proof_optimization_metadata(&self.proof_optimization_metadata);
        self.passes.push(pass);
        self
    }

    /// Configure proof-optimization metadata for all current and future passes.
    pub fn set_proof_optimization_metadata(&mut self, metadata: ProofOptimizationMetadata) {
        self.proof_optimization_metadata = metadata;
        for pass in &mut self.passes {
            pass.set_proof_optimization_metadata(&self.proof_optimization_metadata);
        }
    }

    /// Configure proof-optimization metadata (builder pattern).
    pub fn with_proof_optimization_metadata(mut self, metadata: ProofOptimizationMetadata) -> Self {
        self.set_proof_optimization_metadata(metadata);
        self
    }

    /// Returns the number of registered passes.
    pub fn num_passes(&self) -> usize {
        self.passes.len()
    }

    /// Returns registered pass names in pipeline order.
    pub fn pass_names(&self) -> Vec<&str> {
        self.passes.iter().map(|pass| pass.name()).collect()
    }

    /// Run all passes once in order.
    ///
    /// Returns whether any pass modified the function, or the first refused
    /// L10-P5 identity admission (no pass runs after it).
    pub fn run_once(&mut self, func: &mut MachFunction) -> Result<bool, MachIdRefusal> {
        admit_ids_at_entry(func, &self.passes)?;
        if let Some(observe) = self.boundary_observer.as_mut() {
            observe(func, PassBoundary::Entry);
        }
        let mut changed = false;
        for pass in &mut self.passes {
            func.require_id_admission_before_allocation();
            if pass.run(func) {
                changed = true;
            }
            admitted_pass_allocations(func, pass.as_ref(), 1)?;
            if let Some(observe) = self.boundary_observer.as_mut() {
                observe(
                    func,
                    PassBoundary::AfterPass {
                        pass: pass.name(),
                        iteration: 1,
                    },
                );
            }
        }
        admit_ids_at_exit(func, self.passes.last().map(|pass| pass.as_ref()))?;
        if let Some(observe) = self.boundary_observer.as_mut() {
            observe(func, PassBoundary::Exit);
        }
        Ok(changed)
    }

    /// Run all passes once with access to a provenance map.
    ///
    /// Returns whether any pass modified the function, or the first refused
    /// L10-P5 identity admission (no pass runs after it).
    pub fn run_once_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> Result<bool, MachIdRefusal> {
        admit_ids_at_entry(func, &self.passes)?;
        if let Some(observe) = self.boundary_observer.as_mut() {
            observe(func, PassBoundary::Entry);
        }
        let mut changed = false;
        for pass in &mut self.passes {
            func.require_id_admission_before_allocation();
            if pass.run_with_provenance(func, provenance) {
                changed = true;
            }
            admitted_pass_allocations(func, pass.as_ref(), 1)?;
            if let Some(observe) = self.boundary_observer.as_mut() {
                observe(
                    func,
                    PassBoundary::AfterPass {
                        pass: pass.name(),
                        iteration: 1,
                    },
                );
            }
        }
        admit_ids_at_exit(func, self.passes.last().map(|pass| pass.as_ref()))?;
        if let Some(observe) = self.boundary_observer.as_mut() {
            observe(func, PassBoundary::Exit);
        }
        Ok(changed)
    }

    /// Run all passes repeatedly until no pass reports changes, or
    /// `max_iterations` is reached.
    ///
    /// Uses an [`AnalysisCache`] to avoid redundant domtree/loop analysis
    /// recomputation within each iteration. Changed passes invalidate the
    /// cache only when their CFG fingerprint changes.
    ///
    /// Returns statistics about the run.
    pub fn run_to_fixpoint(&mut self, func: &mut MachFunction, max_iterations: u32) -> PassStats {
        let mut stats = PassStats::for_passes(&self.passes, 0, self.validation);
        let mut validation =
            PassValidationHook::new(self.validation).with_transitions(self.transitions);
        // L10-P5: refuse a stale counter before anything indexes the arenas.
        if let Err(refusal) = admit_ids_at_entry(func, &self.passes) {
            stats.id_admission = Err(refusal);
            return stats;
        }
        if let Some(observe) = self.boundary_observer.as_mut() {
            observe(func, PassBoundary::Entry);
        }

        let should_dump = should_dump_mir(func);
        if should_dump {
            eprintln!("=== before passes [func={}] ===", func.name);
            dump_function(func);
        }

        // DETERMINISTIC NO-OP SKIP. 81% of all pass-run time (99.3ms of
        // 122.6ms at many_fns n=200) was re-scans that found nothing: the
        // fixpoint's iteration 2 re-runs every pass, but a pass re-run on a
        // function that has NOT mutated since that pass last returned
        // `changed = false` is a deterministic no-op — same input, same pass,
        // same (absent) effect. Track a mutation epoch (bumped on every
        // changed=true) and each pass's last no-change epoch; skip when equal.
        // A pass that DID change the function stays eligible (it has not seen
        // its own output), exactly matching the fixpoint's existing semantics.
        // Output preservation rests on pass determinism, which byte-identity
        // over the corpus already enforces for every change this session.
        let mut mutation_epoch: u64 = 0;
        let mut nochange_epoch: Vec<Option<u64>> = vec![None; self.passes.len()];
        // The pass that ran last, named by the exit admission.
        let mut last_run: Option<usize> = None;
        // Every label consumer is env-gated and off by default; see `pass_labels`.
        // The TCG_DIAG_CHANGED path prints `pass_name` too, so it counts as a
        // consumer here.
        let want_labels = should_time_passes() || should_dump || diag_changed_enabled();

        // The CFG analyses (dominators, loops) are pure functions of the CFG, and
        // `update_cache_after_changed_pass` already keeps them across passes
        // whose CFG fingerprint is unchanged. Nothing runs between one
        // iteration's end and the next one's start, so the cache is carried
        // across iterations too instead of being rebuilt — same analyses, same
        // answers, one dominator/loop computation fewer per iteration.
        let mut cache = AnalysisCache::new();
        for iteration in 0..max_iterations {
            stats.iterations = iteration + 1;
            let mut any_changed = false;
            // One fingerprint maintained across pass runs. Computing it before
            // EVERY invocation was pure waste for the changed=false majority —
            // measured at 15.6 -> 27.5ms of non-pass-body optimization-phase
            // overhead on the many_fns scaling shape.
            let mut current_cfg = cfg_fingerprint(func);

            for (i, pass) in self.passes.iter_mut().enumerate() {
                if nochange_epoch[i] == Some(mutation_epoch) {
                    // Function unchanged since this pass last found nothing:
                    // re-running it is a proven no-op.
                    continue;
                }
                stats.runs[i].1 += 1;
                let (pass_name, bk_name) = pass_labels(pass.as_ref(), want_labels);
                let before_cfg = current_cfg;
                // DIAGNOSTIC (default off, `TCG_DIAG_CHANGED=1`): verify each
                // pass's claimed change against actual function content. A
                // pass that reports `changed` without changing anything defeats
                // the no-op skip (every claim re-arms all passes) and fakes
                // convergence pressure; this catches it red-handed. Ruled out
                // as the cause of the 4-iteration v2_memfill convergence tail
                // on 2026-08-13 (zero false claims — the tail is genuine
                // progressive enabling), kept for the next suspect.
                let diag_pre = diag_changed_enabled().then(|| format!("{func:?}"));
                let snapshot = validation.snapshot(pass.name(), func);
                let timer = log_pass_start(func, iteration + 1, &pass_name);
                func.require_id_admission_before_allocation();
                let pass_changed = pass.run_with_analyses(func, &mut cache);
                log_pass_end(func, iteration + 1, &pass_name, pass_changed, timer);
                last_run = Some(i);
                // L10-P5: before the pass validator, the CFG fingerprint or any
                // dump reads it.
                if let Err(refusal) = admitted_pass_allocations(func, pass.as_ref(), iteration + 1)
                {
                    stats.id_admission = Err(refusal);
                    return stats;
                }
                validation.conclude(
                    pass.name(),
                    snapshot,
                    pass_changed,
                    func,
                    &mut stats.pass_validation,
                );
                if let Some(observe) = self.boundary_observer.as_mut() {
                    observe(
                        func,
                        PassBoundary::AfterPass {
                            pass: pass.name(),
                            iteration: iteration + 1,
                        },
                    );
                }
                if let Some(pre) = diag_pre {
                    let post = format!("{func:?}");
                    if pass_changed && pre == post {
                        eprintln!(
                            "TCG_DIAG_CHANGED FALSE-CHANGED iter={} pass={} func={}",
                            iteration + 1,
                            pass_name,
                            func.name
                        );
                    }
                    // The dangerous direction: a pass that MUTATED the function
                    // but reported no change. The epoch skip above would then
                    // leave later passes running on stale assumptions, and the
                    // fixpoint could stop early.
                    if !pass_changed && pre != post {
                        eprintln!(
                            "TCG_DIAG_CHANGED SILENT-MUTATION iter={} pass={} func={}",
                            iteration + 1,
                            pass_name,
                            func.name
                        );
                    }
                }
                let bk = log_pass_start(func, iteration + 1, &bk_name);
                collect_proof_optimization_certificates(&mut stats, pass.as_mut());
                collect_certified_pass_runs(&mut stats, pass.as_mut());
                collect_kernel_recheck(&mut stats, pass.as_ref());
                log_pass_end(func, iteration + 1, &bk_name, false, bk);
                if pass_changed {
                    any_changed = true;
                    stats.changes += 1;
                    stats.changed_runs[i].1 += 1;
                    mutation_epoch += 1;
                    // The pass has not seen its own output; leave it eligible.
                    nochange_epoch[i] = None;
                    current_cfg = update_cache_after_changed_pass(func, &mut cache, before_cfg);
                    if should_dump {
                        eprintln!("=== after iter {} pass [{}] ===", iteration + 1, pass_name);
                        dump_function(func);
                    }
                } else if should_dump {
                    eprintln!(
                        "=== iter {} pass [{}] no changes ===",
                        iteration + 1,
                        pass_name
                    );
                }
                if !pass_changed {
                    nochange_epoch[i] = Some(mutation_epoch);
                }
            }

            if !any_changed {
                break;
            }
        }

        let last = last_run.map(|index| self.passes[index].as_ref());
        stats.id_admission = admit_ids_at_exit(func, last);
        if stats.id_admission.is_ok()
            && let Some(observe) = self.boundary_observer.as_mut()
        {
            observe(func, PassBoundary::Exit);
        }
        stats
    }

    /// Run all passes repeatedly with access to a provenance map.
    ///
    /// This is the provenance-aware companion to [`PassManager::run_to_fixpoint`].
    /// Existing passes remain valid because the default pass hook falls back to
    /// `run_with_analyses`.
    pub fn run_to_fixpoint_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
        max_iterations: u32,
    ) -> PassStats {
        let mut stats = PassStats::for_passes(&self.passes, 0, self.validation);
        let mut validation =
            PassValidationHook::new(self.validation).with_transitions(self.transitions);
        // L10-P5: refuse a stale counter before anything indexes the arenas.
        if let Err(refusal) = admit_ids_at_entry(func, &self.passes) {
            stats.id_admission = Err(refusal);
            return stats;
        }
        if let Some(observe) = self.boundary_observer.as_mut() {
            observe(func, PassBoundary::Entry);
        }

        let should_dump = should_dump_mir(func);
        if should_dump {
            eprintln!("=== before passes [func={}] ===", func.name);
            dump_function(func);
        }

        // DETERMINISTIC NO-OP SKIP. 81% of all pass-run time (99.3ms of
        // 122.6ms at many_fns n=200) was re-scans that found nothing: the
        // fixpoint's iteration 2 re-runs every pass, but a pass re-run on a
        // function that has NOT mutated since that pass last returned
        // `changed = false` is a deterministic no-op — same input, same pass,
        // same (absent) effect. Track a mutation epoch (bumped on every
        // changed=true) and each pass's last no-change epoch; skip when equal.
        // A pass that DID change the function stays eligible (it has not seen
        // its own output), exactly matching the fixpoint's existing semantics.
        // Output preservation rests on pass determinism, which byte-identity
        // over the corpus already enforces for every change this session.
        let mut mutation_epoch: u64 = 0;
        let mut nochange_epoch: Vec<Option<u64>> = vec![None; self.passes.len()];
        // The pass that ran last, named by the exit admission.
        let mut last_run: Option<usize> = None;
        // Every label consumer is env-gated and off by default; see `pass_labels`.
        let want_labels = should_time_passes() || should_dump;

        for iteration in 0..max_iterations {
            stats.iterations = iteration + 1;
            let mut any_changed = false;
            let mut cache = AnalysisCache::new();
            // One fingerprint maintained across pass runs. Computing it before
            // EVERY invocation was pure waste for the changed=false majority —
            // measured at 15.6 -> 27.5ms of non-pass-body optimization-phase
            // overhead on the many_fns scaling shape.
            let mut current_cfg = cfg_fingerprint(func);

            for (i, pass) in self.passes.iter_mut().enumerate() {
                if nochange_epoch[i] == Some(mutation_epoch) {
                    // Function unchanged since this pass last found nothing:
                    // re-running it is a proven no-op.
                    continue;
                }
                stats.runs[i].1 += 1;
                let (pass_name, bk_name) = pass_labels(pass.as_ref(), want_labels);
                let before_cfg = current_cfg;
                let snapshot = validation.snapshot(pass.name(), func);
                let timer = log_pass_start(func, iteration + 1, &pass_name);
                func.require_id_admission_before_allocation();
                let pass_changed =
                    pass.run_with_analyses_and_provenance(func, &mut cache, provenance);
                log_pass_end(func, iteration + 1, &pass_name, pass_changed, timer);
                last_run = Some(i);
                if let Err(refusal) = admitted_pass_allocations(func, pass.as_ref(), iteration + 1)
                {
                    stats.id_admission = Err(refusal);
                    return stats;
                }
                validation.conclude(
                    pass.name(),
                    snapshot,
                    pass_changed,
                    func,
                    &mut stats.pass_validation,
                );
                if let Some(observe) = self.boundary_observer.as_mut() {
                    observe(
                        func,
                        PassBoundary::AfterPass {
                            pass: pass.name(),
                            iteration: iteration + 1,
                        },
                    );
                }
                let bk = log_pass_start(func, iteration + 1, &bk_name);
                collect_proof_optimization_certificates(&mut stats, pass.as_mut());
                collect_certified_pass_runs(&mut stats, pass.as_mut());
                collect_kernel_recheck(&mut stats, pass.as_ref());
                log_pass_end(func, iteration + 1, &bk_name, false, bk);
                if pass_changed {
                    any_changed = true;
                    stats.changes += 1;
                    stats.changed_runs[i].1 += 1;
                    mutation_epoch += 1;
                    // The pass has not seen its own output; leave it eligible.
                    nochange_epoch[i] = None;
                    current_cfg = update_cache_after_changed_pass(func, &mut cache, before_cfg);
                    if should_dump {
                        eprintln!("=== after iter {} pass [{}] ===", iteration + 1, pass_name);
                        dump_function(func);
                    }
                } else if should_dump {
                    eprintln!(
                        "=== iter {} pass [{}] no changes ===",
                        iteration + 1,
                        pass_name
                    );
                }
                if !pass_changed {
                    nochange_epoch[i] = Some(mutation_epoch);
                }
            }

            if !any_changed {
                break;
            }
        }

        let last = last_run.map(|index| self.passes[index].as_ref());
        stats.id_admission = admit_ids_at_exit(func, last);
        if stats.id_admission.is_ok()
            && let Some(observe) = self.boundary_observer.as_mut()
        {
            observe(func, PassBoundary::Exit);
        }
        stats
    }

    /// Run all passes once, collecting per-pass statistics.
    ///
    /// Uses an [`AnalysisCache`] to avoid redundant domtree/loop analysis
    /// recomputation across passes.
    pub fn run_once_with_stats(&mut self, func: &mut MachFunction) -> PassStats {
        let mut stats = PassStats::for_passes(&self.passes, 1, self.validation);
        let mut validation =
            PassValidationHook::new(self.validation).with_transitions(self.transitions);
        // L10-P5: refuse a stale counter before anything indexes the arenas.
        if let Err(refusal) = admit_ids_at_entry(func, &self.passes) {
            stats.id_admission = Err(refusal);
            return stats;
        }
        if let Some(observe) = self.boundary_observer.as_mut() {
            observe(func, PassBoundary::Entry);
        }

        let should_dump = should_dump_mir(func);
        if should_dump {
            eprintln!("=== before passes [func={}] ===", func.name);
            dump_function(func);
        }

        // Every label consumer is env-gated and off by default; see `pass_labels`.
        let want_labels = should_time_passes() || should_dump;
        let mut cache = AnalysisCache::new();
        // See the fixpoint drivers: one fingerprint maintained across pass
        // runs instead of one recompute per invocation.
        let mut current_cfg = cfg_fingerprint(func);
        for (i, pass) in self.passes.iter_mut().enumerate() {
            stats.runs[i].1 = 1;
            let (pass_name, bk_name) = pass_labels(pass.as_ref(), want_labels);
            let before_cfg = current_cfg;
            let snapshot = validation.snapshot(pass.name(), func);
            let timer = log_pass_start(func, 1, &pass_name);
            func.require_id_admission_before_allocation();
            let pass_changed = pass.run_with_analyses(func, &mut cache);
            log_pass_end(func, 1, &pass_name, pass_changed, timer);
            if let Err(refusal) = admitted_pass_allocations(func, pass.as_ref(), 1) {
                stats.id_admission = Err(refusal);
                return stats;
            }
            validation.conclude(
                pass.name(),
                snapshot,
                pass_changed,
                func,
                &mut stats.pass_validation,
            );
            if let Some(observe) = self.boundary_observer.as_mut() {
                observe(
                    func,
                    PassBoundary::AfterPass {
                        pass: pass.name(),
                        iteration: 1,
                    },
                );
            }
            let bk = log_pass_start(func, 1, &bk_name);
            collect_proof_optimization_certificates(&mut stats, pass.as_mut());
            collect_certified_pass_runs(&mut stats, pass.as_mut());
            collect_kernel_recheck(&mut stats, pass.as_ref());
            log_pass_end(func, 1, &bk_name, false, bk);
            if pass_changed {
                stats.changes += 1;
                stats.changed_runs[i].1 += 1;
                current_cfg = update_cache_after_changed_pass(func, &mut cache, before_cfg);
                if should_dump {
                    eprintln!("=== after pass [{}] ===", pass_name);
                    dump_function(func);
                }
            } else if should_dump {
                eprintln!("=== pass [{}] no changes ===", pass_name);
            }
        }

        let last = self.passes.last().map(|pass| pass.as_ref());
        stats.id_admission = admit_ids_at_exit(func, last);
        if stats.id_admission.is_ok()
            && let Some(observe) = self.boundary_observer.as_mut()
        {
            observe(func, PassBoundary::Exit);
        }
        stats
    }

    /// Run all passes once with provenance access, collecting per-pass stats.
    ///
    /// This is the provenance-aware companion to
    /// [`PassManager::run_once_with_stats`].
    pub fn run_once_with_stats_and_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> PassStats {
        let mut stats = PassStats::for_passes(&self.passes, 1, self.validation);
        let mut validation =
            PassValidationHook::new(self.validation).with_transitions(self.transitions);
        // L10-P5: refuse a stale counter before anything indexes the arenas.
        if let Err(refusal) = admit_ids_at_entry(func, &self.passes) {
            stats.id_admission = Err(refusal);
            return stats;
        }
        if let Some(observe) = self.boundary_observer.as_mut() {
            observe(func, PassBoundary::Entry);
        }

        let should_dump = should_dump_mir(func);
        if should_dump {
            eprintln!("=== before passes [func={}] ===", func.name);
            dump_function(func);
        }

        // Every label consumer is env-gated and off by default; see `pass_labels`.
        let want_labels = should_time_passes() || should_dump;
        let mut cache = AnalysisCache::new();
        // See the fixpoint drivers: one fingerprint maintained across pass
        // runs instead of one recompute per invocation.
        let mut current_cfg = cfg_fingerprint(func);
        for (i, pass) in self.passes.iter_mut().enumerate() {
            stats.runs[i].1 = 1;
            let (pass_name, bk_name) = pass_labels(pass.as_ref(), want_labels);
            let before_cfg = current_cfg;
            let snapshot = validation.snapshot(pass.name(), func);
            let timer = log_pass_start(func, 1, &pass_name);
            func.require_id_admission_before_allocation();
            let pass_changed = pass.run_with_analyses_and_provenance(func, &mut cache, provenance);
            log_pass_end(func, 1, &pass_name, pass_changed, timer);
            if let Err(refusal) = admitted_pass_allocations(func, pass.as_ref(), 1) {
                stats.id_admission = Err(refusal);
                return stats;
            }
            validation.conclude(
                pass.name(),
                snapshot,
                pass_changed,
                func,
                &mut stats.pass_validation,
            );
            if let Some(observe) = self.boundary_observer.as_mut() {
                observe(
                    func,
                    PassBoundary::AfterPass {
                        pass: pass.name(),
                        iteration: 1,
                    },
                );
            }
            let bk = log_pass_start(func, 1, &bk_name);
            collect_proof_optimization_certificates(&mut stats, pass.as_mut());
            collect_certified_pass_runs(&mut stats, pass.as_mut());
            collect_kernel_recheck(&mut stats, pass.as_ref());
            log_pass_end(func, 1, &bk_name, false, bk);
            if pass_changed {
                stats.changes += 1;
                stats.changed_runs[i].1 += 1;
                current_cfg = update_cache_after_changed_pass(func, &mut cache, before_cfg);
                if should_dump {
                    eprintln!("=== after pass [{}] ===", pass_name);
                    dump_function(func);
                }
            } else if should_dump {
                eprintln!("=== pass [{}] no changes ===", pass_name);
            }
        }

        let last = self.passes.last().map(|pass| pass.as_ref());
        stats.id_admission = admit_ids_at_exit(func, last);
        if stats.id_admission.is_ok()
            && let Some(observe) = self.boundary_observer.as_mut()
        {
            observe(func, PassBoundary::Exit);
        }
        stats
    }
}

impl Default for PassManager {
    fn default() -> Self {
        Self::new()
    }
}

/// Dev hook (#366 bisect): when TRUST_CG_DUMP_MIR is set and matches the
/// function name, emit MIR before passes and after each changed pass.
fn should_dump_mir(func: &MachFunction) -> bool {
    let dump_name = std::env::var("TRUST_CG_DUMP_MIR").unwrap_or_default();
    !dump_name.is_empty() && func.name.contains(&dump_name)
}

/// Dev-only MIR dumper used by the TRUST_CG_DUMP_MIR debug hook.
fn dump_function(func: &MachFunction) {
    for block_id in &func.block_order {
        let block = func.block(*block_id);
        eprintln!("  block {:?}  (succs: {:?})", block_id, block.succs);
        for inst_id in &block.insts {
            let inst = func.inst(*inst_id);
            eprintln!("    {:?}: {:?}  {:?}", inst_id, inst.opcode, inst.operands);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proof_opts::ProofOptimization;
    use std::{cell::RefCell, rc::Rc};
    use trust_cg_ir::{
        AArch64Opcode, BlockId, InstId, MachInst, MachOperand, PassId, ProofAnnotation, RegClass,
        Signature, TransformKind, TrustIrInstId, VReg,
    };

    /// A no-op pass for testing.
    struct NoOpPass;

    impl MachinePass for NoOpPass {
        fn name(&self) -> &str {
            "no-op"
        }
        fn run(&mut self, _func: &mut MachFunction) -> bool {
            false
        }
    }

    /// A pass that reports a change exactly N times, then stops.
    struct CountingPass {
        remaining: u32,
    }

    impl MachinePass for CountingPass {
        fn name(&self) -> &str {
            "counting"
        }
        fn run(&mut self, _func: &mut MachFunction) -> bool {
            if self.remaining > 0 {
                self.remaining -= 1;
                true
            } else {
                false
            }
        }
    }

    /// A pass that records a provenance-preserving in-place rewrite.
    struct ProvenanceMarkingPass {
        inst: InstId,
    }

    impl MachinePass for ProvenanceMarkingPass {
        fn name(&self) -> &str {
            "provenance-mark"
        }

        fn run(&mut self, _func: &mut MachFunction) -> bool {
            false
        }

        fn run_with_provenance(
            &mut self,
            _func: &mut MachFunction,
            provenance: &mut ProvenanceMap,
        ) -> bool {
            provenance.record_in_place_transform(self.inst, PassId::new(self.name()));
            true
        }

        fn run_with_analyses_and_provenance(
            &mut self,
            _func: &mut MachFunction,
            _analyses: &mut AnalysisCache,
            provenance: &mut ProvenanceMap,
        ) -> bool {
            self.run_with_provenance(_func, provenance)
        }
    }

    struct AnalysisProbePass {
        samples: Rc<RefCell<Vec<AnalysisCacheStats>>>,
    }

    impl MachinePass for AnalysisProbePass {
        fn name(&self) -> &str {
            "analysis-probe"
        }

        fn run(&mut self, _func: &mut MachFunction) -> bool {
            false
        }

        fn run_with_analyses(
            &mut self,
            func: &mut MachFunction,
            analyses: &mut AnalysisCache,
        ) -> bool {
            let _ = analyses.domtree(func).rpo_order().len();
            let _ = analyses.loop_analysis(func).is_empty();
            self.samples.borrow_mut().push(analyses.stats());
            false
        }
    }

    struct ImmediateRewritePass {
        inst: InstId,
    }

    impl MachinePass for ImmediateRewritePass {
        fn name(&self) -> &str {
            "imm-rewrite"
        }

        fn run(&mut self, func: &mut MachFunction) -> bool {
            let inst = func.inst_mut(self.inst);
            assert_eq!(inst.opcode, AArch64Opcode::AddRI);
            inst.operands[2] = MachOperand::Imm(42);
            true
        }
    }

    struct BranchRedirectPass {
        branch: InstId,
        from: BlockId,
        old_target: BlockId,
        new_target: BlockId,
    }

    impl MachinePass for BranchRedirectPass {
        fn name(&self) -> &str {
            "branch-redirect"
        }

        fn run(&mut self, func: &mut MachFunction) -> bool {
            let mut redirected = false;
            for operand in &mut func.inst_mut(self.branch).operands {
                if let MachOperand::Block(target) = operand {
                    assert_eq!(*target, self.old_target);
                    *target = self.new_target;
                    redirected = true;
                }
            }
            assert!(redirected);

            {
                let succs = &mut func.block_mut(self.from).succs;
                succs.retain(|&succ| succ != self.old_target);
                if !succs.contains(&self.new_target) {
                    succs.push(self.new_target);
                }
            }

            func.block_mut(self.old_target)
                .preds
                .retain(|&pred| pred != self.from);
            if !func.block(self.new_target).preds.contains(&self.from) {
                func.block_mut(self.new_target).preds.push(self.from);
            }

            true
        }
    }

    fn make_empty_func() -> MachFunction {
        MachFunction::new("test".to_string(), Signature::new(vec![], vec![]))
    }

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn imm(value: i64) -> MachOperand {
        MachOperand::Imm(value)
    }

    fn make_no_overflow_func() -> MachFunction {
        let mut func = MachFunction::new(
            "pass_manager_proof".to_string(),
            Signature::new(vec![], vec![]),
        );
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);
        let trap = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(BlockId(1))],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let block = func.entry;
        for inst in [adds, trap, ret] {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
        }
        func.create_block();
        func
    }

    fn make_analysis_func() -> (MachFunction, InstId) {
        let mut func = make_empty_func();
        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(1), vreg(0), imm(1)],
        ));
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(func.entry, add);
        func.append_inst(func.entry, ret);
        (func, add)
    }

    fn make_redirectable_branch_func() -> (MachFunction, InstId, BlockId, BlockId, BlockId) {
        let mut func = make_empty_func();
        let old_target = func.create_block();
        let new_target = func.create_block();
        let entry = func.entry;

        let branch = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(old_target)],
        ));
        let old_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        let new_ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));

        func.append_inst(entry, branch);
        func.append_inst(old_target, old_ret);
        func.append_inst(new_target, new_ret);
        func.add_edge(entry, old_target);

        (func, branch, entry, old_target, new_target)
    }

    #[test]
    fn test_empty_pass_manager() {
        let mut pm = PassManager::new();
        let mut func = make_empty_func();
        assert_eq!(pm.run_once(&mut func), Ok(false));
    }

    #[test]
    fn test_noop_pass() {
        let mut pm = PassManager::new();
        pm.add_pass(Box::new(NoOpPass));
        let mut func = make_empty_func();
        assert_eq!(pm.run_once(&mut func), Ok(false));
    }

    #[test]
    fn test_fixpoint_convergence() {
        let mut pm = PassManager::new();
        pm.add_pass(Box::new(CountingPass { remaining: 3 }));
        let mut func = make_empty_func();

        let stats = pm.run_to_fixpoint(&mut func, 10);
        // Should run 4 iterations: 3 with changes + 1 that detects fixpoint
        assert_eq!(stats.iterations, 4);
        assert_eq!(stats.changes, 3);
    }

    /// `changed_runs` counts, per pass and in `runs` order, the runs that
    /// reported a change, in every driver; `changed_run_count` separates a
    /// scheduled pass that never changed (`Some(0)`) from an unscheduled one
    /// (`None`).
    #[test]
    fn changed_runs_count_each_pass_in_every_driver() {
        fn manager() -> PassManager {
            PassManager::new()
                .with_pass(Box::new(NoOpPass))
                .with_pass(Box::new(CountingPass { remaining: 2 }))
        }
        let expected_once = vec![("no-op".to_string(), 0), ("counting".to_string(), 1)];
        let expected_fixpoint = vec![("no-op".to_string(), 0), ("counting".to_string(), 2)];

        let stats = manager().run_once_with_stats(&mut make_empty_func());
        assert_eq!(stats.changed_runs, expected_once);
        let mut provenance = ProvenanceMap::new();
        let stats =
            manager().run_once_with_stats_and_provenance(&mut make_empty_func(), &mut provenance);
        assert_eq!(stats.changed_runs, expected_once);

        let stats = manager().run_to_fixpoint(&mut make_empty_func(), 10);
        assert_eq!(stats.changed_runs, expected_fixpoint);
        assert_eq!(stats.changes, 2);
        let mut provenance = ProvenanceMap::new();
        let stats =
            manager().run_to_fixpoint_with_provenance(&mut make_empty_func(), &mut provenance, 10);
        assert_eq!(stats.changed_runs, expected_fixpoint);

        assert_eq!(stats.changed_run_count("counting"), Some(2));
        assert_eq!(stats.changed_run_count("no-op"), Some(0));
        assert_eq!(stats.changed_run_count("absent"), None);
        assert_eq!(
            stats
                .runs
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>(),
            stats
                .changed_runs
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_fixpoint_max_iterations() {
        let mut pm = PassManager::new();
        pm.add_pass(Box::new(CountingPass { remaining: 100 }));
        let mut func = make_empty_func();

        let stats = pm.run_to_fixpoint(&mut func, 5);
        assert_eq!(stats.iterations, 5);
        assert_eq!(stats.changes, 5);
    }

    #[test]
    fn test_builder_pattern() {
        let pm = PassManager::new()
            .with_pass(Box::new(NoOpPass))
            .with_pass(Box::new(NoOpPass));
        assert_eq!(pm.num_passes(), 2);
    }

    #[test]
    fn test_run_once_with_provenance_plumbs_map_to_pass() {
        let mut pm =
            PassManager::new().with_pass(Box::new(ProvenanceMarkingPass { inst: InstId(0) }));
        let mut func = make_empty_func();
        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(0), &[InstId(0)], PassId::new("isel"));

        assert_eq!(
            pm.run_once_with_provenance(&mut func, &mut provenance),
            Ok(true)
        );

        let entry = provenance.get_entry(InstId(0)).unwrap();
        assert_eq!(
            entry.transforms.last().unwrap().pass,
            PassId::new("provenance-mark")
        );
        assert_eq!(
            entry.transforms.last().unwrap().kind,
            TransformKind::Survived
        );
    }

    #[test]
    fn test_run_once_with_stats_and_provenance_plumbs_map_to_pass() {
        let mut pm =
            PassManager::new().with_pass(Box::new(ProvenanceMarkingPass { inst: InstId(0) }));
        let mut func = make_empty_func();
        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(0), &[InstId(0)], PassId::new("isel"));

        let stats = pm.run_once_with_stats_and_provenance(&mut func, &mut provenance);

        assert_eq!(stats.changes, 1);
        assert_eq!(stats.runs, vec![("provenance-mark".to_string(), 1)]);
        let entry = provenance.get_entry(InstId(0)).unwrap();
        assert_eq!(
            entry.transforms.last().unwrap().pass,
            PassId::new("provenance-mark")
        );
        assert_eq!(
            entry.transforms.last().unwrap().kind,
            TransformKind::Survived
        );
    }

    #[test]
    fn test_run_once_with_stats_collects_boxed_proof_certificates() {
        let mut pm = PassManager::new().with_pass(Box::new(ProofOptimization::new()));
        let mut func = make_no_overflow_func();

        func.try_sync_vreg_counter()
            .expect("fixture register ids fit u32");
        let stats = pm.run_once_with_stats(&mut func);

        assert_eq!(stats.changes, 1);
        assert_eq!(stats.proof_optimization_certificates.len(), 1);
        let cert = &stats.proof_optimization_certificates[0];
        assert_ne!(cert.certificate_id, 0);
        assert_ne!(cert.proof_hash, 0);
        assert_ne!(cert.validation_hash, 0);
    }

    #[test]
    fn test_cfg_fingerprint_ignores_non_cfg_instruction_mutations() {
        let (mut func, add) = make_analysis_func();
        let before = cfg_fingerprint(&func);

        func.inst_mut(add).operands[2] = MachOperand::Imm(99);

        assert_eq!(cfg_fingerprint(&func), before);
    }

    #[test]
    fn test_cfg_fingerprint_tracks_terminator_target_changes() {
        let (mut func, branch, _entry, _old_target, new_target) = make_redirectable_branch_func();
        let before = cfg_fingerprint(&func);

        func.inst_mut(branch).operands[0] = MachOperand::Block(new_target);

        assert_ne!(cfg_fingerprint(&func), before);
    }

    #[test]
    fn analysis_cache_refreshes_dominators_for_another_function() {
        let (first, _, entry, old_target, new_target) = make_redirectable_branch_func();
        let (mut second, branch, _, _, _) = make_redirectable_branch_func();
        let mut cache = AnalysisCache::new();
        assert!(cache.loop_analysis(&first).is_empty());
        assert_eq!(cache.domtree(&first).idom(old_target), Some(entry));
        assert_eq!(cache.domtree(&first).idom(new_target), None);
        assert!(
            BranchRedirectPass {
                branch,
                from: entry,
                old_target,
                new_target
            }
            .run(&mut second)
        );
        assert_eq!(cache.domtree(&second).idom(new_target), Some(entry));
        assert_eq!(cache.domtree(&second).idom(old_target), None);
        assert!(cache.loop_analysis(&second).is_empty());
        assert_eq!(cache.stats().domtree_computations, 2);
        assert_eq!(cache.stats().loop_analysis_computations, 2);
        assert_eq!(cache.stats().cfg_invalidations, 1);
    }

    #[test]
    fn analysis_cache_refreshes_loops_after_direct_cfg_mutation() {
        let (mut func, _, _, target, _) = make_redirectable_branch_func();
        let mut cache = AnalysisCache::new();
        assert!(cache.loop_analysis(&func).is_empty());
        add_analysis_self_loop(&mut func, target);
        assert!(!cache.loop_analysis(&func).is_empty());
        assert_eq!(cache.stats().domtree_computations, 2);
        assert_eq!(cache.stats().loop_analysis_computations, 2);
        assert_eq!(cache.stats().cfg_invalidations, 1);
    }

    #[test]
    fn analysis_cache_paired_accessor_refreshes_both_results() {
        let (mut func, branch, entry, old_target, new_target) = make_redirectable_branch_func();
        let mut cache = AnalysisCache::new();
        let (dom, loops) = cache.domtree_and_loops(&func);
        assert_eq!(dom.idom(old_target), Some(entry));
        assert!(loops.is_empty());
        assert!(
            BranchRedirectPass {
                branch,
                from: entry,
                old_target,
                new_target
            }
            .run(&mut func)
        );
        add_analysis_self_loop(&mut func, new_target);
        let (dom, loops) = cache.domtree_and_loops(&func);
        assert_eq!(dom.idom(new_target), Some(entry));
        assert_eq!(dom.idom(old_target), None);
        assert!(!loops.is_empty());
        assert_eq!(cache.stats().domtree_computations, 2);
        assert_eq!(cache.stats().loop_analysis_computations, 2);
    }

    #[test]
    fn analysis_cache_keeps_results_for_non_cfg_edits() {
        let (mut func, add) = make_analysis_func();
        let mut cache = AnalysisCache::new();
        cache.domtree_and_loops(&func);
        func.name = "same graph, different name".into();
        func.inst_mut(add).operands[2] = imm(99);
        cache.domtree_and_loops(&func);
        assert_eq!(
            cache.stats(),
            AnalysisCacheStats {
                domtree_computations: 1,
                loop_analysis_computations: 1,
                cfg_preservations: 0,
                cfg_invalidations: 0,
            }
        );
    }

    fn add_analysis_self_loop(func: &mut MachFunction, block: BlockId) {
        let terminator = *func.block(block).insts.last().unwrap();
        *func.inst_mut(terminator) =
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(block)]);
        func.add_edge(block, block);
    }

    #[test]
    fn analysis_cache_key_compares_every_graph_input_exactly() {
        let (func, _, entry, target, _) = make_redirectable_branch_func();
        let snapshot = AnalysisCfg::capture(&func);
        assert!(snapshot.matches(&func));
        for changed_field in 0..5 {
            let mut changed = func.clone();
            match changed_field {
                0 => changed.entry = target,
                1 => changed.block_order.reverse(),
                2 => {
                    changed.create_block();
                }
                3 => changed.block_mut(target).preds.clear(),
                4 => changed.block_mut(entry).succs.clear(),
                _ => unreachable!(),
            }
            assert!(
                !snapshot.matches(&changed),
                "unbound graph field {changed_field}"
            );
        }
    }

    #[test]
    fn analysis_cache_explicit_invalidation_clears_the_graph_binding() {
        let (func, _) = make_analysis_func();
        let mut cache = AnalysisCache::new();
        cache.domtree_and_loops(&func);
        cache.invalidate();
        assert!(cache.cfg.is_none());
        cache.domtree_and_loops(&func);
        assert_eq!(cache.stats().domtree_computations, 2);
        assert_eq!(cache.stats().loop_analysis_computations, 2);
        assert_eq!(cache.stats().cfg_invalidations, 1);
    }

    #[test]
    fn analysis_cache_statistics_saturate() {
        let (func, _) = make_analysis_func();
        let mut cache = AnalysisCache::new();
        let full = AnalysisCacheStats {
            domtree_computations: u32::MAX,
            loop_analysis_computations: u32::MAX,
            cfg_preservations: u32::MAX,
            cfg_invalidations: u32::MAX,
        };
        cache.stats = full;
        cache.domtree_and_loops(&func);
        cache.preserve_for_unchanged_cfg();
        cache.invalidate();
        cache.domtree(&func);
        cache.loop_analysis(&func);
        assert_eq!(cache.stats(), full);
    }

    #[test]
    fn test_analysis_cache_preserved_for_non_cfg_change() {
        let (mut func, add) = make_analysis_func();
        let samples = Rc::new(RefCell::new(Vec::new()));
        let mut pm = PassManager::new()
            .with_pass(Box::new(AnalysisProbePass {
                samples: Rc::clone(&samples),
            }))
            .with_pass(Box::new(ImmediateRewritePass { inst: add }))
            .with_pass(Box::new(AnalysisProbePass {
                samples: Rc::clone(&samples),
            }));

        func.try_sync_vreg_counter()
            .expect("fixture register ids fit u32");
        let stats = pm.run_once_with_stats(&mut func);

        assert_eq!(stats.changes, 1);
        let samples = samples.borrow();
        assert_eq!(samples.len(), 2);
        assert_eq!(samples[0].domtree_computations, 1);
        assert_eq!(samples[0].loop_analysis_computations, 1);
        assert_eq!(samples[1].domtree_computations, 1);
        assert_eq!(samples[1].loop_analysis_computations, 1);
        assert_eq!(samples[1].cfg_preservations, 1);
        assert_eq!(samples[1].cfg_invalidations, 0);
    }

    #[test]
    fn test_analysis_cache_invalidated_for_cfg_change() {
        let (mut func, branch, entry, old_target, new_target) = make_redirectable_branch_func();
        let samples = Rc::new(RefCell::new(Vec::new()));
        let mut pm = PassManager::new()
            .with_pass(Box::new(AnalysisProbePass {
                samples: Rc::clone(&samples),
            }))
            .with_pass(Box::new(BranchRedirectPass {
                branch,
                from: entry,
                old_target,
                new_target,
            }))
            .with_pass(Box::new(AnalysisProbePass {
                samples: Rc::clone(&samples),
            }));

        let stats = pm.run_once_with_stats(&mut func);

        assert_eq!(stats.changes, 1);
        let samples = samples.borrow();
        assert_eq!(samples.len(), 2);
        assert_eq!(samples[0].domtree_computations, 1);
        assert_eq!(samples[0].loop_analysis_computations, 1);
        assert_eq!(samples[1].domtree_computations, 2);
        assert_eq!(samples[1].loop_analysis_computations, 2);
        assert_eq!(samples[1].cfg_preservations, 0);
        assert_eq!(samples[1].cfg_invalidations, 1);
    }

    #[test]
    fn test_run_to_fixpoint_with_provenance_uses_default_analysis_hook() {
        let mut pm = PassManager::new().with_pass(Box::new(CountingPass { remaining: 1 }));
        let mut func = make_empty_func();
        let mut provenance = ProvenanceMap::new();

        let stats = pm.run_to_fixpoint_with_provenance(&mut func, &mut provenance, 4);

        assert_eq!(stats.iterations, 2);
        assert_eq!(stats.changes, 1);
        assert_eq!(stats.runs, vec![("counting".to_string(), 2)]);
    }

    // ---- Sentinel S4: kernel-recheck plumbing (AArch64 production parity) ----

    /// A pass whose independent re-check always rejects. Stands in for a
    /// `ProofOptimization` run that authorized an elimination it cannot
    /// re-justify, exercising the fail-closed plumbing without depending on a
    /// genuine kernel divergence (the real pass shares evidence between
    /// `decide` and `recheck`, so it can only diverge under a true bug).
    struct PoisonedRecheckPass;

    impl MachinePass for PoisonedRecheckPass {
        fn name(&self) -> &str {
            "poisoned-recheck"
        }
        fn run(&mut self, _func: &mut MachFunction) -> bool {
            false
        }
        fn recheck_kernel_eliminations(&self) -> Result<(), String> {
            Err("poisoned: elimination could not be re-justified".to_string())
        }
    }

    /// A bounds-check carrier (InstId 0) + ldr + ret — the AArch64 carrier the
    /// kernel gate operates on.
    fn make_bounds_carrier_func() -> MachFunction {
        let mut func = MachFunction::new(
            "pass_manager_kernel_recheck".to_string(),
            Signature::new(vec![], vec![]),
        );
        let block = func.entry;
        let guard = MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![vreg(0), vreg(1), imm(8)],
        )
        .with_proof(ProofAnnotation::InBounds);
        let ldr = MachInst::new(AArch64Opcode::LdrRI, vec![vreg(2), vreg(3), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        for inst in [guard, ldr, ret] {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
        }
        func
    }

    /// The PassManager surfaces a boxed pass's re-check REJECTION through
    /// `PassStats::kernel_recheck` (every run mode). This is the exact plumbing
    /// the AArch64 production path relies on to fail closed.
    #[test]
    fn kernel_recheck_rejection_is_surfaced_through_pass_stats() {
        let mut func = make_empty_func();

        // run_to_fixpoint
        let mut pm = PassManager::new().with_pass(Box::new(PoisonedRecheckPass));
        let stats = pm.run_to_fixpoint(&mut func, 4);
        assert!(
            stats.kernel_recheck().is_err(),
            "fixpoint run must surface the poisoned re-check verdict"
        );

        // run_once_with_stats
        let mut pm = PassManager::new().with_pass(Box::new(PoisonedRecheckPass));
        let stats = pm.run_once_with_stats(&mut func);
        assert!(
            stats.kernel_recheck().is_err(),
            "single run must surface the poisoned re-check verdict"
        );

        // run_to_fixpoint_with_provenance
        let mut pm = PassManager::new().with_pass(Box::new(PoisonedRecheckPass));
        let mut provenance = ProvenanceMap::new();
        let stats = pm.run_to_fixpoint_with_provenance(&mut func, &mut provenance, 4);
        assert!(
            stats.kernel_recheck().is_err(),
            "provenance fixpoint run must surface the poisoned re-check verdict"
        );
    }

    /// A passing re-check (or a pipeline with no kernel-gated pass at all)
    /// leaves `PassStats::kernel_recheck` as `Ok(())` so the production caller
    /// proceeds normally.
    #[test]
    fn kernel_recheck_ok_when_no_gated_pass_or_recheck_passes() {
        let mut func = make_empty_func();
        let mut pm = PassManager::new().with_pass(Box::new(NoOpPass));
        let stats = pm.run_to_fixpoint(&mut func, 4);
        assert!(stats.kernel_recheck().is_ok());
    }

    /// End-to-end through the PassManager: a kernel-gated `ProofOptimization`
    /// with a DISCHARGED obligation eliminates the carrier AND its independent
    /// re-check, surfaced via `PassStats::kernel_recheck`, passes — proving the
    /// real pass's verdict flows through the boxed-pass plumbing the AArch64
    /// production path consumes.
    #[test]
    fn kernel_gated_proof_optimization_recheck_flows_through_pass_manager() {
        use std::collections::HashMap;
        use trust_cg_ir::{DischargeStatus, DischargedEvidenceTable};

        let mut func = make_bounds_carrier_func();
        let mut evidence = DischargedEvidenceTable::new();
        evidence.insert(100, DischargeStatus::Discharged, None);
        let mut obligations = HashMap::new();
        obligations.insert(InstId(0), (100u128, None)); // carrier is InstId 0

        let mut pass = ProofOptimization::new();
        pass.enable_kernel_gate(evidence, obligations);

        let mut pm = PassManager::new().with_pass(Box::new(pass));
        func.try_sync_vreg_counter()
            .expect("fixture register ids fit u32");
        let stats = pm.run_to_fixpoint(&mut func, 4);

        // The carrier was eliminated (guard removed; ldr + ret remain) ...
        assert_eq!(func.block(func.entry).insts.len(), 2);
        // ... and the kernel re-check, surfaced through the boxed pass, passed.
        assert!(
            stats.kernel_recheck().is_ok(),
            "discharged-obligation elimination must re-justify on re-check"
        );
    }

    /// `pass_labels` is the allocation elision for the env-gated label
    /// consumers: with every consumer off it must build NOTHING, and with one
    /// on it must yield exactly the strings the timing log / dump / diag paths
    /// print, so enabling a consumer never changes what is reported.
    #[test]
    fn pass_labels_are_empty_when_no_consumer_is_enabled() {
        let (name, bk) = pass_labels(&NoOpPass, false);
        assert!(name.is_empty(), "pass label built with every consumer off");
        assert!(
            bk.is_empty(),
            "bookkeeping label built with every consumer off"
        );
        assert_eq!(
            name.capacity(),
            0,
            "pass label allocated with every consumer off"
        );
        assert_eq!(
            bk.capacity(),
            0,
            "bookkeeping label allocated with every consumer off"
        );
    }

    #[test]
    fn pass_labels_are_the_real_names_when_a_consumer_is_enabled() {
        let (name, bk) = pass_labels(&NoOpPass, true);
        assert_eq!(name, "no-op");
        assert_eq!(bk, bookkeeping_name("no-op"));
        assert_eq!(bk, "no-op::bookkeeping");

        let (name, bk) = pass_labels(&CountingPass { remaining: 0 }, true);
        assert_eq!(name, "counting");
        assert_eq!(bk, "counting::bookkeeping");
    }

    /// Eliding the labels must not touch the fixpoint itself: the same passes
    /// run the same number of times and report the same changes, and the
    /// per-pass stats still carry the real pass names (those come from
    /// `PassStats::runs`, not from the elided labels).
    #[test]
    fn label_elision_leaves_fixpoint_stats_and_names_intact() {
        let mut pm = PassManager::new()
            .with_pass(Box::new(NoOpPass))
            .with_pass(Box::new(CountingPass { remaining: 2 }));
        let mut func = make_empty_func();
        let stats = pm.run_to_fixpoint(&mut func, 10);
        assert_eq!(stats.iterations, 3);
        assert_eq!(stats.changes, 2);
        assert_eq!(stats.runs[0].0, "no-op");
        assert_eq!(stats.runs[1].0, "counting");
        assert_eq!(stats.runs[1].1, 3);
    }
}
