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

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::time::Instant;

use serde::{Deserialize, Serialize};
use trust_cg_ir::{MachFunction, MachOperand, ProvenanceMap};

use crate::dom::DomTree;
use crate::loops::LoopAnalysis;
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
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct AnalysisCacheStats {
    /// Number of dominator tree computations performed by this cache.
    pub domtree_computations: u32,
    /// Number of loop analysis computations performed by this cache.
    pub loop_analysis_computations: u32,
    /// Changed passes whose CFG fingerprint stayed stable.
    pub cfg_preservations: u32,
    /// Changed passes whose CFG fingerprint changed and invalidated analyses.
    pub cfg_invalidations: u32,
}

/// Cached analysis results shared across passes within an iteration.
///
/// Avoids redundant recomputation of dominator trees and loop analysis
/// when multiple passes need them within a single fixpoint iteration.
/// The cache is invalidated only when a changed pass also changes the CFG
/// fingerprint; non-CFG rewrites preserve these analyses.
pub struct AnalysisCache {
    domtree: Option<DomTree>,
    loop_analysis: Option<LoopAnalysis>,
    stats: AnalysisCacheStats,
}

impl AnalysisCache {
    /// Create an empty analysis cache.
    pub fn new() -> Self {
        Self {
            domtree: None,
            loop_analysis: None,
            stats: AnalysisCacheStats::default(),
        }
    }

    /// Get the dominator tree, computing and caching it if necessary.
    pub fn domtree(&mut self, func: &MachFunction) -> &DomTree {
        if self.domtree.is_none() {
            self.domtree = Some(DomTree::compute(func));
            self.stats.domtree_computations += 1;
        }
        self.domtree.as_ref().unwrap()
    }

    /// Get the loop analysis, computing and caching it if necessary.
    /// This also ensures the dominator tree is cached.
    pub fn loop_analysis(&mut self, func: &MachFunction) -> &LoopAnalysis {
        if self.loop_analysis.is_none() {
            // Ensure domtree is computed first.
            if self.domtree.is_none() {
                self.domtree = Some(DomTree::compute(func));
                self.stats.domtree_computations += 1;
            }
            let dom = self.domtree.as_ref().unwrap();
            self.loop_analysis = Some(LoopAnalysis::compute(func, dom));
            self.stats.loop_analysis_computations += 1;
        }
        self.loop_analysis.as_ref().unwrap()
    }

    /// Current cache reuse statistics.
    pub fn stats(&self) -> AnalysisCacheStats {
        self.stats
    }

    /// Record that a changed pass preserved the CFG, so analyses remain valid.
    pub fn preserve_for_unchanged_cfg(&mut self) {
        self.stats.cfg_preservations += 1;
    }

    /// Invalidate all cached analyses. Called when a pass changes the CFG.
    pub fn invalidate(&mut self) {
        self.domtree = None;
        self.loop_analysis = None;
        self.stats.cfg_invalidations += 1;
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
}

impl Default for PassStats {
    fn default() -> Self {
        Self {
            runs: Vec::new(),
            changes: 0,
            iterations: 0,
            proof_optimization_certificates: Vec::new(),
            certified_pass_runs: Vec::new(),
            kernel_recheck: Ok(()),
        }
    }
}

impl PassStats {
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
}

/// Manages and executes a pipeline of optimization passes.
///
/// Passes are run in insertion order. The pass manager supports both
/// single-run and fixed-point iteration modes.
pub struct PassManager {
    passes: Vec<Box<dyn MachinePass>>,
    proof_optimization_metadata: ProofOptimizationMetadata,
}

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

fn cfg_fingerprint(func: &MachFunction) -> CfgFingerprint {
    let mut hasher = DefaultHasher::new();

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
        let inst = func.inst(inst_id);
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
/// for passes that reported `changed = true`. A pass that mutates while
/// reporting false corrupts the analysis cache under EITHER scheme.
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

/// Cached `TCG_DIAG_CHANGED` flag: read the environment once per process so
/// the default-off path costs one branch per pass run, not a getenv.
fn diag_changed_enabled() -> bool {
    use std::sync::OnceLock;
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("TCG_DIAG_CHANGED").is_some())
}

fn log_pass_start(func: &MachFunction, iteration: u32, pass_name: &str) -> Option<Instant> {
    if !should_time_passes() {
        return None;
    }
    let (blocks, insts) = function_shape(func);
    eprintln!(
        "[trust-cg-time-pass] start func={} iter={} pass={} blocks={} insts={}",
        func.name, iteration, pass_name, blocks, insts
    );
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
    let (blocks, insts) = function_shape(func);
    eprintln!(
        "[trust-cg-time-pass] end func={} iter={} pass={} changed={} elapsed_us={} blocks={} insts={}",
        func.name,
        iteration,
        pass_name,
        changed,
        start.elapsed().as_micros(),
        blocks,
        insts
    );
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
        }
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
    /// Returns `true` if any pass modified the function.
    pub fn run_once(&mut self, func: &mut MachFunction) -> bool {
        let mut changed = false;
        for pass in &mut self.passes {
            if pass.run(func) {
                changed = true;
            }
        }
        changed
    }

    /// Run all passes once with access to a provenance map.
    ///
    /// Returns `true` if any pass modified the function.
    pub fn run_once_with_provenance(
        &mut self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> bool {
        let mut changed = false;
        for pass in &mut self.passes {
            if pass.run_with_provenance(func, provenance) {
                changed = true;
            }
        }
        changed
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
        let mut stats = PassStats {
            runs: self
                .passes
                .iter()
                .map(|p| (p.name().to_string(), 0))
                .collect(),
            changes: 0,
            iterations: 0,
            proof_optimization_certificates: Vec::new(),
            certified_pass_runs: Vec::new(),
            kernel_recheck: Ok(()),
        };

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
                let pass_name = pass.name().to_string();
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
                let timer = log_pass_start(func, iteration + 1, &pass_name);
                let pass_changed = pass.run_with_analyses(func, &mut cache);
                log_pass_end(func, iteration + 1, &pass_name, pass_changed, timer);
                if let Some(pre) = diag_pre {
                    if pass_changed {
                        let post = format!("{func:?}");
                        if pre == post {
                            eprintln!(
                                "TCG_DIAG_CHANGED FALSE-CHANGED iter={} pass={} func={}",
                                iteration + 1,
                                pass_name,
                                func.name
                            );
                        }
                    }
                }
                let bk = log_pass_start(func, iteration + 1, &bookkeeping_name(&pass_name));
                collect_proof_optimization_certificates(&mut stats, pass.as_mut());
                collect_certified_pass_runs(&mut stats, pass.as_mut());
                collect_kernel_recheck(&mut stats, pass.as_ref());
                log_pass_end(
                    func,
                    iteration + 1,
                    &bookkeeping_name(&pass_name),
                    false,
                    bk,
                );
                if pass_changed {
                    any_changed = true;
                    stats.changes += 1;
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
        let mut stats = PassStats {
            runs: self
                .passes
                .iter()
                .map(|p| (p.name().to_string(), 0))
                .collect(),
            changes: 0,
            iterations: 0,
            proof_optimization_certificates: Vec::new(),
            certified_pass_runs: Vec::new(),
            kernel_recheck: Ok(()),
        };

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
                let pass_name = pass.name().to_string();
                let before_cfg = current_cfg;
                let timer = log_pass_start(func, iteration + 1, &pass_name);
                let pass_changed =
                    pass.run_with_analyses_and_provenance(func, &mut cache, provenance);
                log_pass_end(func, iteration + 1, &pass_name, pass_changed, timer);
                let bk = log_pass_start(func, iteration + 1, &bookkeeping_name(&pass_name));
                collect_proof_optimization_certificates(&mut stats, pass.as_mut());
                collect_certified_pass_runs(&mut stats, pass.as_mut());
                collect_kernel_recheck(&mut stats, pass.as_ref());
                log_pass_end(
                    func,
                    iteration + 1,
                    &bookkeeping_name(&pass_name),
                    false,
                    bk,
                );
                if pass_changed {
                    any_changed = true;
                    stats.changes += 1;
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

        stats
    }

    /// Run all passes once, collecting per-pass statistics.
    ///
    /// Uses an [`AnalysisCache`] to avoid redundant domtree/loop analysis
    /// recomputation across passes.
    pub fn run_once_with_stats(&mut self, func: &mut MachFunction) -> PassStats {
        let mut stats = PassStats {
            runs: self
                .passes
                .iter()
                .map(|p| (p.name().to_string(), 0))
                .collect(),
            changes: 0,
            iterations: 1,
            proof_optimization_certificates: Vec::new(),
            certified_pass_runs: Vec::new(),
            kernel_recheck: Ok(()),
        };

        let should_dump = should_dump_mir(func);
        if should_dump {
            eprintln!("=== before passes [func={}] ===", func.name);
            dump_function(func);
        }

        let mut cache = AnalysisCache::new();
        // See the fixpoint drivers: one fingerprint maintained across pass
        // runs instead of one recompute per invocation.
        let mut current_cfg = cfg_fingerprint(func);
        for (i, pass) in self.passes.iter_mut().enumerate() {
            stats.runs[i].1 = 1;
            let pass_name = pass.name().to_string();
            let before_cfg = current_cfg;
            let timer = log_pass_start(func, 1, &pass_name);
            let pass_changed = pass.run_with_analyses(func, &mut cache);
            log_pass_end(func, 1, &pass_name, pass_changed, timer);
            let bk = log_pass_start(func, 1, &bookkeeping_name(&pass_name));
            collect_proof_optimization_certificates(&mut stats, pass.as_mut());
            collect_certified_pass_runs(&mut stats, pass.as_mut());
            collect_kernel_recheck(&mut stats, pass.as_ref());
            log_pass_end(func, 1, &bookkeeping_name(&pass_name), false, bk);
            if pass_changed {
                stats.changes += 1;
                current_cfg = update_cache_after_changed_pass(func, &mut cache, before_cfg);
                if should_dump {
                    eprintln!("=== after pass [{}] ===", pass_name);
                    dump_function(func);
                }
            } else if should_dump {
                eprintln!("=== pass [{}] no changes ===", pass_name);
            }
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
        let mut stats = PassStats {
            runs: self
                .passes
                .iter()
                .map(|p| (p.name().to_string(), 0))
                .collect(),
            changes: 0,
            iterations: 1,
            proof_optimization_certificates: Vec::new(),
            certified_pass_runs: Vec::new(),
            kernel_recheck: Ok(()),
        };

        let should_dump = should_dump_mir(func);
        if should_dump {
            eprintln!("=== before passes [func={}] ===", func.name);
            dump_function(func);
        }

        let mut cache = AnalysisCache::new();
        // See the fixpoint drivers: one fingerprint maintained across pass
        // runs instead of one recompute per invocation.
        let mut current_cfg = cfg_fingerprint(func);
        for (i, pass) in self.passes.iter_mut().enumerate() {
            stats.runs[i].1 = 1;
            let pass_name = pass.name().to_string();
            let before_cfg = current_cfg;
            let timer = log_pass_start(func, 1, &pass_name);
            let pass_changed = pass.run_with_analyses_and_provenance(func, &mut cache, provenance);
            log_pass_end(func, 1, &pass_name, pass_changed, timer);
            let bk = log_pass_start(func, 1, &bookkeeping_name(&pass_name));
            collect_proof_optimization_certificates(&mut stats, pass.as_mut());
            collect_certified_pass_runs(&mut stats, pass.as_mut());
            collect_kernel_recheck(&mut stats, pass.as_ref());
            log_pass_end(func, 1, &bookkeeping_name(&pass_name), false, bk);
            if pass_changed {
                stats.changes += 1;
                current_cfg = update_cache_after_changed_pass(func, &mut cache, before_cfg);
                if should_dump {
                    eprintln!("=== after pass [{}] ===", pass_name);
                    dump_function(func);
                }
            } else if should_dump {
                eprintln!("=== pass [{}] no changes ===", pass_name);
            }
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
        assert!(!pm.run_once(&mut func));
    }

    #[test]
    fn test_noop_pass() {
        let mut pm = PassManager::new();
        pm.add_pass(Box::new(NoOpPass));
        let mut func = make_empty_func();
        assert!(!pm.run_once(&mut func));
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

        assert!(pm.run_once_with_provenance(&mut func, &mut provenance));

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
        let stats = pm.run_to_fixpoint(&mut func, 4);

        // The carrier was eliminated (guard removed; ldr + ret remain) ...
        assert_eq!(func.block(func.entry).insts.len(), 2);
        // ... and the kernel re-check, surfaced through the boxed pass, passed.
        assert!(
            stats.kernel_recheck().is_ok(),
            "discharged-obligation elimination must re-justify on re-check"
        );
    }
}
