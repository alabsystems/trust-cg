// trust-cg-opt - Optimization pipeline
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Optimization pipeline configuration and execution.
//!
//! Builds a `PassManager` with passes appropriate for the requested
//! optimization level. The pipeline follows the ordering from the
//! design doc (designs/2026-04-12-aarch64-backend.md):
//!
//! Pre-register-allocation:
//! 1. Constant folding
//! 2. Copy propagation
//! 3. CSE (common subexpression elimination)
//! 4. LICM (loop-invariant code motion)
//! 5. Declarative rewrite and rotate-idiom recognition
//! 6. DCE
//! 7. Instruction scheduling
//!
//! O1 uses the basic `InstructionScheduler` as the final pass, while
//! higher optimization levels use `PressureAwareScheduler` to balance
//! ILP against register pressure.
//!
//! Higher optimization levels run additional iterations and enable
//! more aggressive transforms.

use std::sync::{Arc, OnceLock};

use trust_cg_ir::{MachFunction, ProvenanceMap};

use crate::aarch64_bounds_check_elim::AArch64BoundsCheckElimination;
use crate::addr_mode::{AddrModeEarlyFormation, AddrModeFormation};
use crate::alias_hoist::AliasVersionedLoadHoist;
use crate::and_cmp_fuse::AndCmpFuse;
use crate::cfg_simplify::CfgSimplify;
use crate::cmp_branch_fusion::CmpBranchFusion;
use crate::cmp_select::CmpSelectCombine;
use crate::const_fold::{CertifiedConstantFolding, ConstantFolding};
use crate::copy_prop::CopyPropagation;
use crate::cse::CommonSubexprElim;
use crate::dce::{CertifiedDeadCodeElimination, DeadCodeElimination};
use crate::dead_loop::DeadCountedLoopElimination;
use crate::eor_rotate_fuse::EorRotateFuse;
use crate::ext_addr::ExtRegAddrFold;
use crate::gvn::GlobalValueNumbering;
use crate::if_convert::{CsincFold, IfConversion, TinyLoopDiamondConvert};
use crate::inline::FunctionInlining;
use crate::latch_and_split::LatchAndSplit;
use crate::licm::LoopInvariantCodeMotion;
use crate::loop_dead_pure_sink::LoopDeadPureSink;
use crate::loop_latch_layout::LoopLatchLayoutCombine;
use crate::loop_unroll::LoopUnroll;
use crate::loop_unswitch::LoopUnswitch;
use crate::lsr_and_ubfx::LsrAndUbfx;
use crate::mac_reg_block::MacRegBlock;
use crate::mac_row_unroll::MacRowUnroll;
use crate::mul_shift_reduce::MulShiftReduce;
use crate::neon_array::NeonArrayPass;
use crate::neon_bitrev::NeonBitrevPass;
use crate::neon_butterfly::NeonButterflyPass;
use crate::neon_bytesum::NeonBytesumPass;
use crate::neon_farray::NeonFArrayPass;
use crate::neon_fill::NeonFillPass;
use crate::neon_find::NeonFindPass;
use crate::neon_fmap::NeonFMapPass;
use crate::neon_fpred::NeonFPRedPass;
use crate::neon_iota_fill::NeonIotaFillPass;
use crate::neon_map::NeonMapPass;
use crate::neon_minmax::NeonMinMaxPass;
use crate::neon_predsum::NeonPredSumPass;
use crate::neon_reduce::NeonReducePass;
use crate::neon_stencil::NeonStencilPass;
use crate::pass_manager::{MachinePass, PassManager, PassStats};
use crate::pgo::{PipelineConfig as PgoPipelineConfig, ProfileUsePass};
use crate::post_index::PostIndexForm;
use crate::proof_opts::{ProofOptimization, ProofOptimizationMetadata};
use crate::ptr_iv_sr::PtrIvStrengthReduce;
use crate::recurrence_store_forward::RecurrenceStoreForward;
use crate::reduction_split::{ClosedFormReduction, ReductionSplit};
use crate::resid_collapse::ResidTripCollapse;
use crate::rewrite::patterns::register_migrated;
use crate::rewrite::{
    DeclarativeRewritePass, RewriteAdmissionLoadError, RewriteAdmissionLoadReport,
    RewriteAdmissionLoaderConfig, RewriteEngine, load_admitted_rewrites_from_json,
    register_admitted_rewrites_from_json,
};
use crate::rotate_idiom::RotateIdiom;
use crate::scalar_unroll::ScalarUnrollPass;
use crate::scheduler::{InstructionScheduler, PressureAwareScheduler};
use crate::select_fuse::SelectFlagFuse;
use crate::shift_alu_fuse::ShiftAluFuse;
use crate::sincos_merge::SincosMerge;
use crate::sroa::ScalarReplacementOfAggregates;
use crate::strength_reduce::StrengthReduction;
use crate::strided_store_unroll::StridedStoreUnroll;
use crate::swap_range_guard::SwapRangeGuardPass;
use crate::tail_call::TailCallOptimization;
use crate::unfuse_serial_fma::UnfuseSerialFma;
use crate::vectorize::VectorizationPass;
use crate::xorshift_demanded_bits::XorshiftDemandedBits;

#[cfg(test)]
thread_local! {
    static TEST_DISABLE_PASSES: std::cell::RefCell<Option<Option<String>>> =
        const { std::cell::RefCell::new(None) };
}

#[cfg(test)]
fn test_env_override(key: &str) -> Option<Option<String>> {
    match key {
        "TRUST_CG_DISABLE_PASSES" => {
            TEST_DISABLE_PASSES.with(|override_value| override_value.borrow().clone())
        }
        _ => None,
    }
}

#[cfg(test)]
#[derive(Clone, Copy)]
enum TestEnvOverrideKey {
    DisablePasses,
}

#[cfg(test)]
struct TestEnvOverrideGuard {
    key: TestEnvOverrideKey,
    previous: Option<Option<String>>,
}

#[cfg(test)]
impl Drop for TestEnvOverrideGuard {
    fn drop(&mut self) {
        let previous = self.previous.take();
        match self.key {
            TestEnvOverrideKey::DisablePasses => {
                TEST_DISABLE_PASSES.with(|slot| *slot.borrow_mut() = previous);
            }
        }
    }
}

#[cfg(test)]
fn set_test_env_override(key: TestEnvOverrideKey, value: Option<&str>) -> TestEnvOverrideGuard {
    let value = Some(value.map(str::to_owned));
    let previous = match key {
        TestEnvOverrideKey::DisablePasses => TEST_DISABLE_PASSES.with(|slot| slot.replace(value)),
    };
    TestEnvOverrideGuard { key, previous }
}

fn pipeline_env_var(key: &str) -> Option<String> {
    #[cfg(test)]
    if let Some(value) = test_env_override(key) {
        return value;
    }

    crate::env_lock::var(key).ok()
}

/// Kill switch for the late (post-unroll) SROA instance: set
/// `TCG_NO_LATE_SROA` (any value) to drop it from the O2/O3 pipelines.
fn late_sroa_enabled() -> bool {
    std::env::var_os("TCG_NO_LATE_SROA").is_none()
}

// The declarative rewrite pass is unconditionally on (it carries the migrated
// single-instruction peephole patterns). The only opt-out is the general
// per-pass bisect tool `TRUST_CG_DISABLE_PASSES=declrewrite` (`is_disabled`).
// The previous dedicated `TRUST_CG_ENABLE_DECLARATIVE_REWRITE` /
// `TRUST_CG_DISABLE_DECLARATIVE_REWRITE` kill-switch env vars were a transitional
// rollback path and have been removed now that the pass is stable.

/// Process-wide, lazily-built engine carrying only the constant migrated
/// peephole rule set (no admitted rewrites). Construction is deterministic and
/// the engine is consulted immutably at run time, so a single shared instance
/// is observationally identical to a freshly built one for every caller on the
/// no-admitted-rewrites path. Sharing avoids re-running `register_migrated`
/// (dozens of rule constructions, each allocating boxed matcher/constraint/
/// rewriter trait objects) on every pipeline/function construction.
fn shared_migrated_engine() -> Arc<RewriteEngine> {
    static MIGRATED_ENGINE: OnceLock<Arc<RewriteEngine>> = OnceLock::new();
    MIGRATED_ENGINE
        .get_or_init(|| {
            let mut engine = RewriteEngine::new();
            register_migrated(&mut engine);
            Arc::new(engine)
        })
        .clone()
}

/// Construct a declarative rewrite pass pre-loaded with the currently migrated
/// peephole rules plus any enabled, admitted static rewrites. Runs by default;
/// can be turned off with `TRUST_CG_DISABLE_PASSES=declrewrite`.
///
/// When there are no admitted rewrite records AND the admission loader is
/// disabled (the default), `register_admitted_rewrites_from_json` provably
/// registers zero additional rules, so the engine content is exactly the
/// constant migrated rule set. In that case we share a single, process-wide
/// engine via [`shared_migrated_engine`] instead of rebuilding it, which is
/// identical-output (same rules, consulted immutably) but avoids the per-call
/// `register_migrated` rebuild cost. Any other configuration (records present
/// or loader enabled) takes the historical owned-engine path unchanged.
fn make_declarative_rewrite_pass_with_report(
    admitted_rewrite_records: &[String],
    rewrite_admission_config: RewriteAdmissionLoaderConfig,
) -> (
    DeclarativeRewritePass,
    Result<RewriteAdmissionLoadReport, RewriteAdmissionLoadError>,
) {
    // Fast path: no admitted rewrite records and loader disabled. In this
    // configuration `register_admitted_rewrites_from_json` registers no rules
    // (it returns early after counting inputs) and yields the disabled report.
    // The engine is therefore exactly `register_migrated`, so we reuse the
    // shared instance. We still produce the identical report via the loader so
    // observability (`input_records`, `loader_enabled`, etc.) is unchanged.
    if !rewrite_admission_config.enabled {
        let report = load_admitted_rewrites_from_json(
            admitted_rewrite_records.iter().map(String::as_str),
            rewrite_admission_config,
        );
        return (
            DeclarativeRewritePass::new_shared("declarative-rewrite", shared_migrated_engine(), 16),
            report,
        );
    }

    let mut engine = RewriteEngine::new();
    register_migrated(&mut engine);
    let report = register_admitted_rewrites_from_json(
        admitted_rewrite_records.iter().map(String::as_str),
        rewrite_admission_config,
        &mut engine,
    );
    (
        DeclarativeRewritePass::new("declarative-rewrite", engine, 16),
        report,
    )
}

/// Optimization level.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptLevel {
    /// No optimizations (fastest compile).
    O0,
    /// Basic optimizations (DCE + peephole + scheduling).
    O1,
    /// Standard optimizations (full pipeline, 1 iteration).
    O2,
    /// Aggressive optimizations (full pipeline, iterated to fixpoint).
    O3,
    /// Size optimization (same as O2 for now).
    Os,
}

/// Observability emitted while constructing an [`OptimizationPipeline`].
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct OptimizationPipelineReport {
    /// Admission preview/load counts from the declarative rewrite hook.
    pub rewrite_admission_load_report: Option<RewriteAdmissionLoadReport>,
    /// Admission preview/load error when the hook failed closed.
    pub rewrite_admission_load_error: Option<RewriteAdmissionLoadError>,
}

impl OptimizationPipelineReport {
    fn record_rewrite_admission_load(
        &mut self,
        report: Result<RewriteAdmissionLoadReport, RewriteAdmissionLoadError>,
    ) {
        match report {
            Ok(report) => self.rewrite_admission_load_report = Some(report),
            Err(error) => self.rewrite_admission_load_error = Some(error),
        }
    }
}

/// Result of running an optimization pipeline with build-time observability.
#[derive(Debug, Clone)]
pub struct OptimizationPipelineRunReport {
    /// Standard pass-manager execution statistics.
    pub pass_stats: PassStats,
    /// Build-time pipeline observability.
    pub pipeline_report: OptimizationPipelineReport,
}

enum KernelGate {
    /// Compatibility/test route. Production accepts these public inputs only when the separately
    /// wired validator authority exists; otherwise [`ProofOptimization`] clears them fail-closed.
    Raw(
        trust_cg_ir::DischargedEvidenceTable,
        std::collections::HashMap<trust_cg_ir::InstId, (u128, Option<u128>)>,
    ),
    /// Decidable-lattice route. The opaque object owns evidence reconstructed by exact replay and
    /// live-carrier binding; no caller-constructible evidence/map crosses this boundary.
    Lattice(trust_cg_lower::lattice_guard::LatticeGuardReplayAuthority),
}

/// Optimization pipeline configuration.
pub struct OptimizationPipeline {
    pub level: OptLevel,
    pgo: PgoPipelineConfig,
    proof_metadata: ProofOptimizationMetadata,
    admitted_rewrite_records: Vec<String>,
    rewrite_admission_config: RewriteAdmissionLoaderConfig,
    certified_pass_execution: bool,
    /// Sentinel S4: when set, the guard-elimination pass is kernel-gated — a carrier is deleted
    /// only when the Certified-Elimination Kernel authorizes it against this evidence + the
    /// per-carrier obligation map. `None` => legacy behaviour (default; zero behaviour change).
    kernel_gate: Option<KernelGate>,
    /// When set, the redundancy-elimination passes (CSE + GVN) are skipped at
    /// O2/O3. Both passes replace a recomputation with a *reference* to an
    /// earlier result, which extends the live range of that value from its
    /// first computation to its last use. That trade is only profitable when
    /// the register allocator can rematerialize cheap values under pressure
    /// instead of spilling them.
    ///
    /// Under the JIT-latency register-allocator profile
    /// (`AllocConfig::jit_latency_aarch64`, used for in-process JIT kernels)
    /// rematerialization, coalescing, and splitting are all disabled, so the
    /// extended live ranges turn directly into spill stores/reloads that
    /// execute on every kernel invocation. For workloads that invoke the same
    /// kernels millions of times (e.g. an explicit-state model checker's
    /// next-state action kernels), recomputing a cheap pure expression is
    /// cheaper than the spill traffic CSE/GVN introduce. Measured on the
    /// `MCLamportMutex` corpus spec: skipping CSE+GVN cut executed instructions
    /// ~24% and wall ~16% with byte-identical state-graph results.
    ///
    /// Default `false`: zero behaviour change for every existing caller.
    skip_redundancy_elimination: bool,
    /// Explicit per-invocation pass-disable list. `None` preserves the
    /// process-level `TRUST_CG_DISABLE_PASSES` compatibility control; `Some`
    /// (including an empty string) makes this pipeline independent of mutable
    /// process environment.
    disabled_passes_override: Option<String>,
    /// Explicit per-invocation contains4 batch-scanner rewrite selection.
    /// `None` preserves the environment-controlled default.
    contains4_scanner_batch_rewrite_override: Option<bool>,
    /// When true, the object target is Darwin/Mach-O arm64, enabling the
    /// `sincos-merge` pass to emit the Apple-specific `___sincos_stret` combined
    /// call. Fail-closed default `false`: on any non-Darwin (ELF) target the
    /// `sincos` ABI differs, so the merge must stay inert. Set by the codegen
    /// pipeline from the concrete target triple.
    target_is_darwin: bool,
}

impl OptimizationPipeline {
    /// Create a pipeline for the given optimization level.
    pub fn new(level: OptLevel) -> Self {
        Self {
            level,
            pgo: PgoPipelineConfig::default(),
            proof_metadata: ProofOptimizationMetadata::new(),
            admitted_rewrite_records: Vec::new(),
            rewrite_admission_config: RewriteAdmissionLoaderConfig::default(),
            certified_pass_execution: false,
            kernel_gate: None,
            skip_redundancy_elimination: false,
            disabled_passes_override: None,
            contains4_scanner_batch_rewrite_override: None,
            target_is_darwin: false,
        }
    }

    /// Use an explicit pass-disable list for this pipeline invocation.
    ///
    /// This avoids temporarily mutating `TRUST_CG_DISABLE_PASSES` when a
    /// library caller needs an isolated scalar-control compilation. Passing an
    /// empty string explicitly enables the normal pass set regardless of the
    /// ambient process environment.
    pub fn with_disabled_passes(mut self, disabled: impl Into<String>) -> Self {
        self.disabled_passes_override = Some(disabled.into());
        self
    }

    /// Select the contains4 batch-scanner vector rewrite for this pipeline
    /// invocation without changing process environment.
    pub fn with_contains4_scanner_batch_rewrite(mut self, enabled: bool) -> Self {
        self.contains4_scanner_batch_rewrite_override = Some(enabled);
        self
    }

    /// Declare whether the object target is Darwin/Mach-O arm64. Only when true
    /// does the `sincos-merge` pass emit the Apple-only `___sincos_stret`
    /// combined call (see [`crate::sincos_merge`]). Fail-closed default is
    /// `false` (no merge), so callers that never set this stay bit-identical.
    pub fn with_target_is_darwin(mut self, darwin: bool) -> Self {
        self.target_is_darwin = darwin;
        self
    }

    /// Skip the redundancy-elimination passes (CSE + GVN) at O2/O3.
    ///
    /// Intended for in-process JIT kernels compiled under the JIT-latency
    /// register-allocator profile (no rematerialization), where CSE/GVN's
    /// live-range extension produces net-negative spill traffic. See
    /// `OptimizationPipeline::skip_redundancy_elimination` for the full
    /// rationale and measurements. This is purely a code-quality choice: the
    /// passes it skips are value-preserving, so omitting them cannot change
    /// observable results.
    pub fn without_redundancy_elimination(mut self) -> Self {
        self.skip_redundancy_elimination = true;
        self
    }

    /// Sentinel S4: enable kernel-gated guard elimination for this pipeline's proof pass(es).
    /// `evidence` is the discharged-obligation table (built from trust-ir); `obligations` maps a
    /// carrier `InstId` to its (obligation id, lineage digest).
    pub fn with_kernel_gate(
        mut self,
        evidence: trust_cg_ir::DischargedEvidenceTable,
        obligations: std::collections::HashMap<trust_cg_ir::InstId, (u128, Option<u128>)>,
    ) -> Self {
        self.kernel_gate = Some(KernelGate::Raw(evidence, obligations));
        self
    }

    /// Enable the decidable-lattice guard lane with replay-derived opaque authority.
    pub fn with_lattice_kernel_gate(
        mut self,
        authority: trust_cg_lower::lattice_guard::LatticeGuardReplayAuthority,
    ) -> Self {
        self.kernel_gate = Some(KernelGate::Lattice(authority));
        self
    }

    /// Build a `ProofOptimization` pass, kernel-gated if [`OptimizationPipeline::with_kernel_gate`]
    /// was set. Used at every level so the gate applies uniformly.
    fn proof_optimization_pass(&self) -> Box<dyn MachinePass> {
        let mut pass = ProofOptimization::new();
        match &self.kernel_gate {
            Some(KernelGate::Raw(evidence, obligations)) => {
                pass.enable_kernel_gate(evidence.clone(), obligations.clone());
            }
            Some(KernelGate::Lattice(authority)) => {
                pass.enable_lattice_kernel_gate(authority.clone());
            }
            None => {}
        }
        Box::new(pass)
    }

    /// Attach PGO configuration to the pipeline.
    pub fn with_pgo_config(mut self, pgo: PgoPipelineConfig) -> Self {
        self.pgo = pgo;
        self
    }

    /// Attach a loaded profile for profile-use mode.
    pub fn with_profile_use(self, profile: crate::pgo::ProfData) -> Self {
        self.with_pgo_config(PgoPipelineConfig::with_profile_use(profile))
    }

    /// Attach proof-optimization metadata consumed by the boxed proof pass.
    pub fn with_proof_optimization_metadata(mut self, metadata: ProofOptimizationMetadata) -> Self {
        self.proof_metadata = metadata;
        self
    }

    /// Attach admitted rewrite JSON records for the declarative rewrite pass.
    ///
    /// Records remain inert unless [`RewriteAdmissionLoaderConfig::enabled`] is
    /// set through [`OptimizationPipeline::with_rewrite_admission_config`].
    pub fn with_admitted_rewrite_records<I, S>(mut self, records: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.admitted_rewrite_records = records.into_iter().map(Into::into).collect();
        self
    }

    /// Attach opt-side admitted rewrite loader configuration.
    ///
    /// The default is disabled, preserving the existing pipeline behavior when
    /// no caller explicitly opts into the admitted rewrite loader.
    pub fn with_rewrite_admission_config(mut self, config: RewriteAdmissionLoaderConfig) -> Self {
        self.rewrite_admission_config = config;
        self
    }

    /// Use certified wrappers for the production const-fold/DCE pass slice.
    ///
    /// This is intentionally opt-in. The default pipeline continues to run the
    /// existing passes without emitting certified pass run records.
    pub fn with_certified_pass_execution(mut self) -> Self {
        self.certified_pass_execution = true;
        self
    }

    fn constant_folding_pass(&self) -> Box<dyn MachinePass> {
        if self.certified_pass_execution {
            Box::new(CertifiedConstantFolding::new())
        } else {
            Box::new(ConstantFolding)
        }
    }

    fn dce_pass(&self) -> Box<dyn MachinePass> {
        if self.certified_pass_execution {
            Box::new(CertifiedDeadCodeElimination::new())
        } else {
            Box::new(DeadCodeElimination)
        }
    }

    /// Build a PassManager configured for the current optimization level.
    pub fn build_pass_manager(&self) -> PassManager {
        self.build_pass_manager_with_report().0
    }

    /// Build a PassManager and return build-time observability.
    pub fn build_pass_manager_with_report(&self) -> (PassManager, OptimizationPipelineReport) {
        let mut pipeline_report = OptimizationPipelineReport::default();
        let disabled = self
            .disabled_passes_override
            .clone()
            .unwrap_or_else(|| pipeline_env_var("TRUST_CG_DISABLE_PASSES").unwrap_or_default());
        let skip_redundancy_elimination = self.skip_redundancy_elimination;
        let lattice_kernel_gate = matches!(self.kernel_gate, Some(KernelGate::Lattice(_)));
        let is_disabled = |name: &str| -> bool {
            // The opt-in `without_redundancy_elimination()` builder skips the
            // value-preserving redundancy passes (CSE + GVN) for JIT kernels
            // compiled without rematerialization; it is observationally the
            // same as `TRUST_CG_DISABLE_PASSES=cse,gvn`.
            if skip_redundancy_elimination && matches!(name, "cse" | "gvn") {
                return true;
            }
            disabled.split(',').any(|d| d.trim() == name)
        };

        let pm = match self.level {
            OptLevel::O0 => {
                // No optimizations at O0.
                PassManager::new().with_proof_optimization_metadata(self.proof_metadata.clone())
            }
            OptLevel::O1 => {
                // Basic: DCE, declarative rewrite, rotate idiom, late
                // scheduling.
                //
                // Wave 3 (#393) flipped declarative rewrite to default-on;
                // the hand-written `Peephole` pass has since been deleted.
                // The declarative pass carries every migrated pattern and
                // the standalone `RotateIdiom` pass carries pattern 53.
                // Kill switch: `TRUST_CG_DISABLE_PASSES=declrewrite`.
                let mut pm = PassManager::new()
                    .with_proof_optimization_metadata(self.proof_metadata.clone());
                // ProofOptimization (guard elimination) is pure-deletion:
                // apply_in_bounds/apply_not_null only insert into `to_delete`,
                // so the exact post-ISel lattice authority can be consumed
                // before an unrelated transform rewrites its bound function.
                // The ordinary/raw compatibility pass retains its established
                // post-DCE placement. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=proof`.
                if lattice_kernel_gate && !is_disabled("proof") {
                    pm = pm.with_pass(self.proof_optimization_pass());
                }
                if !is_disabled("dce") {
                    pm = pm.with_pass(self.dce_pass());
                }
                if !lattice_kernel_gate && !is_disabled("proof") {
                    pm = pm.with_pass(self.proof_optimization_pass());
                }
                if !is_disabled("declrewrite") {
                    let (pass, report) = make_declarative_rewrite_pass_with_report(
                        &self.admitted_rewrite_records,
                        self.rewrite_admission_config,
                    );
                    pipeline_report.record_rewrite_admission_load(report);
                    pm = pm.with_pass(Box::new(pass));
                }
                // SROA before rotate-idiom recognition: scalarise aggregate
                // locals so the subsequent rewrite/scheduler stages see plain
                // vreg moves instead of LDR/STR pairs. Part of #391
                // (aggregate lowering).
                if !is_disabled("sroa") {
                    pm = pm.with_pass(Box::new(ScalarReplacementOfAggregates));
                }
                // Peephole dropped: declarative rewrite covers it;
                // RotateIdiom carries pattern 53 (needs dominator info).
                // The `peep` bisect key now gates RotateIdiom.
                if !is_disabled("peep") {
                    pm = pm.with_pass(Box::new(RotateIdiom));
                }
                // EOR-with-rotate fusion: collapse `t = RorRI(s,k); d = EorRR(x,t)`
                // (single-use t) into the shifted-register `d = EorRRShift(x,s,k)`
                // (EOR x, s, ROR #k) — the consumer of the RorRI RotateIdiom just
                // created. Removes one instruction and one serial critical-path
                // node per ARX statement (salsa20). Fail-closed. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=eorrotfuse`.
                if !is_disabled("eorrotfuse") {
                    pm = pm.with_pass(Box::new(EorRotateFuse));
                }
                // Shift-into-ADD/SUB fusion: collapse `t = LslRI(s,k); d =
                // AddRR/SubRR(x,t)` (single-use t) into the shifted-register
                // `d = AddRRShift/SubRRShift(x,s,k)`; also the LSR sibling
                // `t = LsrRI(s,k); d = AddRR(x,t)` -> `AddRRShiftLsr` (the
                // srem/sdiv magic sign-bit correction; `TCG_NO_LSR_ADD_FUSE`
                // disables the LSR half alone). Non-commutative for SUB (the
                // shift binds to the subtrahend only). Fail-closed. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=shiftalufuse`.
                if !is_disabled("shiftalufuse") {
                    pm = pm.with_pass(Box::new(ShiftAluFuse));
                }
                // `LSR #k; AND #low_mask` -> UBFM/UBFX. The shared symbolic
                // W/X UBFM theorem proves the exact pre-rewrite expression and
                // independently decoded immediates. Fail-closed on use/def,
                // widths, masks, and field bounds. Bisect key: `lsrandubfx`.
                if !is_disabled("lsrandubfx") {
                    pm = pm.with_pass(Box::new(LsrAndUbfx));
                }
                if !is_disabled("sched") {
                    pm = pm.with_pass(Box::new(InstructionScheduler));
                }
                pm
            }
            OptLevel::O2 | OptLevel::Os => {
                // Standard: inlining + proof-consuming opts + scalar opts +
                // vectorization (before LICM!) + loop opts + peephole combines,
                // DCE, CFG cleanup, and pressure-aware scheduling last.
                //
                // Vectorization runs BEFORE LICM because LICM hoists
                // loop-invariant pure instructions out of loops, removing
                // the instructions the vectorizer needs to see. This matches
                // LLVM's ordering where LoopVectorize runs early in the loop
                // optimization pipeline. After vectorization rewrites scalar
                // ops to NEON, LICM can still hoist any remaining invariants.
                //
                // Dev note (#366 bisect): set TRUST_CG_DISABLE_PASSES to a
                // comma-separated list of pass short names to skip at O2.
                // Names: inline, addrmodeearly, proof, cfold, copyprop, cse,
                // gvn, sroa, vec, licm, strred, unswitch, unroll, declrewrite,
                // peep, addrmode, cmpsel, ifconv, cmpbr, latchsplit, tailcall, dce,
                // cfgsimp, aarch64bce, looplatch, extaddr, selfuse,
                // shiftalufuse, lsrandubfx, sched, profileuse. Empty/missing =
                // run all.
                //
                // Declarative rewrite (#393) is DEFAULT-ON as of Wave 3 and,
                // with the hand-written peephole pass deleted, is the sole
                // carrier of the migrated patterns (`RotateIdiom` carries
                // pattern 53; the `peep` bisect key gates it).
                // Kill switch: `TRUST_CG_DISABLE_PASSES=declrewrite`.
                let mut pm = PassManager::new()
                    .with_proof_optimization_metadata(self.proof_metadata.clone());
                // Consume exact post-ISel replay authority before any pass can
                // mutate the machine function it is bound to.
                if lattice_kernel_gate && !is_disabled("proof") {
                    pm = pm.with_pass(self.proof_optimization_pass());
                }
                let profile_use_enabled = !is_disabled("profileuse");
                let profile_hotness = profile_use_enabled
                    .then(|| self.pgo.profile_hotness())
                    .flatten();
                if let Some(profile) = self.pgo.profile_use.clone()
                    && profile_use_enabled
                {
                    pm = pm.with_pass(Box::new(ProfileUsePass::new(profile)));
                }
                if !is_disabled("inline") {
                    pm = pm.with_pass(Box::new(
                        FunctionInlining::new().with_profile_hotness(profile_hotness.clone()),
                    ));
                }
                // Sin/cos -> ___sincos_stret fusion (Darwin arm64). Runs EARLY —
                // right after inlining (so inlined bodies are covered) and before
                // the scheduler, which legally reorders across the two calls and
                // would separate the same-argument pair. The pass is inert unless
                // the target is Darwin (`with_target_is_darwin`). Kill switch:
                // `TCG_NO_SINCOS_MERGE` / `TRUST_CG_DISABLE_PASSES=sincosmerge`.
                if !is_disabled("sincosmerge") {
                    pm = pm.with_pass(Box::new(SincosMerge::new(self.target_is_darwin)));
                }
                // Loop-dead pure-computation deferral (almabench store
                // sinking). Runs EARLY — right after inlining/sincos-merge on
                // the pristine post-ISel shapes (the call-cluster and rotated
                // do-while recognizers depend on them), and before
                // addr-mode/CSE/scheduling rewrite the address chains. The
                // deferred loop it emits is then optimized by every later
                // pass. Kill switch: `TCG_NO_LOOP_DEAD_SINK` /
                // `TRUST_CG_DISABLE_PASSES=loopdeadsink`.
                if !is_disabled("loopdeadsink") {
                    pm = pm.with_pass(Box::new(LoopDeadPureSink));
                }
                if !is_disabled("addrmodeearly") {
                    pm = pm.with_pass(Box::new(AddrModeEarlyFormation));
                }
                if !lattice_kernel_gate && !is_disabled("proof") {
                    pm = pm.with_pass(self.proof_optimization_pass());
                }
                if !is_disabled("cfold") {
                    pm = pm.with_pass(self.constant_folding_pass());
                }
                if !is_disabled("copyprop") {
                    pm = pm.with_pass(Box::new(CopyPropagation));
                }
                if !is_disabled("cse") {
                    pm = pm.with_pass(Box::new(CommonSubexprElim));
                }
                if !is_disabled("gvn") {
                    pm = pm.with_pass(Box::new(GlobalValueNumbering));
                }
                // SROA: scalarise non-escaping aggregate locals (#391 phase 2b).
                // Runs after load-eliminating passes so it sees the canonical
                // LDR/STR pattern, and before loop/peep transforms that might
                // fold scalar moves back into memory ops.
                if !is_disabled("sroa") {
                    pm = pm.with_pass(Box::new(ScalarReplacementOfAggregates));
                }
                if !is_disabled("vec") {
                    let mut vectorizer =
                        VectorizationPass::new().with_profile_hotness(profile_hotness.clone());
                    if let Some(enabled) = self.contains4_scanner_batch_rewrite_override {
                        vectorizer = vectorizer.with_contains4_scanner_batch_rewrite(enabled);
                    }
                    pm = pm.with_pass(Box::new(vectorizer));
                }
                if !is_disabled("licm") {
                    pm = pm.with_pass(Box::new(LoopInvariantCodeMotion));
                }
                if !is_disabled("strred") {
                    pm = pm.with_pass(Box::new(StrengthReduction));
                }
                if !is_disabled("unfusefma") {
                    pm = pm.with_pass(Box::new(UnfuseSerialFma));
                }
                // Invariant loop unswitching: version a small innermost loop
                // on a loop-invariant Cbz/Cbnz/CmpRI#0+BCond test so the
                // decision is made ONCE in the preheader (Queens' Try
                // `i < 8`: previously tested 8x per call after the bounded
                // early-exit unroll, with the boolean spilled post-RA — a
                // serialized ldur+cbnz per clone). MUST run immediately
                // BEFORE loop-unroll so both versions unroll cleanly.
                // Fail-closed. Kill switch: `TCG_NO_LOOP_UNSWITCH`; bisect
                // key `unswitch`.
                if !is_disabled("unswitch") {
                    pm = pm.with_pass(Box::new(LoopUnswitch));
                }
                if !is_disabled("unroll") {
                    pm = pm.with_pass(Box::new(LoopUnroll::new(profile_hotness.clone())));
                }
                // Late SROA (2nd instance): the const-addr full unroll above
                // (`TCG_NO_CONST_ADDR_UNROLL`) rewrites stack-array index
                // arithmetic into constant offsets; re-running SROA promotes
                // the now-constant-offset local array to scalars (salsa20's
                // `x[16]` stack round-trip). Kill switch: `TCG_NO_LATE_SROA`;
                // shares the `sroa` bisect key.
                if !is_disabled("sroa") && late_sroa_enabled() {
                    pm = pm.with_pass(Box::new(ScalarReplacementOfAggregates));
                }
                if !is_disabled("declrewrite") {
                    let (pass, report) = make_declarative_rewrite_pass_with_report(
                        &self.admitted_rewrite_records,
                        self.rewrite_admission_config,
                    );
                    pipeline_report.record_rewrite_admission_load(report);
                    pm = pm.with_pass(Box::new(pass));
                }
                // Peephole dropped: declarative rewrite covers it;
                // RotateIdiom carries pattern 53 (needs dominator info).
                // The `peep` bisect key now gates RotateIdiom.
                if !is_disabled("peep") {
                    pm = pm.with_pass(Box::new(RotateIdiom));
                }
                // EOR-with-rotate fusion: collapse `t = RorRI(s,k); d = EorRR(x,t)`
                // (single-use t) into the shifted-register `d = EorRRShift(x,s,k)`
                // (EOR x, s, ROR #k) — the consumer of the RorRI RotateIdiom just
                // created. Removes one instruction and one serial critical-path
                // node per ARX statement (salsa20). Fail-closed. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=eorrotfuse`.
                if !is_disabled("eorrotfuse") {
                    pm = pm.with_pass(Box::new(EorRotateFuse));
                }
                if !is_disabled("addrmode") {
                    pm = pm.with_pass(Box::new(AddrModeFormation));
                }
                if !is_disabled("cmpsel") {
                    pm = pm.with_pass(Box::new(CmpSelectCombine));
                }
                if !is_disabled("ifconv") {
                    pm = pm.with_pass(Box::new(IfConversion));
                }
                // AND+CMP#0 -> TST. MUST precede cmp-branch-fusion: that pass
                // rewrites CmpRI into Cbz/Cbnz and AndCmpFuse only matches a
                // surviving CmpRI, so the reverse order silently starves it.
                // Together they compose into LLVM's `tbz`. C-flag guarded (ANDS
                // clears C, SUBS #0 sets it). Kill switch:
                // `TRUST_CG_DISABLE_PASSES=andcmpfuse`.
                if !is_disabled("andcmpfuse") {
                    pm = pm.with_pass(Box::new(AndCmpFuse));
                }
                // `y = x ^ (x << k)`: consumers reading only bits [0,k) may read
                // `x`, shortening the dependency chain into a mispredicting
                // branch by one shifted-EOR. Purely an operand swap; the bit
                // range must be provably below k or the operand is left alone.
                // Kill switch: `TRUST_CG_DISABLE_PASSES=xorshiftdemanded`.
                if !is_disabled("xorshiftdemanded") {
                    pm = pm.with_pass(Box::new(XorshiftDemandedBits));
                }
                if !is_disabled("cmpbr") {
                    pm = pm.with_pass(Box::new(CmpBranchFusion));
                }
                // Profile-gated hot-latch AND-condition split. Runs right AFTER
                // cmp-branch-fusion (which forms the `cbnz t` its recogniser
                // matches). INERT without an attached profile — the default
                // compile stays byte-identical; with a profile it fires only in
                // the unpredictable taken-rate band (see latch_and_split.rs).
                // Kill switch: `TCG_NO_LATCH_AND_SPLIT`; bisect key `latchsplit`.
                if !is_disabled("latchsplit") {
                    pm = pm.with_pass(Box::new(LatchAndSplit::new(profile_hotness.clone())));
                }
                if !is_disabled("tailcall") {
                    pm = pm.with_pass(Box::new(TailCallOptimization));
                }
                if !is_disabled("dce") {
                    pm = pm.with_pass(self.dce_pass());
                }
                if !is_disabled("cfgsimp") {
                    pm = pm.with_pass(Box::new(CfgSimplify));
                }
                // Late tiny-loop-diamond if-conversion: convert an unpredictable
                // NON-AFFINE-recurrence-gated tiny pure-arm diamond (b1's
                // `if s&6==2 { acc=rotate_left(acc,7) }`) to a CSEL. Runs HERE —
                // after cfg-simplify canonicalizes it to a clean diamond, which
                // the primary if-convert (pre-dce/cfg-simplify) cannot see. Tight
                // gate (loop-resident + tiny pure arm + EOR self-recurrence) so it
                // stays branchy on predictable diamonds. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=tinyloop`.
                if !is_disabled("tinyloop") {
                    pm = pm.with_pass(Box::new(TinyLoopDiamondConvert));
                }
                // AArch64 bounds-check elimination: DELETE a still-live
                // `TrapBoundsCheckExact` carrier whose enclosing loop-header
                // unsigned guard machine-proves the bound at the carrier site
                // (the own-length `for i in 0..N { a[i] }` shape). Runs here —
                // post-dce/cfgsimp (guard canonicalized to a direct
                // CmpRR/CmpRI+BCond) and PRE-looplatch/vectorization (single
                // unrotated header dominates the body) — the simplest sound
                // case. Standalone structural delete: it never touches the
                // proof/kernel path. Fail-safe on every unproven condition.
                // Default-ON kill switch: `TCG_NO_AARCH64_BCE`; per-pass bisect:
                // `TRUST_CG_DISABLE_PASSES=aarch64bce`.
                if !is_disabled("aarch64bce") {
                    pm = pm.with_pass(Box::new(AArch64BoundsCheckElimination::new()));
                }
                // Loop-carried store-to-load forwarding: register-carry the
                // memory recurrence of an in-place `a[i+1] = f(a[i], i)` loop
                // (one preheader load; the in-loop re-loads of the
                // just-stored cell are deleted and read the stored register
                // instead). Removes the store-forward latency — and its
                // address-sensitive run-to-run variance — from the
                // loop-carried critical path (d02 prefix-recurrence class).
                // Runs right AFTER aarch64-bounds-check-elim (recognizes the
                // clean bounds-elided body) and BEFORE the
                // unrollers/vectorizers. Closed-world, fail-closed on every
                // unproven precondition; emits only already-credited opcodes
                // (Madd + LdrRI). Default-ON kill switch:
                // `TCG_NO_RECURRENCE_STORE_FWD`; per-pass bisect:
                // `TRUST_CG_DISABLE_PASSES=recurrence_store_fwd`.
                if !is_disabled("recurrence_store_fwd") {
                    pm = pm.with_pass(Box::new(RecurrenceStoreForward::new()));
                }
                // Counted-strided-store partial-unroll (x4): splice a guarded,
                // 4x-unrolled main loop in FRONT of an innermost `while q <u N {
                // base[q]=val; q+=strideReg }` marking loop (const N, invariant
                // base/value, invariant REGISTER stride), leaving the scalar loop
                // as the exact `trip mod 4` remainder. This is p7's sieve marking
                // loop, which LLVM 4x-unrolls. PURELY ADDITIVE (never edits the
                // scalar loop); wrap-free via an `s <u N` pre-guard (3s/lim built
                // from AddRR/SubRR only — NO udiv, NO multiply); emits only
                // already-credited opcodes. Runs AFTER aarch64-bounds-check-elim
                // (needs the clean bounds-elided body) and BEFORE
                // closed-form-reduction/loop-latch-layout (needs the NATIVE,
                // non-rotated header test). Fail-safe on every unproven
                // precondition. Compile-time kill switch:
                // `TCG_NO_STRIDED_STORE_UNROLL`; per-pass bisect:
                // `TRUST_CG_DISABLE_PASSES=strided_store_unroll`.
                // Normalize ISel's folded constant-trip `CmpRI` guards back to
                // `CmpRR(iv, movz)` BEFORE the vectorizers/unrollers, so
                // dc5916e's `cmp_imm12_fold` does not silently defeat their
                // constant-trip recognizers (matmul full-unroll, the dt-class FP
                // maps). Semantics-preserving. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=consttripnorm`.
                if !is_disabled("consttripnorm") {
                    pm = pm.with_pass(Box::new(crate::scalar_unroll::ConstTripGuardNormalize));
                }
                if !is_disabled("strided_store_unroll") {
                    pm = pm.with_pass(Box::new(StridedStoreUnroll::new()));
                }
                // RMW-MAC row-loop partial-unroll (x4): splice a guarded,
                // 4x-unrolled main loop in FRONT of an innermost bounds-checked
                // `while j <u N { c[i*N+j] += aik*b[k*N+j]; j+=1 }` accumulate
                // loop (const N, const array length L, invariant i/k/aik/bases),
                // leaving the scalar loop as the exact `trip mod 4` remainder and
                // the fallback on any guard failure. This is p4_matmul's inner
                // j-loop, which LLVM 4x-unrolls with running pointers. PURELY
                // ADDITIVE (never edits the scalar loop); each lane replicates
                // the scalar per-lane memory order bit-for-bit (sound under any
                // aliasing); the three per-block guards re-check `j<N-3`,
                // `cidx<L-3`, `bidx<L-3` and subsume the scalar per-iteration
                // bounds branches; emits only already-credited opcodes (no
                // udiv/mul beyond the scalar madd). Same slot/ordering as
                // strided-store-unroll: AFTER aarch64-bounds-check-elim and
                // BEFORE closed-form-reduction/loop-latch-layout (needs the
                // NATIVE, non-rotated header test). Fail-safe on every unproven
                // precondition. Compile-time kill switch:
                // `TCG_NO_MAC_ROW_UNROLL`; per-pass bisect:
                // `TRUST_CG_DISABLE_PASSES=mac_row_unroll`.
                // Matmul 1D register-blocking (T=8): recognize the whole
                // 3-deep bounds-checked matmul nest (distinct stack-local
                // a/b/c, read-only a/b, single c store, const N a multiple of
                // 8, L>=N*N) and splice a CHECK-FREE register-blocked fast path
                // (k/j interchange, 8 c accumulators held across the k-loop,
                // stores sunk to tile end) in FRONT of the untouched checked
                // nest — kept as the runtime-guarded fallback so mac-row-unroll
                // still fires on it. Store-sinking is sound because a/b/c are
                // distinct locals (a/b never written; c's only store is
                // c[i*N+j]); the tiled indices are provably < L so no per-access
                // check is emitted. Runs right BEFORE mac-row-unroll (which
                // handles the fallback's inner j-loop) and AFTER
                // aarch64-bounds-check-elim (the clean LdrRI/StrRI + Madd
                // address form). Purely additive, fail-closed, emits only
                // already-credited opcodes. Kill switch: `TCG_NO_MAC_REG_BLOCK`;
                // per-pass bisect: `TRUST_CG_DISABLE_PASSES=mac_reg_block`.
                if !is_disabled("mac_reg_block") {
                    pm = pm.with_pass(Box::new(MacRegBlock::new()));
                }
                if !is_disabled("mac_row_unroll") {
                    pm = pm.with_pass(Box::new(MacRowUnroll::new()));
                }
                // SOUND hoisted-range-guard crosswise-SWAP fast path
                // (mac-row-unroll's sibling shape): splice a guarded,
                // check-free running-pointer main loop in FRONT of the
                // innermost bounds-checked transpose swap loop
                // `while x <u C { swap(base[y*S+x], base[x*S+y]) }` (const
                // C/S/K, invariant y/base, 4 expanded per-access checks). The
                // hoisted guards prove every elided check passes (both index
                // families are strictly monotone in x; their maxima are
                // checked once); the fast path replays the scalar loop's EXACT
                // per-iteration memory trace (sound under any aliasing);
                // guard-fail runs the untouched scalar loop. Same slot
                // rationale as mac-row-unroll: AFTER
                // aarch64-bounds-check-elim (the surviving checks are the
                // expanded cmp/b.lo diamonds), BEFORE
                // closed-form-reduction/loop-latch-layout (needs the NATIVE
                // header test) and BEFORE ext-addr/mul-shift-reduce (matches
                // the Madd index/address form). Purely additive; emits only
                // already-credited opcodes. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=swap_range_guard`.
                if !is_disabled("swap_range_guard") {
                    pm = pm.with_pass(Box::new(SwapRangeGuardPass::new()));
                }
                // Closed-form (Faulhaber) reduction: DELETE a reduction loop
                // whose entire term is a pure degree-≤2 polynomial in the IV,
                // replacing it with straight-line O(1) code. Runs BEFORE
                // LoopLatchLayoutCombine (which rotates the loop) so it sees the
                // clean, non-rotated register loop, and before the split so it
                // claims pure-polynomial add/madd reductions; everything else
                // (xor/or/mul/opaque terms) falls through to the split.
                // Fail-closed. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=closed_form_reduction`.
                if !is_disabled("closed_form_reduction") {
                    pm = pm.with_pass(Box::new(ClosedFormReduction));
                }
                // Delete provably-terminating, side-effect-free counted loops
                // (empty after upstream DCE). Fail-closed. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=deadloop`.
                if !is_disabled("deadloop") {
                    pm = pm.with_pass(Box::new(DeadCountedLoopElimination::new()));
                }
                if !is_disabled("looplatch") {
                    pm = pm.with_pass(Box::new(LoopLatchLayoutCombine));
                }
                // Reduction splitting (accumulator widening): break a
                // throughput-bound integer reduction's loop-carried chain into
                // N independent accumulators for ILP. Fail-closed: only fires on
                // the exact recognized constant-trip register-reduction shape.
                // Placed after DCE/CFG-simplify so it sees the cleaned-up loop.
                // SOUND NEON add-reduction vectorizer. Runs immediately BEFORE
                // reduction_split so it fires FIRST on lane-wise-vectorizable
                // reduction terms (e.g. `a += (i*7)|(i*3)`), lowering them to a
                // NEON vector accumulator + scalar tail. It BAILS (leaving the
                // scalar loop intact) on any shape it cannot prove lane-wise
                // equivalent, so reduction_split still handles those.
                if !is_disabled("neonreduce") {
                    pm = pm.with_pass(Box::new(NeonReducePass::new()));
                }
                // SOUND NEON array-reduction vectorizer: extends neon-reduce to
                // reductions whose term reads from READ-ONLY memory (`s +=
                // TERM(a[i], b[i], ...)`). Runs immediately after neon-reduce
                // (which BAILS on any load) and before reduction_split. Fires
                // only on the shapes it can prove lane-wise equivalent (i32
                // accumulator, `a[i]` loads, lane-wise ops) and BAILS otherwise.
                // Kill switch: `TRUST_CG_DISABLE_PASSES=neon_array`.
                if !is_disabled("neon_array") {
                    pm = pm.with_pass(Box::new(NeonArrayPass::new()));
                }
                // SOUND NEON byte-widening reduction into a u64 accumulator
                // (popcount-sum / byte-sum) — the case neon_array's i32-only
                // widening TRACK B and 2-block loop shape both miss (e.g.
                // v3_popcount). Composes already-proven CNT/UADDLP/ADD/UMOV +
                // the const-materialization MOVI and the shared-debt paired-Q
                // load, all now credited per-compile, so it promotes gate-clean.
                // Default-ON; kill switch: `TRUST_CG_DISABLE_PASSES=neon_bytesum`.
                if !is_disabled("neon_bytesum") {
                    pm = pm.with_pass(Box::new(NeonBytesumPass::new()));
                }
                // SOUND NEON min/max & bitwise array-reduction vectorizer:
                // extends neon-array to the non-add associative+commutative
                // reductions `m = max/min(m, TERM(a[i]))` (via `select(icmp)`)
                // and `m &= / |= / ^= TERM(a[i])`, plus the index-tracking
                // ARGMIN/ARGMAX shape (a 3rd carried var — best index — updated
                // under the SAME strict compare; first-occurrence preserved by a
                // (value, min-index) lexicographic exit fold). Runs immediately
                // after neon-array (which claims add/madd and BAILS on these)
                // and before reduction_split. i32-only; BAILS on i64, register
                // reductions, ambiguous / non-strict selects, and any
                // store/effect. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=neon_minmax`.
                if !is_disabled("neon_minmax") {
                    pm = pm.with_pass(Box::new(NeonMinMaxPass::new()));
                }
                // SOUND NEON predicated-sum array-reduction vectorizer: `s +=
                // TERM(a[i], ...)` where TERM contains a lane-wise `select`
                // (`(a[i]>0)?a[i]:0`, count-if, abs-sum, per-element-max sum).
                // Add-rooted, so neon-array (no Csel in its whitelist) and
                // neon-minmax (needs a Csel/bitwise-rooted acc) both BAIL on
                // these; this pass fires ONLY when the term has a select. The
                // select lowers to a proven per-lane compare mask + branchless
                // bitselect (EOR/AND). i32-only; BAILS on i64, ambiguous selects,
                // and any store/effect. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=neon_predsum`.
                if !is_disabled("neon_predsum") {
                    pm = pm.with_pass(Box::new(NeonPredSumPass::new()));
                }
                // SOUND NEON memory-MAP/STORE vectorizer: `a[i] = TERM(b[i],
                // c[i], ...)`. Distinct from the reduction vectorizers — it fires
                // only on loops that WRITE a single output array (BAILS on any
                // accumulator/reduction) and only when it can PROVE the store
                // pointer does not alias any input (trust_ir `noalias` params).
                // Runs after neon-array (both BAIL on each other's shapes) and
                // before reduction_split. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=neon_map`.
                if !is_disabled("neon_map") {
                    pm = pm.with_pass(Box::new(NeonMapPass::new()));
                }
                // SOUND NEON per-byte 8-bit-reverse MAP vectorizer: the byte
                // elementwise `out[i] = a[i].reverse_bits()` over two DISTINCT
                // `[u8; N]` stack slots — the case neon-map's i32/i64 lane set and
                // 2-block/chain shapes both miss. Recognizes the bridge's exact
                // `bitmanip_reverse_bits(n=8)` isolate/shift/OR ladder and lowers
                // each 16-byte Q to one FAITHFULLY-PROVEN `RBIT.16B`; purely
                // additive (a `ldp/rbit.16b/stp` main loop before the untouched
                // scalar tail), proven non-aliasing via distinct stack slots.
                // Kill switch: `TRUST_CG_DISABLE_PASSES=neon_bitrev`.
                if !is_disabled("neon_bitrev") {
                    pm = pm.with_pass(Box::new(NeonBitrevPass::new()));
                }
                // SOUND NEON array-FILL store vectorizer: `for i in 0..bound {
                // base[i*sz] = value }` with a loop-invariant base, a
                // const-OR-loop-invariant value, ZERO loads. Fires on the shared
                // `__trustcg_array_fill_iN` helper (DUP path) and any inline
                // const/invariant fill (MOVI/DUP). Purely additive (a MOVI/DUP
                // preheader + a `stp q,q,[p],#32` main loop in front of the
                // UNTOUCHED scalar loop); removes no bounds check. Runs after
                // neon-map, which needs a memory-reading TERM and BAILs on a
                // load-free pure fill, so the two never contend. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=neon_fill`.
                if !is_disabled("neon_fill") {
                    pm = pm.with_pass(Box::new(NeonFillPass::new()));
                }
                // SOUND NEON affine IOTA-fill store vectorizer: `for iv in
                // start..bound { base[iv] = trunc32(iv) + inv }` (i32
                // elements; `inv` loop-invariant/const/absent). The affine
                // sibling of neon-fill, which requires an iteration-INVARIANT
                // stored value and BAILS on this shape — the two never
                // contend. Purely additive (iota literal + DUP/ADD preheader +
                // a 64-byte `stp q,q` main loop in front of the UNTOUCHED
                // scalar loop); removes no bounds check. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=neon_iota_fill`.
                if !is_disabled("neon_iota_fill") {
                    pm = pm.with_pass(Box::new(NeonIotaFillPass::new()));
                }
                // Conditional-store blind-write vectorization is intentionally
                // unscheduled: TrustIR/MachIR does not yet carry the required
                // function/value/range-bound writable+single-owner capability.
                // SOUND NEON EARLY-EXIT SEARCH (find/memchr) vectorizer: the
                // vector loop is a BLOCK FILTER — it only skips 16-blocks it has
                // PROVEN contain no match (faithful CMEQ + OR); on any-hit it
                // hands off to the UNTOUCHED scalar loop at the block base, which
                // finds the exact first match. Over-read is a SUBSET of the
                // no-match scalar execution's read set (guard admits only fully
                // in-bounds blocks) — no new axiom. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=neon_find`.
                if !is_disabled("neon_find") {
                    pm = pm.with_pass(Box::new(NeonFindPass::new()));
                }
                // SOUND NEON STENCIL (windowed-read) vectorizer: `out[i] =
                // TERM(a[i+k1], a[i+k2], ...)` with small constant offsets. Runs
                // after neon-map (which BAILS on any shifted read) and requires
                // `out` and every read base to be DISTINCT noalias params (so the
                // store is disjoint from every read; in-place stencils BAIL) and
                // the store at offset 0 (so the halo stays inside the scalar
                // loop's access set). Kill switch:
                // `TRUST_CG_DISABLE_PASSES=neon_stencil`.
                if !is_disabled("neon_stencil") {
                    pm = pm.with_pass(Box::new(NeonStencilPass::new()));
                }
                // SOUND NEON elementwise-FP map/stencil/count vectorizer:
                // `out[i] = FTERM(a[i+k], ..., invariants)` (f32 `.4S` / f64
                // `.2D`) and the integer-accumulating FP count-above
                // `c += (a[i] > t)`. FP REDUCTIONS ARE NEVER TOUCHED
                // (reassociation would change results — they stay on the
                // order-preserving scalar path). Per-lane ops are the SAME
                // IEEE operations the scalar loop performs (no FMLA
                // contraction), so the output is bit-identical. Runs after
                // the integer map/stencil passes (disjoint shapes — those
                // bail on FP classes) and before reduction_split. Kill
                // switch: `TRUST_CG_DISABLE_PASSES=neon_fmap`.
                if !is_disabled("neon_fmap") {
                    pm = pm.with_pass(Box::new(NeonFMapPass::new()));
                }
                // SOUND NEON AoS stride-2 complex-butterfly vectorizer: the
                // radix-2 FFT inner loop over `struct complex { f32 rp, ip; }`
                // (Stanford Oscar's Fft — clang -O3 vectorizes it, trust-cg
                // was fully scalar). One complex PAIR (`.4S`) per iteration on
                // the INTERLEAVED data: FADD/FSUB per lane + the REV64.4S
                // pair-swap + sign-mask EOR (the scalar FNEG, bitwise) +
                // FMUL/FMLA with broadcast twiddles — per-lane the SAME IEEE
                // ops and roundings the scalar loop performs (no contraction
                // introduced; the source's fused fmuladd stays fused), so
                // BIT-IDENTICAL. Entered only behind a runtime 7-pair
                // byte-range disjointness preamble (regime-C versioning,
                // wrap-safe modular-interval tests) that otherwise falls back
                // to the untouched scalar loop. Fail-closed on any deviation
                // from the exact butterfly dag. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=neon_butterfly`.
                if !is_disabled("neon_butterfly") {
                    pm = pm.with_pass(Box::new(NeonButterflyPass::new()));
                }
                // SOUND NEON early-exit linear-search (find/memchr) vectorizer:
                // `for i<n: if a[i]==key return i; return -1`. A purely additive
                // vector BLOCK FILTER runs in front of the UNCHANGED scalar loop:
                // per whole 16-element in-bounds block it CMEQs the loads against
                // a key splat and, on a PROVEN no-match block, skips it; on any-
                // hit (or a partial trailing block) it re-enters the scalar loop,
                // which computes the exact first-match index (delegated — no
                // vector lane ordering, so same-block and cross-block duplicates
                // are correct by the scalar scan). The over-read is a SUBSET of
                // the no-match scalar read set (the guard admits only whole blocks
                // within [0,n)); reads are pure (BAILS on stores / atomics; volatile
                // fails closed at lowering). Every other neon pass BAILS on this
                // early-exit shape. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=neon_find`.
                if !is_disabled("neon_find") {
                    pm = pm.with_pass(Box::new(NeonFindPass::new()));
                }
                // SOUND NEON IV-synthesized FP-reduction vectorizer:
                // `acc += f(i)` where `f(i)` is a pure lane-wise f64 dataflow of
                // the induction (`(double)i` via UCVTF/SCVTF) and loop-invariant
                // scalars (NO arrays/memory), combined by a PLAIN fadd. It
                // vectorizes only the INDEPENDENT per-lane term (`.2D`, x4 pairs)
                // and folds the lanes into the scalar accumulator with ORDERED
                // scalar fadds in iteration order — no reassociation, so the sum
                // is BIT-IDENTICAL to the scalar loop (clang -O3's own emission
                // for the flops kernels). Runs before reduction_split /
                // scalar_unroll (first shot at the FP-reduction loop); BAILS on a
                // fused accumulate, f32, non-unit step, stores/calls, or an extra
                // live-out — scalar_unroll's SERIAL unroll is the fallback. Kill
                // switch: `TRUST_CG_DISABLE_PASSES=neonfpred`.
                if !is_disabled("neonfpred") {
                    pm = pm.with_pass(Box::new(NeonFPRedPass::new()));
                }
                // SOUND NEON FP ARRAY-reduction vectorizer (memory-bearing sibling
                // of neon-fpred): `acc += a[i]*b[i]` / `acc += a[i]` over unit-stride
                // f64 arrays, PLUS the `f32 -> f64` widening dot (the fp-convert
                // kernel) via the proven vector FCVTL/FCVTL2. Coalesced LDP-Q loads
                // (widened by FCVTL for f32 streams) + ORDERED scalar drain (fused
                // fmadd preserved) = bit-identical to the scalar loop.
                //
                // ASYMMETRIC DEFAULT (measured): the `f32 -> f64` WIDENING
                // recognition fires BY DEFAULT — the FCVTL halved convert
                // throughput is a real win (fp-convert ~1.1x, bit-exact). The
                // NON-widening pure-`f64` recognition stays OPT-IN
                // (`TRUST_CG_ENABLE_NEONFARRAY=1` = full mode): the ordered-drain
                // ceiling is ~0% there and firing on the fused f64 ddot regresses
                // ~5% by stealing the loop from scalar_unroll's extract-free
                // unroll. Kill switch: `TRUST_CG_DISABLE_PASSES=neonfarray`.
                if !is_disabled("neonfarray") {
                    let farray = if pipeline_env_var("TRUST_CG_ENABLE_NEONFARRAY").is_some() {
                        NeonFArrayPass::new()
                    } else {
                        NeonFArrayPass::widening_only()
                    };
                    pm = pm.with_pass(Box::new(farray));
                }
                if !is_disabled("redsplit") {
                    pm = pm.with_pass(Box::new(ReductionSplit));
                }
                // Scalar ILP unroll: the load-bearing reduction loops nothing
                // above could take. SPLIT mode = 4 independent integer
                // accumulators (two's-complement reassociation, the
                // reduction_split argument) for i64-mul / gather-term
                // reductions no NEON path exists for; SERIAL mode =
                // order-preserving 4x unroll (bit-identical by construction —
                // FP chains and compound integer recurrences are NEVER
                // reassociated). Runs AFTER every vectorizer and
                // reduction_split (placement + a no-vector-path shape gate
                // mean it can never steal their loops) and BEFORE ext-addr,
                // which folds each unrolled lane's address chain. Fail-closed.
                // Kill switch: `TRUST_CG_DISABLE_PASSES=scalar_unroll`.
                if !is_disabled("scalar_unroll") {
                    pm = pm.with_pass(Box::new(ScalarUnrollPass::new()));
                }
                // Single-trip residual-loop collapse: decides the ALWAYS-TAKEN
                // exit branch of the one-iteration tail loop scalar-unroll's
                // full-unroll leaves behind (the iv enters as a compile-time
                // constant, so `iv+step` vs the constant bound is decidable)
                // and rewrites `BCond exit; B latch` into `B exit`, unlinking
                // the dead latch. Runs immediately AFTER scalar-unroll (whose
                // full-unroll mints these tails) and BEFORE ext-addr /
                // alias-hoist, so the straight-lined residual body's iv
                // becomes single-def and its loads hoistable like every other
                // lane (Shootout matrix lane 9, ~9% whole-program).
                // Fail-closed on every unproven shape. Compile-time kill
                // switch: `TCG_NO_RESID_COLLAPSE`; per-pass bisect:
                // `TRUST_CG_DISABLE_PASSES=residcollapse`.
                if !is_disabled("residcollapse") {
                    pm = pm.with_pass(Box::new(ResidTripCollapse));
                }
                // Second (LATE) UnfuseSerialFma instance: the NEON vectorizers
                // above emit ordered-drain reductions as IN-PLACE FmaddRR runs
                // (`FmaddRR [acc, a, b, acc]` — e.g. fp-convert's vectorized
                // sum), which do not exist at the early instance's position.
                // Loops the early instance already un-fused have no FMADDs
                // left, so this re-run only touches vectorizer output. Same
                // gate, same kill switch.
                if !is_disabled("unfusefma") {
                    pm = pm.with_pass(Box::new(UnfuseSerialFma));
                }
                // Extended-register addressing fold + select/flag fusion:
                // LATE scalar cleanups that MUST run after the NEON
                // vectorizers (whose recognizers decode the unfused
                // Sxtw/Madd/LdrRI and CSet/CmpRI/Csel chains) and before the
                // scheduler. Fail-closed; kill switches:
                // `TRUST_CG_DISABLE_PASSES=extaddr` / `selfuse`.
                if !is_disabled("extaddr") {
                    pm = pm.with_pass(Box::new(ExtRegAddrFold));
                }
                // Pointer-IV strength reduction: rewrite a register-offset 2D
                // array walk (`ldr [base, idx]` with `idx` affine in the loop
                // counter — the loop-invariant-addend shape ext-addr cannot
                // fold) into a preheader-initialized WALKING POINTER advanced
                // by an explicit AddRI+MovR carrier in the latch, deleting the
                // per-iteration index recompute (almabench planetpv's
                // k-loops). Runs AFTER the vectorizers and ext-addr so it only
                // claims accesses they left scalar/register-offset, and before
                // the scheduler. Fail-closed on every unproven shape; never
                // traces through a sign/zero-extend of a loop-variant index.
                // Compile-time kill switch: `TCG_NO_PTR_IV_SR`; per-pass
                // bisect: `TRUST_CG_DISABLE_PASSES=ptrivsr`.
                // Scalar post-index formation. Runs immediately AFTER ptr-iv-sr
                // and is disjoint from it by construction: ptr-iv-sr demands a
                // single-back-edge {header}/{header,latch} body, this one only
                // needs the load in the header, so a loop either pass rewrote is
                // no longer in the shape the other recognises. Kill switch
                // `TCG_NO_POST_INDEX`; bisect `TRUST_CG_DISABLE_PASSES=postindex`.
                if !is_disabled("postindex") {
                    pm = pm.with_pass(Box::new(PostIndexForm));
                }
                if !is_disabled("ptrivsr") {
                    pm = pm.with_pass(Box::new(PtrIvStrengthReduce));
                }
                // Late call-bearing exact-trip FULL unroll: replicate the
                // body of a proven-constant-trip counted loop whose body
                // CONTAINS a call, at K = N (the loop control then evaluates
                // once per entry instead of N times). Runs immediately AFTER
                // ptr-iv-sr — that ordering IS the pass: unrolling this shape
                // at the early `unroll` slot deletes the loop before ptr-iv-sr
                // can reduce it, so each clone keeps the unreduced
                // `lsl; madd; add; ldr` address chain. Toggling
                // TCG_NO_PTR_IV_SR around THIS slot reproduces that placement
                // exactly and prices it: almabench planetpv emits madd 16 /
                // lsl 9 either way when the order is right, madd 58 / lsl 51
                // when it is not (+42 = 6 arrays x 7 extra clones), and the
                // unreduced unroll is a WASH against not unrolling at all
                // (1.0095 vs 1.0094 PMC cycles) where the reduced one is
                // 0.9890. Here the clones inherit the walking-pointer body
                // and the unroll only removes work. Disjoint from
                // partial-unroll by construction (that tier refuses calls).
                // Purely structural: trip test, bound, step and exit edge are
                // untouched, so a mis-modeled trip count can only refuse.
                // Kill switch: `TCG_NO_CALL_UNROLL`; bisect key `callunroll`.
                if !is_disabled("callunroll") {
                    pm = pm.with_pass(Box::new(crate::loop_unroll::CallUnroll::new()));
                }
                // Alias-versioned loop-invariant load hoisting (LICM tier c):
                // versions an inner loop on a RUNTIME byte-range disjointness
                // check between its store range and each loop-invariant load,
                // hoisting the loads into the disjoint (fast) clone's preheader
                // and leaving the original loop untouched as the aliasing
                // fallback. Runs after ext-addr so it sees the folded
                // `ldr [base,#imm]` invariant loads the full-unroll exposes,
                // and before the scheduler. Fail-closed on every unbounded
                // store / unproven speculation / live-out clone value. Kill
                // switch: `TRUST_CG_DISABLE_PASSES=aliashoist`.
                if !is_disabled("aliashoist") {
                    pm = pm.with_pass(Box::new(AliasVersionedLoadHoist));
                }
                if !is_disabled("selfuse") {
                    pm = pm.with_pass(Box::new(SelectFlagFuse));
                }
                // Multiply-by-small-constant -> shift/add-sub strength reduction:
                // rewrite `MulRR x, C` / `Madd x, C, y` (C a proven small
                // compile-time constant expressible as ≤2 signed powers of two)
                // into `LslRI` + `AddRR`/`SubRR`, off the latency-3-4 MUL/MADD
                // critical path (p2_collatz's carried `c = c*3 + 1`). Fail-closed
                // via `unique_reaching_const`; emits only already-gate-credited
                // opcodes (no new surface). Runs DEAD LAST (after every
                // vectorizer, unroller, and addressing pass) so it NEVER hides a
                // multiply those passes must recognize — it only reduces the
                // multiplies that survive to final scalar code, immediately before
                // scheduling. The now-dead constant `Movz` is loop-invariant
                // (LICM-hoisted to the preheader), so leaving it uncollected costs
                // nothing on the hot path. Compile-time kill switch:
                // `TCG_NO_MUL_SHIFT_REDUCE`; per-pass bisect:
                // `TRUST_CG_DISABLE_PASSES=mulshift`.
                if !is_disabled("mulshift") {
                    pm = pm.with_pass(Box::new(MulShiftReduce));
                }
                // Shift-into-ADD/SUB fusion: collapse `t = LslRI(s,k); d =
                // AddRR/SubRR(x,t)` (single-use t) into the shifted-register
                // `d = AddRRShift/SubRRShift(x,s,k)` (ADD/SUB x, s, LSL #k). Runs
                // right after mul-shift-reduce so it also collapses that pass's
                // `LslRI`+`AddRR`/`SubRR` output (`x*(2^k±1)`) into ONE op, plus
                // any explicit `y + (x<<k)` / `y - (x<<k)`, and the LSR sibling
                // `t = LsrRI(s,k); d = AddRR(x,t)` -> `AddRRShiftLsr` (the
                // srem/sdiv magic sign-bit correction and udiv magic add-back;
                // `TCG_NO_LSR_ADD_FUSE` disables the LSR half alone).
                // Non-commutative for SUB (the shift binds to the subtrahend
                // only). Fail-closed. Kill
                // switch: `TRUST_CG_DISABLE_PASSES=shiftalufuse`.
                if !is_disabled("shiftalufuse") {
                    pm = pm.with_pass(Box::new(ShiftAluFuse));
                }
                // `LSR #k; AND #low_mask` -> UBFM/UBFX; see the O1 site for
                // proof authority and fail-closed guards.
                if !is_disabled("lsrandubfx") {
                    pm = pm.with_pass(Box::new(LsrAndUbfx));
                }
                // CSEL->CSINC increment fold: absorb a single-use `+1` select arm
                // into a `CSINC` (p2_collatz's `c*3+1` odd arm after
                // mul-shift-reduce+shift-alu-fuse expose the trailing `+1`).
                // Runs here so the `+1` is already the CSEL's direct operand.
                // Sound (exact select semantics); `Csinc` is already credited.
                // Kill switch: `TRUST_CG_DISABLE_PASSES=csincfold`.
                if !is_disabled("csincfold") {
                    pm = pm.with_pass(Box::new(CsincFold));
                }
                // PARTIAL (factor) unroll: replicate the body of a constant-trip
                // loop that is TOO LONG for any full unroller (every tier caps
                // at 4..16 trips) K times, with the `N mod K` remainder peeled
                // as a prologue. Runs LATE — after every vectorizer and
                // pattern-specific unroller has had first refusal on the native
                // counted shape, and before scheduling/mem-pair so the
                // replicated accesses can still pair. Purely structural: the
                // trip test, bound, step and exit edge are untouched, so a
                // mis-modeled trip count can only refuse to fire. Kill switch:
                // `TCG_NO_PARTIAL_UNROLL`; bisect key `partial_unroll`.
                if !is_disabled("partial_unroll") {
                    pm = pm.with_pass(Box::new(crate::loop_unroll::PartialUnroll::new()));
                }
                if !is_disabled("sched") {
                    pm = pm.with_pass(Box::new(PressureAwareScheduler));
                }
                // LDP/STP pair formation runs AFTER scheduling (adjacency is
                // near-final) but before regalloc (so the translation validator
                // checks every pair). Kill switch: `TRUST_CG_DISABLE_PASSES=mempair`.
                if !is_disabled("mempair") {
                    pm = pm.with_pass(Box::new(crate::mem_pair::MemPairFormation));
                }
                pm
            }
            OptLevel::O3 => {
                // Aggressive: same as O2 but iterated to fixpoint.
                // Vectorization before LICM (see O2 comment for rationale).
                //
                // Declarative rewrite (#393) runs before the standalone
                // RotateIdiom stage when the default is on. The kill switch
                // `TRUST_CG_DISABLE_PASSES=declrewrite` drops the pass for
                // forensic rollback.
                //
                // SROA (#391 Phase 2b) runs once before vectorization,
                // between GVN and VectorizationPass.
                let mut pm = PassManager::new()
                    .with_proof_optimization_metadata(self.proof_metadata.clone());
                // Consume exact post-ISel replay authority before any pass can
                // mutate the machine function it is bound to.
                if lattice_kernel_gate && !is_disabled("proof") {
                    pm = pm.with_pass(self.proof_optimization_pass());
                }
                let profile_use_enabled = !is_disabled("profileuse");
                let profile_hotness = profile_use_enabled
                    .then(|| self.pgo.profile_hotness())
                    .flatten();
                if let Some(profile) = self.pgo.profile_use.clone()
                    && profile_use_enabled
                {
                    pm = pm.with_pass(Box::new(ProfileUsePass::new(profile)));
                }
                if !is_disabled("inline") {
                    pm = pm.with_pass(Box::new(
                        FunctionInlining::new().with_profile_hotness(profile_hotness.clone()),
                    ));
                }
                // Sin/cos -> ___sincos_stret fusion (Darwin arm64). See the O2
                // branch for the placement rationale (early, pre-scheduler;
                // Darwin-gated). Kill switch: `TCG_NO_SINCOS_MERGE` /
                // `TRUST_CG_DISABLE_PASSES=sincosmerge`.
                if !is_disabled("sincosmerge") {
                    pm = pm.with_pass(Box::new(SincosMerge::new(self.target_is_darwin)));
                }
                // Loop-dead pure-computation deferral (almabench store
                // sinking). Runs EARLY — right after inlining/sincos-merge on
                // the pristine post-ISel shapes (the call-cluster and rotated
                // do-while recognizers depend on them), and before
                // addr-mode/CSE/scheduling rewrite the address chains. The
                // deferred loop it emits is then optimized by every later
                // pass. Kill switch: `TCG_NO_LOOP_DEAD_SINK` /
                // `TRUST_CG_DISABLE_PASSES=loopdeadsink`.
                if !is_disabled("loopdeadsink") {
                    pm = pm.with_pass(Box::new(LoopDeadPureSink));
                }
                if !is_disabled("addrmodeearly") {
                    pm = pm.with_pass(Box::new(AddrModeEarlyFormation));
                }
                if !lattice_kernel_gate && !is_disabled("proof") {
                    pm = pm.with_pass(self.proof_optimization_pass());
                }
                if !is_disabled("cfold") {
                    pm = pm.with_pass(self.constant_folding_pass());
                }
                if !is_disabled("copyprop") {
                    pm = pm.with_pass(Box::new(CopyPropagation));
                }
                if !is_disabled("cse") {
                    pm = pm.with_pass(Box::new(CommonSubexprElim));
                }
                if !is_disabled("gvn") {
                    pm = pm.with_pass(Box::new(GlobalValueNumbering));
                }
                if !is_disabled("sroa") {
                    pm = pm.with_pass(Box::new(ScalarReplacementOfAggregates));
                }
                if !is_disabled("vec") {
                    let mut vectorizer =
                        VectorizationPass::new().with_profile_hotness(profile_hotness.clone());
                    if let Some(enabled) = self.contains4_scanner_batch_rewrite_override {
                        vectorizer = vectorizer.with_contains4_scanner_batch_rewrite(enabled);
                    }
                    pm = pm.with_pass(Box::new(vectorizer));
                }
                if !is_disabled("licm") {
                    pm = pm.with_pass(Box::new(LoopInvariantCodeMotion));
                }
                if !is_disabled("strred") {
                    pm = pm.with_pass(Box::new(StrengthReduction));
                }
                if !is_disabled("unfusefma") {
                    pm = pm.with_pass(Box::new(UnfuseSerialFma));
                }
                // Invariant loop unswitching: version a small innermost loop
                // on a loop-invariant Cbz/Cbnz/CmpRI#0+BCond test so the
                // decision is made ONCE in the preheader (Queens' Try
                // `i < 8`: previously tested 8x per call after the bounded
                // early-exit unroll, with the boolean spilled post-RA — a
                // serialized ldur+cbnz per clone). MUST run immediately
                // BEFORE loop-unroll so both versions unroll cleanly.
                // Fail-closed. Kill switch: `TCG_NO_LOOP_UNSWITCH`; bisect
                // key `unswitch`.
                if !is_disabled("unswitch") {
                    pm = pm.with_pass(Box::new(LoopUnswitch));
                }
                if !is_disabled("unroll") {
                    pm = pm.with_pass(Box::new(LoopUnroll::new(profile_hotness.clone())));
                }
                // Late SROA (2nd instance): the const-addr full unroll above
                // (`TCG_NO_CONST_ADDR_UNROLL`) rewrites stack-array index
                // arithmetic into constant offsets; re-running SROA promotes
                // the now-constant-offset local array to scalars (salsa20's
                // `x[16]` stack round-trip). Kill switch: `TCG_NO_LATE_SROA`;
                // shares the `sroa` bisect key.
                if !is_disabled("sroa") && late_sroa_enabled() {
                    pm = pm.with_pass(Box::new(ScalarReplacementOfAggregates));
                }
                if !is_disabled("declrewrite") {
                    let (pass, report) = make_declarative_rewrite_pass_with_report(
                        &self.admitted_rewrite_records,
                        self.rewrite_admission_config,
                    );
                    pipeline_report.record_rewrite_admission_load(report);
                    pm = pm.with_pass(Box::new(pass));
                }
                // Peephole dropped: declarative rewrite covers it;
                // RotateIdiom carries pattern 53 (needs dominator info).
                // The `peep` bisect key now gates RotateIdiom.
                if !is_disabled("peep") {
                    pm = pm.with_pass(Box::new(RotateIdiom));
                }
                // EOR-with-rotate fusion: collapse `t = RorRI(s,k); d = EorRR(x,t)`
                // (single-use t) into the shifted-register `d = EorRRShift(x,s,k)`
                // (EOR x, s, ROR #k) — the consumer of the RorRI RotateIdiom just
                // created. Removes one instruction and one serial critical-path
                // node per ARX statement (salsa20). Fail-closed. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=eorrotfuse`.
                if !is_disabled("eorrotfuse") {
                    pm = pm.with_pass(Box::new(EorRotateFuse));
                }
                if !is_disabled("addrmode") {
                    pm = pm.with_pass(Box::new(AddrModeFormation));
                }
                if !is_disabled("cmpsel") {
                    pm = pm.with_pass(Box::new(CmpSelectCombine));
                }
                if !is_disabled("ifconv") {
                    pm = pm.with_pass(Box::new(IfConversion));
                }
                // AND+CMP#0 -> TST. MUST precede cmp-branch-fusion: that pass
                // rewrites CmpRI into Cbz/Cbnz and AndCmpFuse only matches a
                // surviving CmpRI, so the reverse order silently starves it.
                // Together they compose into LLVM's `tbz`. C-flag guarded (ANDS
                // clears C, SUBS #0 sets it). Kill switch:
                // `TRUST_CG_DISABLE_PASSES=andcmpfuse`.
                if !is_disabled("andcmpfuse") {
                    pm = pm.with_pass(Box::new(AndCmpFuse));
                }
                // `y = x ^ (x << k)`: consumers reading only bits [0,k) may read
                // `x`, shortening the dependency chain into a mispredicting
                // branch by one shifted-EOR. Purely an operand swap; the bit
                // range must be provably below k or the operand is left alone.
                // Kill switch: `TRUST_CG_DISABLE_PASSES=xorshiftdemanded`.
                if !is_disabled("xorshiftdemanded") {
                    pm = pm.with_pass(Box::new(XorshiftDemandedBits));
                }
                if !is_disabled("cmpbr") {
                    pm = pm.with_pass(Box::new(CmpBranchFusion));
                }
                // Profile-gated hot-latch AND-condition split. Runs right AFTER
                // cmp-branch-fusion (which forms the `cbnz t` its recogniser
                // matches). INERT without an attached profile — the default
                // compile stays byte-identical; with a profile it fires only in
                // the unpredictable taken-rate band (see latch_and_split.rs).
                // Kill switch: `TCG_NO_LATCH_AND_SPLIT`; bisect key `latchsplit`.
                if !is_disabled("latchsplit") {
                    pm = pm.with_pass(Box::new(LatchAndSplit::new(profile_hotness.clone())));
                }
                if !is_disabled("tailcall") {
                    pm = pm.with_pass(Box::new(TailCallOptimization));
                }
                if !is_disabled("dce") {
                    pm = pm.with_pass(self.dce_pass());
                }
                if !is_disabled("cfgsimp") {
                    pm = pm.with_pass(Box::new(CfgSimplify));
                }
                // Late tiny-loop-diamond if-conversion: convert an unpredictable
                // NON-AFFINE-recurrence-gated tiny pure-arm diamond (b1's
                // `if s&6==2 { acc=rotate_left(acc,7) }`) to a CSEL. Runs HERE —
                // after cfg-simplify canonicalizes it to a clean diamond, which
                // the primary if-convert (pre-dce/cfg-simplify) cannot see. Tight
                // gate (loop-resident + tiny pure arm + EOR self-recurrence) so it
                // stays branchy on predictable diamonds. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=tinyloop`.
                if !is_disabled("tinyloop") {
                    pm = pm.with_pass(Box::new(TinyLoopDiamondConvert));
                }
                // AArch64 bounds-check elimination — see the O2 comment. Same
                // late-machine-opt slot (post-cfgsimp, pre-looplatch/vectorize).
                // Default-ON kill switch: `TCG_NO_AARCH64_BCE`; per-pass bisect:
                // `TRUST_CG_DISABLE_PASSES=aarch64bce`.
                if !is_disabled("aarch64bce") {
                    pm = pm.with_pass(Box::new(AArch64BoundsCheckElimination::new()));
                }
                // Loop-carried store-to-load forwarding — see the O2 comment.
                // Same slot: right AFTER aarch64-bounds-check-elim, BEFORE the
                // unrollers/vectorizers. Closed-world, fail-closed; emits only
                // already-credited opcodes. Default-ON kill switch:
                // `TCG_NO_RECURRENCE_STORE_FWD`; per-pass bisect:
                // `TRUST_CG_DISABLE_PASSES=recurrence_store_fwd`.
                if !is_disabled("recurrence_store_fwd") {
                    pm = pm.with_pass(Box::new(RecurrenceStoreForward::new()));
                }
                // Counted-strided-store partial-unroll (x4) — see the O2 comment.
                // Same slot: AFTER aarch64-bounds-check-elim, BEFORE
                // closed-form-reduction/loop-latch-layout. Additive, wrap-free,
                // fail-safe; emits only already-credited opcodes (no udiv/mul).
                // Compile-time kill switch: `TCG_NO_STRIDED_STORE_UNROLL`;
                // per-pass bisect: `TRUST_CG_DISABLE_PASSES=strided_store_unroll`.
                // Normalize ISel's folded constant-trip `CmpRI` guards back to
                // `CmpRR(iv, movz)` BEFORE the vectorizers/unrollers, so
                // dc5916e's `cmp_imm12_fold` does not silently defeat their
                // constant-trip recognizers (matmul full-unroll, the dt-class FP
                // maps). Semantics-preserving. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=consttripnorm`.
                if !is_disabled("consttripnorm") {
                    pm = pm.with_pass(Box::new(crate::scalar_unroll::ConstTripGuardNormalize));
                }
                if !is_disabled("strided_store_unroll") {
                    pm = pm.with_pass(Box::new(StridedStoreUnroll::new()));
                }
                // RMW-MAC row-loop partial-unroll (x4) — see the O2 comment.
                // Same slot: AFTER aarch64-bounds-check-elim, BEFORE
                // closed-form-reduction/loop-latch-layout. Additive, wrap-free,
                // fail-safe; emits only already-credited opcodes (no udiv/mul).
                // Compile-time kill switch: `TCG_NO_MAC_ROW_UNROLL`; per-pass
                // bisect: `TRUST_CG_DISABLE_PASSES=mac_row_unroll`.
                // Matmul 1D register-blocking (T=8): recognize the whole
                // 3-deep bounds-checked matmul nest (distinct stack-local
                // a/b/c, read-only a/b, single c store, const N a multiple of
                // 8, L>=N*N) and splice a CHECK-FREE register-blocked fast path
                // (k/j interchange, 8 c accumulators held across the k-loop,
                // stores sunk to tile end) in FRONT of the untouched checked
                // nest — kept as the runtime-guarded fallback so mac-row-unroll
                // still fires on it. Store-sinking is sound because a/b/c are
                // distinct locals (a/b never written; c's only store is
                // c[i*N+j]); the tiled indices are provably < L so no per-access
                // check is emitted. Runs right BEFORE mac-row-unroll (which
                // handles the fallback's inner j-loop) and AFTER
                // aarch64-bounds-check-elim (the clean LdrRI/StrRI + Madd
                // address form). Purely additive, fail-closed, emits only
                // already-credited opcodes. Kill switch: `TCG_NO_MAC_REG_BLOCK`;
                // per-pass bisect: `TRUST_CG_DISABLE_PASSES=mac_reg_block`.
                if !is_disabled("mac_reg_block") {
                    pm = pm.with_pass(Box::new(MacRegBlock::new()));
                }
                if !is_disabled("mac_row_unroll") {
                    pm = pm.with_pass(Box::new(MacRowUnroll::new()));
                }
                // SOUND hoisted-range-guard crosswise-SWAP fast path (O3):
                // see the O2 comment. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=swap_range_guard`.
                if !is_disabled("swap_range_guard") {
                    pm = pm.with_pass(Box::new(SwapRangeGuardPass::new()));
                }
                // Closed-form (Faulhaber) reduction — see the O2 comment. Runs
                // before LoopLatchLayoutCombine and the split; iterated to
                // fixpoint at O3. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=closed_form_reduction`.
                if !is_disabled("closed_form_reduction") {
                    pm = pm.with_pass(Box::new(ClosedFormReduction));
                }
                // Delete provably-terminating, side-effect-free counted loops
                // (empty after upstream DCE). Fail-closed. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=deadloop`.
                if !is_disabled("deadloop") {
                    pm = pm.with_pass(Box::new(DeadCountedLoopElimination::new()));
                }
                if !is_disabled("looplatch") {
                    pm = pm.with_pass(Box::new(LoopLatchLayoutCombine));
                }
                // Reduction splitting (accumulator widening): break a
                // throughput-bound integer reduction's loop-carried chain into
                // N independent accumulators for ILP. Fail-closed: only fires on
                // the exact recognized constant-trip register-reduction shape.
                // Placed after DCE/CFG-simplify so it sees the cleaned-up loop.
                // SOUND NEON add-reduction vectorizer. Runs immediately BEFORE
                // reduction_split so it fires FIRST on lane-wise-vectorizable
                // reduction terms (e.g. `a += (i*7)|(i*3)`), lowering them to a
                // NEON vector accumulator + scalar tail. It BAILS (leaving the
                // scalar loop intact) on any shape it cannot prove lane-wise
                // equivalent, so reduction_split still handles those.
                if !is_disabled("neonreduce") {
                    pm = pm.with_pass(Box::new(NeonReducePass::new()));
                }
                // SOUND NEON array-reduction vectorizer: extends neon-reduce to
                // reductions whose term reads from READ-ONLY memory (`s +=
                // TERM(a[i], b[i], ...)`). Runs immediately after neon-reduce
                // (which BAILS on any load) and before reduction_split. Fires
                // only on the shapes it can prove lane-wise equivalent (i32
                // accumulator, `a[i]` loads, lane-wise ops) and BAILS otherwise.
                // Kill switch: `TRUST_CG_DISABLE_PASSES=neon_array`.
                if !is_disabled("neon_array") {
                    pm = pm.with_pass(Box::new(NeonArrayPass::new()));
                }
                // SOUND NEON byte-widening reduction into a u64 accumulator
                // (popcount-sum / byte-sum) — the case neon_array's i32-only
                // widening TRACK B and 2-block loop shape both miss (e.g.
                // v3_popcount). Composes already-proven CNT/UADDLP/ADD/UMOV +
                // the const-materialization MOVI and the shared-debt paired-Q
                // load, all now credited per-compile, so it promotes gate-clean.
                // Default-ON; kill switch: `TRUST_CG_DISABLE_PASSES=neon_bytesum`.
                if !is_disabled("neon_bytesum") {
                    pm = pm.with_pass(Box::new(NeonBytesumPass::new()));
                }
                // SOUND NEON min/max & bitwise array-reduction vectorizer:
                // extends neon-array to the non-add associative+commutative
                // reductions `m = max/min(m, TERM(a[i]))` (via `select(icmp)`)
                // and `m &= / |= / ^= TERM(a[i])`, plus the index-tracking
                // ARGMIN/ARGMAX shape (a 3rd carried var — best index — updated
                // under the SAME strict compare; first-occurrence preserved by a
                // (value, min-index) lexicographic exit fold). Runs immediately
                // after neon-array (which claims add/madd and BAILS on these)
                // and before reduction_split. i32-only; BAILS on i64, register
                // reductions, ambiguous / non-strict selects, and any
                // store/effect. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=neon_minmax`.
                if !is_disabled("neon_minmax") {
                    pm = pm.with_pass(Box::new(NeonMinMaxPass::new()));
                }
                // SOUND NEON predicated-sum array-reduction vectorizer (O3): see
                // the O2 comment. Add-rooted `s += select(...)`; fires only when
                // the term has a lane-wise select, lowering it to a proven
                // per-lane compare mask + branchless bitselect. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=neon_predsum`.
                if !is_disabled("neon_predsum") {
                    pm = pm.with_pass(Box::new(NeonPredSumPass::new()));
                }
                // SOUND NEON memory-MAP/STORE vectorizer (O3): see the O2 comment.
                // Fires only on provably-non-aliasing store loops; BAILS
                // otherwise. Kill switch: `TRUST_CG_DISABLE_PASSES=neon_map`.
                if !is_disabled("neon_map") {
                    pm = pm.with_pass(Box::new(NeonMapPass::new()));
                }
                // SOUND NEON per-byte 8-bit-reverse MAP vectorizer (O3): see the
                // O2 comment. Kill switch: `TRUST_CG_DISABLE_PASSES=neon_bitrev`.
                if !is_disabled("neon_bitrev") {
                    pm = pm.with_pass(Box::new(NeonBitrevPass::new()));
                }
                // SOUND NEON array-FILL store vectorizer (O3): see the O2
                // comment. Fires on the shared `__trustcg_array_fill_iN` helper
                // and any inline const/invariant fill; purely additive, removes
                // no bounds check. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=neon_fill`.
                if !is_disabled("neon_fill") {
                    pm = pm.with_pass(Box::new(NeonFillPass::new()));
                }
                // SOUND NEON affine IOTA-fill store vectorizer (O3): see the
                // O2 comment. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=neon_iota_fill`.
                if !is_disabled("neon_iota_fill") {
                    pm = pm.with_pass(Box::new(NeonIotaFillPass::new()));
                }
                // Conditional-store blind-write vectorization remains
                // unscheduled until typed ownership evidence is available.
                // SOUND NEON EARLY-EXIT SEARCH vectorizer (O3): see the O2 comment.
                // Kill switch: `TRUST_CG_DISABLE_PASSES=neon_find`.
                if !is_disabled("neon_find") {
                    pm = pm.with_pass(Box::new(NeonFindPass::new()));
                }
                // SOUND NEON STENCIL (windowed-read) vectorizer (O3): see the O2
                // comment. Fires only on provably-disjoint (noalias) out-vs-reads
                // stencils with the store at offset 0; BAILS otherwise. Kill
                // switch: `TRUST_CG_DISABLE_PASSES=neon_stencil`.
                if !is_disabled("neon_stencil") {
                    pm = pm.with_pass(Box::new(NeonStencilPass::new()));
                }
                // SOUND NEON elementwise-FP map/stencil/count vectorizer:
                // `out[i] = FTERM(a[i+k], ..., invariants)` (f32 `.4S` / f64
                // `.2D`) and the integer-accumulating FP count-above
                // `c += (a[i] > t)`. FP REDUCTIONS ARE NEVER TOUCHED
                // (reassociation would change results — they stay on the
                // order-preserving scalar path). Per-lane ops are the SAME
                // IEEE operations the scalar loop performs (no FMLA
                // contraction), so the output is bit-identical. Runs after
                // the integer map/stencil passes (disjoint shapes — those
                // bail on FP classes) and before reduction_split. Kill
                // switch: `TRUST_CG_DISABLE_PASSES=neon_fmap`.
                if !is_disabled("neon_fmap") {
                    pm = pm.with_pass(Box::new(NeonFMapPass::new()));
                }
                // SOUND NEON AoS stride-2 complex-butterfly vectorizer: the
                // radix-2 FFT inner loop over `struct complex { f32 rp, ip; }`
                // (Stanford Oscar's Fft — clang -O3 vectorizes it, trust-cg
                // was fully scalar). One complex PAIR (`.4S`) per iteration on
                // the INTERLEAVED data: FADD/FSUB per lane + the REV64.4S
                // pair-swap + sign-mask EOR (the scalar FNEG, bitwise) +
                // FMUL/FMLA with broadcast twiddles — per-lane the SAME IEEE
                // ops and roundings the scalar loop performs (no contraction
                // introduced; the source's fused fmuladd stays fused), so
                // BIT-IDENTICAL. Entered only behind a runtime 7-pair
                // byte-range disjointness preamble (regime-C versioning,
                // wrap-safe modular-interval tests) that otherwise falls back
                // to the untouched scalar loop. Fail-closed on any deviation
                // from the exact butterfly dag. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=neon_butterfly`.
                if !is_disabled("neon_butterfly") {
                    pm = pm.with_pass(Box::new(NeonButterflyPass::new()));
                }
                // SOUND NEON early-exit linear-search (find/memchr) vectorizer:
                // `for i<n: if a[i]==key return i; return -1`. A purely additive
                // vector BLOCK FILTER runs in front of the UNCHANGED scalar loop:
                // per whole 16-element in-bounds block it CMEQs the loads against
                // a key splat and, on a PROVEN no-match block, skips it; on any-
                // hit (or a partial trailing block) it re-enters the scalar loop,
                // which computes the exact first-match index (delegated — no
                // vector lane ordering, so same-block and cross-block duplicates
                // are correct by the scalar scan). The over-read is a SUBSET of
                // the no-match scalar read set (the guard admits only whole blocks
                // within [0,n)); reads are pure (BAILS on stores / atomics; volatile
                // fails closed at lowering). Every other neon pass BAILS on this
                // early-exit shape. Kill switch:
                // `TRUST_CG_DISABLE_PASSES=neon_find`.
                if !is_disabled("neon_find") {
                    pm = pm.with_pass(Box::new(NeonFindPass::new()));
                }
                // SOUND NEON IV-synthesized FP-reduction vectorizer:
                // `acc += f(i)` where `f(i)` is a pure lane-wise f64 dataflow of
                // the induction (`(double)i` via UCVTF/SCVTF) and loop-invariant
                // scalars (NO arrays/memory), combined by a PLAIN fadd. It
                // vectorizes only the INDEPENDENT per-lane term (`.2D`, x4 pairs)
                // and folds the lanes into the scalar accumulator with ORDERED
                // scalar fadds in iteration order — no reassociation, so the sum
                // is BIT-IDENTICAL to the scalar loop (clang -O3's own emission
                // for the flops kernels). Runs before reduction_split /
                // scalar_unroll (first shot at the FP-reduction loop); BAILS on a
                // fused accumulate, f32, non-unit step, stores/calls, or an extra
                // live-out — scalar_unroll's SERIAL unroll is the fallback. Kill
                // switch: `TRUST_CG_DISABLE_PASSES=neonfpred`.
                if !is_disabled("neonfpred") {
                    pm = pm.with_pass(Box::new(NeonFPRedPass::new()));
                }
                // SOUND NEON FP ARRAY-reduction vectorizer (memory-bearing sibling
                // of neon-fpred): `acc += a[i]*b[i]` / `acc += a[i]` over unit-stride
                // f64 arrays, PLUS the `f32 -> f64` widening dot (the fp-convert
                // kernel) via the proven vector FCVTL/FCVTL2. Coalesced LDP-Q loads
                // (widened by FCVTL for f32 streams) + ORDERED scalar drain (fused
                // fmadd preserved) = bit-identical to the scalar loop.
                //
                // ASYMMETRIC DEFAULT (measured): the `f32 -> f64` WIDENING
                // recognition fires BY DEFAULT — the FCVTL halved convert
                // throughput is a real win (fp-convert ~1.1x, bit-exact). The
                // NON-widening pure-`f64` recognition stays OPT-IN
                // (`TRUST_CG_ENABLE_NEONFARRAY=1` = full mode): the ordered-drain
                // ceiling is ~0% there and firing on the fused f64 ddot regresses
                // ~5% by stealing the loop from scalar_unroll's extract-free
                // unroll. Kill switch: `TRUST_CG_DISABLE_PASSES=neonfarray`.
                if !is_disabled("neonfarray") {
                    let farray = if pipeline_env_var("TRUST_CG_ENABLE_NEONFARRAY").is_some() {
                        NeonFArrayPass::new()
                    } else {
                        NeonFArrayPass::widening_only()
                    };
                    pm = pm.with_pass(Box::new(farray));
                }
                if !is_disabled("redsplit") {
                    pm = pm.with_pass(Box::new(ReductionSplit));
                }
                // Scalar ILP unroll (O3): see the O2 comment. Idempotent (the
                // inserted 3-block main loop and the tail's multi-pred entry
                // are both rejected by the recognizer), so fixpoint iteration
                // is safe. Kill switch: `TRUST_CG_DISABLE_PASSES=scalar_unroll`.
                if !is_disabled("scalar_unroll") {
                    pm = pm.with_pass(Box::new(ScalarUnrollPass::new()));
                }
                // Single-trip residual-loop collapse (O3) — see the O2
                // comment. Idempotent under fixpoint: the rewritten block ends
                // in a single unconditional `B` (no `BCond`+`B` pair left), so
                // the recognizer never re-matches a collapsed header. Same
                // kill switches (`TCG_NO_RESID_COLLAPSE` /
                // `TRUST_CG_DISABLE_PASSES=residcollapse`).
                if !is_disabled("residcollapse") {
                    pm = pm.with_pass(Box::new(ResidTripCollapse));
                }
                // Second (LATE) UnfuseSerialFma instance: the NEON vectorizers
                // above emit ordered-drain reductions as IN-PLACE FmaddRR runs
                // (`FmaddRR [acc, a, b, acc]` — e.g. fp-convert's vectorized
                // sum), which do not exist at the early instance's position.
                // Loops the early instance already un-fused have no FMADDs
                // left, so this re-run only touches vectorizer output. Same
                // gate, same kill switch.
                if !is_disabled("unfusefma") {
                    pm = pm.with_pass(Box::new(UnfuseSerialFma));
                }
                // Extended-register addressing fold + select/flag fusion —
                // see the O2 comment. Both are idempotent (each fold consumes
                // its matched chain), so O3 fixpoint iteration is safe; the
                // vectorizers bail cleanly on already-folded shapes.
                if !is_disabled("extaddr") {
                    pm = pm.with_pass(Box::new(ExtRegAddrFold));
                }
                // Pointer-IV strength reduction — see the O2 comment. Safe
                // under fixpoint iteration: a rewritten access is a
                // zero-offset LdrRI/StrRI (no LdrRO/StrRO left to re-claim),
                // so the pass reports no change on re-runs.
                // Scalar post-index formation. Runs immediately AFTER ptr-iv-sr
                // and is disjoint from it by construction: ptr-iv-sr demands a
                // single-back-edge {header}/{header,latch} body, this one only
                // needs the load in the header, so a loop either pass rewrote is
                // no longer in the shape the other recognises. Kill switch
                // `TCG_NO_POST_INDEX`; bisect `TRUST_CG_DISABLE_PASSES=postindex`.
                if !is_disabled("postindex") {
                    pm = pm.with_pass(Box::new(PostIndexForm));
                }
                if !is_disabled("ptrivsr") {
                    pm = pm.with_pass(Box::new(PtrIvStrengthReduce));
                }
                // Late call-bearing exact-trip FULL unroll: replicate the
                // body of a proven-constant-trip counted loop whose body
                // CONTAINS a call, at K = N (the loop control then evaluates
                // once per entry instead of N times). Runs immediately AFTER
                // ptr-iv-sr — that ordering IS the pass: unrolling this shape
                // at the early `unroll` slot deletes the loop before ptr-iv-sr
                // can reduce it, so each clone keeps the unreduced
                // `lsl; madd; add; ldr` address chain. Toggling
                // TCG_NO_PTR_IV_SR around THIS slot reproduces that placement
                // exactly and prices it: almabench planetpv emits madd 16 /
                // lsl 9 either way when the order is right, madd 58 / lsl 51
                // when it is not (+42 = 6 arrays x 7 extra clones), and the
                // unreduced unroll is a WASH against not unrolling at all
                // (1.0095 vs 1.0094 PMC cycles) where the reduced one is
                // 0.9890. Here the clones inherit the walking-pointer body
                // and the unroll only removes work. Disjoint from
                // partial-unroll by construction (that tier refuses calls).
                // Purely structural: trip test, bound, step and exit edge are
                // untouched, so a mis-modeled trip count can only refuse.
                // Kill switch: `TCG_NO_CALL_UNROLL`; bisect key `callunroll`.
                if !is_disabled("callunroll") {
                    pm = pm.with_pass(Box::new(crate::loop_unroll::CallUnroll::new()));
                }
                // Alias-versioned load hoisting (LICM tier c) — see the O2
                // comment. Self-limiting under fixpoint: the slow loop's new
                // preheader is a two-successor check block (fails the
                // unconditional-entry gate on re-run) and the fast clone has no
                // hoistable loads left, so it fires at most once per loop.
                if !is_disabled("aliashoist") {
                    pm = pm.with_pass(Box::new(AliasVersionedLoadHoist));
                }
                if !is_disabled("selfuse") {
                    pm = pm.with_pass(Box::new(SelectFlagFuse));
                }
                // Multiply-by-small-constant -> shift/add-sub strength reduction:
                // rewrite `MulRR x, C` / `Madd x, C, y` (C a proven small
                // compile-time constant expressible as ≤2 signed powers of two)
                // into `LslRI` + `AddRR`/`SubRR`, off the latency-3-4 MUL/MADD
                // critical path (p2_collatz's carried `c = c*3 + 1`). Fail-closed
                // via `unique_reaching_const`; emits only already-gate-credited
                // opcodes (no new surface). Runs DEAD LAST (after every
                // vectorizer, unroller, and addressing pass) so it NEVER hides a
                // multiply those passes must recognize — it only reduces the
                // multiplies that survive to final scalar code, immediately before
                // scheduling. The now-dead constant `Movz` is loop-invariant
                // (LICM-hoisted to the preheader), so leaving it uncollected costs
                // nothing on the hot path. Compile-time kill switch:
                // `TCG_NO_MUL_SHIFT_REDUCE`; per-pass bisect:
                // `TRUST_CG_DISABLE_PASSES=mulshift`.
                if !is_disabled("mulshift") {
                    pm = pm.with_pass(Box::new(MulShiftReduce));
                }
                // Shift-into-ADD/SUB fusion: collapse `t = LslRI(s,k); d =
                // AddRR/SubRR(x,t)` (single-use t) into the shifted-register
                // `d = AddRRShift/SubRRShift(x,s,k)` (ADD/SUB x, s, LSL #k). Runs
                // right after mul-shift-reduce so it also collapses that pass's
                // `LslRI`+`AddRR`/`SubRR` output (`x*(2^k±1)`) into ONE op, plus
                // any explicit `y + (x<<k)` / `y - (x<<k)`, and the LSR sibling
                // `t = LsrRI(s,k); d = AddRR(x,t)` -> `AddRRShiftLsr` (the
                // srem/sdiv magic sign-bit correction and udiv magic add-back;
                // `TCG_NO_LSR_ADD_FUSE` disables the LSR half alone).
                // Non-commutative for SUB (the shift binds to the subtrahend
                // only). Fail-closed. Kill
                // switch: `TRUST_CG_DISABLE_PASSES=shiftalufuse`.
                if !is_disabled("shiftalufuse") {
                    pm = pm.with_pass(Box::new(ShiftAluFuse));
                }
                // `LSR #k; AND #low_mask` -> UBFM/UBFX; see the O1 site for
                // proof authority and fail-closed guards.
                if !is_disabled("lsrandubfx") {
                    pm = pm.with_pass(Box::new(LsrAndUbfx));
                }
                // CSEL->CSINC increment fold: absorb a single-use `+1` select arm
                // into a `CSINC` (p2_collatz's `c*3+1` odd arm after
                // mul-shift-reduce+shift-alu-fuse expose the trailing `+1`).
                // Runs here so the `+1` is already the CSEL's direct operand.
                // Sound (exact select semantics); `Csinc` is already credited.
                // Kill switch: `TRUST_CG_DISABLE_PASSES=csincfold`.
                if !is_disabled("csincfold") {
                    pm = pm.with_pass(Box::new(CsincFold));
                }
                // PARTIAL (factor) unroll — see the O2 comment. Kill switch:
                // `TCG_NO_PARTIAL_UNROLL`; bisect key `partial_unroll`.
                if !is_disabled("partial_unroll") {
                    pm = pm.with_pass(Box::new(crate::loop_unroll::PartialUnroll::new()));
                }
                if !is_disabled("sched") {
                    pm = pm.with_pass(Box::new(PressureAwareScheduler));
                }
                // LDP/STP pair formation runs AFTER scheduling (adjacency is
                // near-final) but before regalloc (so the translation validator
                // checks every pair). Kill switch: `TRUST_CG_DISABLE_PASSES=mempair`.
                if !is_disabled("mempair") {
                    pm = pm.with_pass(Box::new(crate::mem_pair::MemPairFormation));
                }
                pm
            }
        };

        (pm, pipeline_report)
    }

    /// Return the number of passes registered for the current optimization
    /// level (single iteration). For `O3` this is the per-iteration count;
    /// actual executions may be higher due to fixpoint iteration.
    pub fn pass_count(&self) -> usize {
        self.build_pass_manager().num_passes()
    }

    fn run_pass_manager(&self, pm: &mut PassManager, func: &mut MachFunction) -> PassStats {
        match self.level {
            OptLevel::O0 => {
                // No-op, return empty stats.
                PassStats::default()
            }
            OptLevel::O1 | OptLevel::O2 | OptLevel::Os => {
                let stats = pm.run_once_with_stats(func);
                self.run_post_convergence(func, None);
                stats
            }
            OptLevel::O3 => {
                // Iterate to fixed point (max 4 iterations to bound compile time).
                // The analysis cache in PassManager avoids redundant domtree
                // recomputation within each iteration.
                let stats = pm.run_to_fixpoint(func, 4);
                self.run_post_convergence(func, None);
                stats
            }
        }
    }

    /// Single-shot passes that must see the CONVERGED function and whose
    /// output must never feed back into the iterative pipeline. Currently:
    /// the extended loop rotation — rotating a while-loop moves the natural
    /// loop's header off its test block, a shape the vectorizers' NATIVE
    /// classifiers must never observe mid-convergence (the 2026-08-13
    /// v2_memfill wrong-abort class).
    fn run_post_convergence(
        &self,
        func: &mut MachFunction,
        provenance: Option<&mut ProvenanceMap>,
    ) {
        let disabled = std::env::var("TRUST_CG_DISABLE_PASSES").unwrap_or_default();
        if disabled.split(',').any(|d| d.trim() == "looplatch") {
            return;
        }
        crate::loop_latch_layout::run_extended_loop_rotation(func, provenance);
    }

    fn run_pass_manager_with_provenance(
        &self,
        pm: &mut PassManager,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> PassStats {
        match self.level {
            OptLevel::O0 => PassStats::default(),
            OptLevel::O1 | OptLevel::O2 | OptLevel::Os => {
                let stats = pm.run_once_with_stats_and_provenance(func, provenance);
                self.run_post_convergence(func, Some(provenance));
                stats
            }
            OptLevel::O3 => {
                let stats = pm.run_to_fixpoint_with_provenance(func, provenance, 4);
                self.run_post_convergence(func, Some(provenance));
                stats
            }
        }
    }

    /// Run the optimization pipeline on a machine function.
    ///
    /// Returns statistics about the optimization run.
    pub fn run(&self, func: &mut MachFunction) -> PassStats {
        let mut pm = self.build_pass_manager();
        self.run_pass_manager(&mut pm, func)
    }

    /// Run the optimization pipeline and return build-time observability.
    pub fn run_with_report(&self, func: &mut MachFunction) -> OptimizationPipelineRunReport {
        let (mut pm, pipeline_report) = self.build_pass_manager_with_report();
        let pass_stats = self.run_pass_manager(&mut pm, func);
        OptimizationPipelineRunReport {
            pass_stats,
            pipeline_report,
        }
    }

    /// Run the optimization pipeline with access to a provenance map.
    ///
    /// This is an additive API for callers that are ready to preserve
    /// `ProvenanceMap` metadata through optimization. Existing callers can
    /// continue using [`OptimizationPipeline::run`].
    pub fn run_with_provenance(
        &self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> PassStats {
        let mut pm = self.build_pass_manager();
        self.run_pass_manager_with_provenance(&mut pm, func, provenance)
    }

    /// Run the provenance-aware optimization pipeline with build-time observability.
    pub fn run_with_provenance_and_report(
        &self,
        func: &mut MachFunction,
        provenance: &mut ProvenanceMap,
    ) -> OptimizationPipelineRunReport {
        let (mut pm, pipeline_report) = self.build_pass_manager_with_report();
        let pass_stats = self.run_pass_manager_with_provenance(&mut pm, func, provenance);
        OptimizationPipelineRunReport {
            pass_stats,
            pipeline_report,
        }
    }
}

impl Default for OptimizationPipeline {
    fn default() -> Self {
        Self::new(OptLevel::O2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interfaces::ProofDiagnosticCode;
    use crate::pgo::{BlockProfile, FunctionProfile, ProfData};
    use crate::proof_opts::OptCertificateKind;
    use trust_cg_ir::{
        AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, PassId,
        ProofAnnotation, ProofDivergence, ProofFact, ProvenanceMap, RegClass, Signature,
        TrustIrInstId, VReg,
        regs::{X0, X1, X2},
    };

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn vreg32(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }

    fn imm(val: i64) -> MachOperand {
        MachOperand::Imm(val)
    }

    fn preg(reg: trust_cg_ir::PReg) -> MachOperand {
        MachOperand::PReg(reg)
    }

    /// Build a simple vectorizable add loop (i32, trip count 100).
    ///
    /// ```text
    ///   bb0 (entry) -> bb1
    ///   bb1 (header): add v2 = v0 + v1 (i32), cmp v3 #100, bcond bb2/bb3
    ///   bb3 (latch): br bb1
    ///   bb2 (exit): ret
    /// ```
    fn make_vectorizable_loop() -> (MachFunction, InstId) {
        let mut func = MachFunction::new(
            "pipeline_vec_loop".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        // bb0: branch to header
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        // bb1 (header): add v2 = v0 + v1 (i32)
        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg32(2), vreg32(0), vreg32(1)],
        ));
        func.append_inst(bb1, add);

        // cmp v3, #100
        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg32(3), imm(100)],
        ));
        func.append_inst(bb1, cmp);

        // bcond exit or latch
        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

        // bb3 (latch): branch back to header
        let br3 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb3, br3);

        // bb2 (exit): ret
        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb3, bb1);

        (func, add)
    }

    /// Build a vectorizable loop with add + sub + mul (i32, trip count 100).
    fn make_multi_op_vectorizable_loop() -> (MachFunction, Vec<InstId>) {
        let mut func = MachFunction::new(
            "pipeline_multi_vec".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        // add v2 = v0 + v1
        let add = func.push_inst(MachInst::new(
            AArch64Opcode::AddRR,
            vec![vreg32(2), vreg32(0), vreg32(1)],
        ));
        func.append_inst(bb1, add);

        // sub v3 = v2 - v1
        let sub = func.push_inst(MachInst::new(
            AArch64Opcode::SubRR,
            vec![vreg32(3), vreg32(2), vreg32(1)],
        ));
        func.append_inst(bb1, sub);

        // mul v4 = v3 * v0
        let mul = func.push_inst(MachInst::new(
            AArch64Opcode::MulRR,
            vec![vreg32(4), vreg32(3), vreg32(0)],
        ));
        func.append_inst(bb1, mul);

        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg32(5), imm(100)],
        ));
        func.append_inst(bb1, cmp);

        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

        let br3 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb3, br3);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb3, bb1);

        (func, vec![add, sub, mul])
    }

    fn make_profitable_small_vectorization_loop() -> (MachFunction, Vec<InstId>) {
        let mut func = MachFunction::new(
            "pipeline_hot_small_vec".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let mut adds = Vec::new();
        for id in 2..12 {
            let add = func.push_inst(MachInst::new(
                AArch64Opcode::AddRR,
                vec![vreg32(id), vreg32(0), vreg32(1)],
            ));
            func.append_inst(bb1, add);
            adds.push(add);
        }

        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg32(20), imm(4)],
        ));
        func.append_inst(bb1, cmp);

        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

        let br3 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb3, br3);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb3, bb1);

        (func, adds)
    }

    fn small_vectorization_profile(header_hits: u64, function_count: u64) -> ProfData {
        let mut profile = ProfData::new(0x396);
        let mut function = FunctionProfile::new("pipeline_hot_small_vec");
        function.call_count = function_count;
        function
            .blocks
            .push(BlockProfile::new(BlockId(1).0, header_hits));
        profile.functions.push(function);
        profile
    }

    fn make_pipeline_counting_loop(trip_count: i64) -> MachFunction {
        let mut func = MachFunction::new(
            "pipeline_hot_unroll_loop".to_string(),
            Signature::new(vec![], vec![]),
        );
        let bb0 = func.entry;
        let bb1 = func.create_block();
        let bb2 = func.create_block();
        let bb3 = func.create_block();

        let init = func.push_inst(MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(0)]));
        func.append_inst(bb0, init);
        let br0 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb0, br0);

        let phi = func.push_inst(MachInst::new(
            AArch64Opcode::Phi,
            vec![
                vreg(1),
                vreg(0),
                MachOperand::Block(bb0),
                vreg(3),
                MachOperand::Block(bb3),
            ],
        ));
        func.append_inst(bb1, phi);
        let cmp = func.push_inst(MachInst::new(
            AArch64Opcode::CmpRI,
            vec![vreg(1), imm(trip_count)],
        ));
        func.append_inst(bb1, cmp);
        let bcond = func.push_inst(MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Block(bb2), MachOperand::Block(bb3)],
        ));
        func.append_inst(bb1, bcond);

        let body_work = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(2), vreg(1), imm(10)],
        ));
        func.append_inst(bb3, body_work);
        let iv_inc = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![vreg(3), vreg(1), imm(1)],
        ));
        func.append_inst(bb3, iv_inc);
        let br3 = func.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Block(bb1)],
        ));
        func.append_inst(bb3, br3);

        let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
        func.append_inst(bb2, ret);

        func.add_edge(bb0, bb1);
        func.add_edge(bb1, bb2);
        func.add_edge(bb1, bb3);
        func.add_edge(bb3, bb1);

        func
    }

    fn loop_unroll_profile(header_hits: u64, function_count: u64) -> ProfData {
        let mut profile = ProfData::new(0x829);
        let mut function = FunctionProfile::new("pipeline_hot_unroll_loop");
        function.call_count = function_count;
        function
            .blocks
            .push(BlockProfile::new(BlockId(1).0, header_hits));
        profile.functions.push(function);
        profile
    }

    fn make_func_with_insts(insts: Vec<MachInst>) -> MachFunction {
        let mut func =
            MachFunction::new("test_pipeline".to_string(), Signature::new(vec![], vec![]));
        let block = func.entry;
        for inst in insts {
            let id = func.push_inst(inst);
            func.append_inst(block, id);
        }
        func
    }

    fn make_and_cmp_branch_candidate() -> MachFunction {
        let mut func = MachFunction::new(
            "and_cmp_branch_pipeline".to_string(),
            Signature::new(vec![], vec![]),
        );
        let entry = func.entry;
        let taken = func.create_block();
        let fallthrough = func.create_block();

        for inst in [
            MachInst::new(
                AArch64Opcode::AndRI,
                vec![vreg(2), vreg(0), MachOperand::Imm(1)],
            ),
            MachInst::new(AArch64Opcode::CmpRI, vec![vreg(2), MachOperand::Imm(0)]),
            MachInst::new(
                AArch64Opcode::BCond,
                vec![MachOperand::Imm(0), MachOperand::Block(taken)],
            ),
        ] {
            let id = func.push_inst(inst);
            func.append_inst(entry, id);
        }

        // Keep the two successors observably different so CFG simplification
        // cannot erase the conditional branch before the composition is seen.
        let store = func.push_inst(MachInst::new(
            AArch64Opcode::StrRI,
            vec![vreg(3), vreg(4), MachOperand::Imm(0)],
        ));
        func.append_inst(taken, store);
        for block in [taken, fallthrough] {
            let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
            func.append_inst(block, ret);
        }
        func.add_edge(entry, taken);
        func.add_edge(entry, fallthrough);
        func
    }

    #[test]
    fn and_cmp_fuse_precedes_cmp_branch_and_composes_to_tbz_at_o2_o3() {
        with_disable_passes_env(None, || {
            for level in [OptLevel::O2, OptLevel::O3] {
                let manager = OptimizationPipeline::new(level).build_pass_manager();
                let names = manager.pass_names();
                let and_cmp = names
                    .iter()
                    .position(|name| *name == "and-cmp-fuse")
                    .expect("optimized pipeline must schedule AndCmpFuse");
                let cmp_branch = names
                    .iter()
                    .position(|name| *name == "cmp-branch-fusion")
                    .expect("optimized pipeline must schedule CmpBranchFusion");
                assert!(
                    and_cmp < cmp_branch,
                    "{level:?}: AndCmpFuse must run before CmpBranchFusion"
                );

                let mut func = make_and_cmp_branch_candidate();
                let mut and_cmp_pass = AndCmpFuse;
                assert!(
                    and_cmp_pass.run(&mut func),
                    "{level:?}: TST fusion must fire"
                );
                let mut cmp_branch_pass = CmpBranchFusion;
                assert!(
                    cmp_branch_pass.run(&mut func),
                    "{level:?}: TST+B.cond branch fusion must fire"
                );
                let opcodes = func
                    .block_order
                    .iter()
                    .flat_map(|block| func.block(*block).insts.iter())
                    .map(|id| func.inst(*id).opcode)
                    .collect::<Vec<_>>();
                assert_eq!(
                    opcodes
                        .iter()
                        .filter(|op| **op == AArch64Opcode::Tbz)
                        .count(),
                    1,
                    "{level:?}: AND+CMP+B.EQ must compose to exactly one TBZ: {opcodes:?}"
                );
                assert!(
                    !opcodes.iter().any(|op| matches!(
                        *op,
                        AArch64Opcode::AndRI | AArch64Opcode::CmpRI | AArch64Opcode::Tst
                    )),
                    "{level:?}: no unfused AND/CMP/TST residue expected: {opcodes:?}"
                );
            }
        });
    }

    #[test]
    fn certified_pass_execution_records_const_fold_and_dce_runs() {
        let m0 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(2)]);
        let m1 = MachInst::new(AArch64Opcode::MovI, vec![vreg(1), imm(3)]);
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(2), vreg(0), vreg(1)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m0, m1, add, ret]);

        let stats = OptimizationPipeline::new(OptLevel::O2)
            .with_certified_pass_execution()
            .run(&mut func);

        let pass_names = stats
            .certified_pass_runs
            .iter()
            .map(|run| run.pass_name.as_str())
            .collect::<Vec<_>>();
        assert!(pass_names.contains(&"const-fold-bv64"));
        assert!(pass_names.contains(&"dce-pure-unused"));
        assert!(
            stats
                .certified_pass_runs
                .iter()
                .all(|run| run.is_verified())
        );
    }

    fn make_no_overflow_pipeline_func() -> MachFunction {
        let adds = MachInst::new(AArch64Opcode::AddsRR, vec![vreg(0), vreg(1), vreg(2)])
            .with_proof(ProofAnnotation::NoOverflow);
        let trap = MachInst::new(
            AArch64Opcode::TrapOverflow,
            vec![imm(0x06), MachOperand::Block(trust_cg_ir::BlockId(1))],
        );
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![adds, trap, ret]);
        func.create_block();
        func
    }

    fn make_early_addrmode_store_pair_candidate() -> MachFunction {
        let add0 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(3), vreg(2), imm(0)]);
        let str0 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(0), vreg(3), imm(0)]);
        let add1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(4), vreg(2), imm(8)]);
        let str1 = MachInst::new(AArch64Opcode::StrRI, vec![vreg(1), vreg(4), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        make_func_with_insts(vec![add0, str0, add1, str1, ret])
    }

    fn admitted_rewrite_json() -> String {
        serde_json::json!({
            "schema": crate::rewrite::REWRITE_ADMISSION_SCHEMA,
            "schema_version": crate::rewrite::REWRITE_ADMISSION_SCHEMA_VERSION,
            "source_region": {
                "source_region_hash": "sha256:region",
                "hash_algorithm": "sha256",
                "kernel_family": "ay_lra_sparse_substitute",
                "kernel_name": "ay_lra_sparse_substitute",
                "function_symbol": "_trust_cg_ay_lra_sparse_substitute",
                "region_label": "bb0:0..2"
            },
            "proof_assumptions": [],
            "target": {
                "arch": "aarch64",
                "target_triple": "aarch64-apple-darwin",
                "abi": "aapcs64",
                "data_layout": "e-m:o-i64:64-i128:128-n32:64-S128",
                "cpu": "apple-m2",
                "features": ["+neon"]
            },
            "cost_context": {
                "cost_model": "trust-cg-aarch64",
                "cost_model_version": "2026.04",
                "profile": "named-kernel-hot",
                "source_cost": 12,
                "replacement_cost": 8,
                "notes": []
            },
            "transform": {
                "name": "ay_lra_sparse_add_zero",
                "version": "v1",
                "rule_proposal_hash": 17,
                "discovered_rule_name": "ay_lra_sparse_add_zero",
                "discovered_rule_proof_hash": 48879,
                "certificate_hash": "0000000000000000feedfacecafebeef",
                "certificate_validation_hash": "00000000000000000000000000005678"
            },
            "evidence": {
                "kind": "ay_equivalence_proof",
                "proof_hash": 48879,
                "cegis_iterations": 2
            },
            "aarch64_cost_delta": 4,
            "admission_state": "admitted",
            "allowlist": {
                "kernel_family": "ay_lra_sparse_substitute",
                "kernel_name": "ay_lra_sparse_substitute",
                "allowlist_entry": "rewrite-admission/ay-lra-sparse-substitute-v1",
                "allowlisted": true
            },
            "product_gates": {
                "replay_passed": true,
                "telemetry_guarded": true,
                "rollback_or_deopt_available": true,
                "product_promotion_approved": true
            },
            "proof_guided_admission": {
                "schema": "trust-cg.proof_guided_admission.verdict.v1",
                "schema_version": 1,
                "issue": 800,
                "disposition": "accepted",
                "rejection_reasons": [],
                "consumed_proof_facts": [
                    "ay-lra-sparse-substitute-row-order",
                    "ay-lra-sparse-output-bounds",
                    "ay-lra-sparse-overflow",
                    "ay-lra-sparse-alias-policy",
                    "ay-lra-basis-epoch"
                ],
                "transform_name": "ay_lra_sparse_add_zero",
                "transform_version": "v1",
                "source_trust_ir_region_hash": "sha256:region",
                "target_aarch64_region_hash": "machir:ay-lra-sparse-add-zero",
                "validation_result_hash": "00000000000000000000000000005678",
                "manifest_hash": "sha256:ay-lra-sparse-substitute-manifest",
                "runtime_status_contract": "ay_lra_status_abi_v1",
                "replay_artifact_root": "replay/ay_lra_sparse_substitute",
                "telemetry_event_id": "telemetry/ay_lra_sparse_substitute/admitted",
                "telemetry_useful_native_applications": 0,
                "rollback_or_disable_knob": "trust_cg_disable_admitted_rewrite_ay_lra_sparse_substitute"
            },
            "certificate_identity": {
                "producer": "trust-cg-opt.proof-opts",
                "certificate_hash": "0000000000000000feedfacecafebeef",
                "certificate_chain_id": "ay_lra_sparse_add_zero@v1:00000000000000000000000000005678"
            },
            "ay_lra_manifest_binding": {
                "schema": "trust-cg.ay_lra.proof_consumption_manifest.v1",
                "schema_version": 1,
                "issue": 796,
                "kernel_family": "ay_lra_sparse_substitute",
                "proof_family": "ay_lra_sparse_substitute",
                "allowlist_family": "ay_lra_sparse_substitute",
                "required_certificate_dependencies": [
                    "ay-lra-sparse-substitute-row-order",
                    "ay-lra-sparse-output-bounds",
                    "ay-lra-sparse-overflow",
                    "ay-lra-sparse-alias-policy",
                    "ay-lra-basis-epoch"
                ]
            }
        })
        .to_string()
    }

    #[test]
    fn test_o0_no_change() {
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ret]);

        let pipeline = OptimizationPipeline::new(OptLevel::O0);
        let stats = pipeline.run(&mut func);
        assert_eq!(stats.changes, 0);

        // add #0 should NOT have been peepholed at O0
        let inst = func.inst(trust_cg_ir::InstId(0));
        assert_eq!(inst.opcode, AArch64Opcode::AddRI);
    }

    #[test]
    fn test_o0_run_with_provenance_noop_preserves_map() {
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![ret]);
        let mut provenance = ProvenanceMap::new();
        provenance.record_lowering(TrustIrInstId(11), &[InstId(0)], PassId::new("isel"));

        let pipeline = OptimizationPipeline::new(OptLevel::O0);
        let stats = pipeline.run_with_provenance(&mut func, &mut provenance);

        assert_eq!(stats.changes, 0);
        assert_eq!(stats.total_pass_runs(), 0);
        let entry = provenance.get_entry(InstId(0)).unwrap();
        assert_eq!(entry.trust_ir_origins, vec![TrustIrInstId(11)]);
        assert_eq!(entry.transforms.len(), 1);
    }

    #[test]
    fn test_o1_peephole() {
        let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(1), imm(0)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![add, ret]);

        let pipeline = OptimizationPipeline::new(OptLevel::O1);
        pipeline.run(&mut func);

        let block = func.block(func.entry);
        // DCE removes the add (v0 unused), only ret remains.
        assert_eq!(block.insts.len(), 1);
    }

    #[test]
    fn test_o2_full_pipeline() {
        let m0 = MachInst::new(AArch64Opcode::MovI, vec![vreg(0), imm(10)]);
        let a1 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(1), vreg(0), imm(0)]);
        let a2 = MachInst::new(AArch64Opcode::AddRI, vec![vreg(2), vreg(1), imm(5)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![m0, a1, a2, ret]);

        let pipeline = OptimizationPipeline::new(OptLevel::O2);
        let stats = pipeline.run(&mut func);
        assert!(stats.changes > 0);
    }

    #[test]
    fn test_o2_pipeline_emits_proof_optimization_certificate_with_metadata() {
        let mut func = make_no_overflow_pipeline_func();
        let source_hash = 0xfeed_cafe_dead_beef_1234_5678_90ab_cdefu128;
        let metadata = ProofOptimizationMetadata::new()
            .with_inst_proof_facts(
                InstId(0),
                vec![
                    ProofFact::NoUndef,
                    ProofFact::Aligned(64),
                    ProofFact::DivergenceClass(ProofDivergence::Low),
                ],
            )
            .with_source_region_hash(InstId(0), source_hash);

        let pipeline =
            OptimizationPipeline::new(OptLevel::O2).with_proof_optimization_metadata(metadata);
        let stats = pipeline.run(&mut func);

        assert_eq!(stats.proof_optimization_certificates.len(), 1);
        let cert = &stats.proof_optimization_certificates[0];
        assert_eq!(cert.source_region_hash, source_hash);
        assert_ne!(cert.certificate_id, 0);
        assert_ne!(cert.proof_hash, 0);
        assert_ne!(cert.validation_hash, 0);
        assert!(
            cert.consumed_facts
                .iter()
                .any(|fact| fact.payload().as_deref() == Some("64"))
        );
        assert!(
            cert.consumed_facts
                .iter()
                .any(|fact| fact.payload().as_deref() == Some("Low"))
        );
    }

    #[test]
    fn test_o2_pipeline_uses_aligned_facts_for_aarch64_store_pair() {
        let str0 = MachInst::new(AArch64Opcode::StrRI, vec![preg(X0), preg(X2), imm(0)]);
        let str1 = MachInst::new(AArch64Opcode::StrRI, vec![preg(X1), preg(X2), imm(8)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![str0, str1, ret]);

        let metadata = ProofOptimizationMetadata::new()
            .with_inst_proof_facts(InstId(0), vec![ProofFact::Aligned(16)])
            .with_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)]);

        let pipeline =
            OptimizationPipeline::new(OptLevel::O2).with_proof_optimization_metadata(metadata);
        let stats = pipeline.run(&mut func);

        assert!(stats.changes > 0);
        let block = func.block(func.entry);
        assert_eq!(block.insts.len(), 2);
        let pair = func.inst(block.insts[0]);
        assert_eq!(pair.opcode, AArch64Opcode::StpRI);
        assert_eq!(pair.operands, vec![preg(X0), preg(X1), preg(X2), imm(0)]);
    }

    #[test]
    fn test_o2_pipeline_early_addrmode_reaches_proof_store_pair() {
        with_disable_passes_env(
            Some(
                "inline,cfold,copyprop,cse,gvn,sroa,vec,licm,strred,unroll,\
                 declrewrite,peep,addrmode,cmpsel,ifconv,cmpbr,looplatch,\
                 tailcall,dce,cfgsimp,closed_form_reduction,neonreduce,neon_array,\
                 neon_minmax,neon_predsum,neon_map,neon_condstore,neon_find,neon_stencil,\
                 neon_fmap,neonfpred,neonfarray,redsplit,scalar_unroll,extaddr,aliashoist,selfuse,sched",
            ),
            || {
                let mut func = make_early_addrmode_store_pair_candidate();
                let metadata = ProofOptimizationMetadata::new()
                    .with_inst_proof_facts(InstId(1), vec![ProofFact::Aligned(16)])
                    .with_inst_proof_facts(InstId(3), vec![ProofFact::Aligned(16)]);

                let pipeline = OptimizationPipeline::new(OptLevel::O2)
                    .with_proof_optimization_metadata(metadata);
                let stats = pipeline.run(&mut func);

                assert_eq!(
                    stats.runs,
                    vec![
                        // sincos-merge runs first (registered right after inline,
                        // which is disabled here); inert on this store-pair
                        // candidate (no sin/cos calls; also non-Darwin default),
                        // but still executes once.
                        ("sincos-merge".to_string(), 1),
                        // loop-dead-pure-sink runs right after sincos-merge;
                        // inert on this store-pair candidate (no libm-pure
                        // call), but still executes once.
                        ("loop-dead-pure-sink".to_string(), 1),
                        ("addr-mode-early".to_string(), 1),
                        ("proof-opts".to_string(), 1),
                        // unfuse-serial-fma runs (registered after StrengthReduction,
                        // not in this test's disable list); inert on this non-loop
                        // store-pair candidate but still executes once.
                        ("unfuse-serial-fma".to_string(), 1),
                        // loop-unswitch runs right before loop-unroll (disabled
                        // here); inert on this non-loop store-pair candidate but
                        // still executes once.
                        ("loop-unswitch".to_string(), 1),
                        // eor-rotate-fuse runs (registered after RotateIdiom, not
                        // in this test's disable list); it is inert on this
                        // store-pair candidate but still executes once.
                        ("eor-rotate-fuse".to_string(), 1),
                        ("and-cmp-fuse".to_string(), 1),
                        ("xorshift-demanded-bits".to_string(), 1),
                        // latch-and-split runs right after cmp-branch-fusion
                        // (disabled here); INERT without a profile (this test
                        // attaches none) but still executes once.
                        ("latch-and-split".to_string(), 1),
                        // tiny-loop-diamond runs right after cfg-simplify (disabled
                        // here); inert on this non-loop store-pair candidate but
                        // executes once.
                        ("tiny-loop-diamond".to_string(), 1),
                        // aarch64-bounds-check-elim executes once (inert on this
                        // non-loop store-pair candidate — no carrier), default-ON.
                        ("aarch64-bounds-check-elim".to_string(), 1),
                        // recurrence-store-forward executes once (inert on this
                        // non-loop store-pair candidate — no recurrence loop),
                        // default-ON.
                        ("recurrence-store-forward".to_string(), 1),
                        // const-trip-guard-normalize runs before the unrollers/
                        // vectorizers (inert on this non-loop candidate — no
                        // constant-trip CmpRI guard), default-ON.
                        ("const-trip-guard-normalize".to_string(), 1),
                        // strided-store-unroll executes once (inert on this
                        // non-loop store-pair candidate — no marking loop),
                        // default-ON.
                        ("strided-store-unroll".to_string(), 1),
                        // mac-reg-block executes once (inert on this non-loop
                        // store-pair candidate — no matmul nest), default-ON.
                        ("mac-reg-block".to_string(), 1),
                        // mac-row-unroll executes once (inert on this non-loop
                        // store-pair candidate — no MAC loop), default-ON.
                        ("mac-row-unroll".to_string(), 1),
                        // swap-range-guard executes once (inert on this non-loop
                        // store-pair candidate — no swap chain), default-ON.
                        ("swap-range-guard".to_string(), 1),
                        ("deadloop".to_string(), 1),
                        // neon-bytesum executes once (inert on this non-loop
                        // store-pair candidate — no change), now default-ON.
                        ("neon-bytesum".to_string(), 1),
                        ("neon-bitrev".to_string(), 1),
                        // neon-fill executes once (inert on this non-loop
                        // store-pair candidate — no fill loop), default-ON.
                        ("neon-fill".to_string(), 1),
                        // neon-iota-fill executes once (inert on this non-loop
                        // store-pair candidate — no iota-fill loop), default-ON.
                        ("neon-iota-fill".to_string(), 1),
                        // neon-butterfly executes once (inert on this non-loop
                        // store-pair candidate — no stride-2 complex-butterfly
                        // loop), default-ON.
                        ("neon-butterfly".to_string(), 1),
                        // resid-collapse runs right after scalar-unroll
                        // (disabled here); inert on this non-loop store-pair
                        // candidate (no counted single-trip tail), default-ON.
                        ("resid-collapse".to_string(), 1),
                        // the LATE unfuse-serial-fma instance (post-vectorizer,
                        // catches ordered-drain FMADD runs); inert here.
                        ("unfuse-serial-fma".to_string(), 1),
                        // ptr-iv-sr runs after ext-addr (disabled in this
                        // test); inert on this non-loop store-pair candidate
                        // but executes once.
                        // post-index is registered immediately before ptr-iv-sr;
                        // inert on this store-pair candidate.
                        ("post-index".to_string(), 1),
                        ("ptr-iv-sr".to_string(), 1),
                        // call-unroll runs immediately after ptr-iv-sr; inert
                        // on this non-loop store-pair candidate (no counted
                        // loop, no call) but executes once.
                        ("call-unroll".to_string(), 1),
                        // mul-shift-reduce runs DEAD LAST (right before the
                        // disabled scheduler); inert on this multiply-free
                        // store-pair candidate but executes once.
                        ("mul-shift-reduce".to_string(), 1),
                        // shift-alu-fuse runs right after mul-shift-reduce; inert
                        // on this store-pair candidate (no LslRI+ADD/SUB) but
                        // executes once.
                        ("shift-alu-fuse".to_string(), 1),
                        // lsr-and-ubfx runs immediately after shift-alu-fuse;
                        // inert on this store-pair candidate but executes once.
                        ("lsr-and-ubfx".to_string(), 1),
                        // csinc-fold runs right after shift-alu-fuse; inert on
                        // this store-pair candidate (no CSEL) but executes once.
                        ("csinc-fold".to_string(), 1),
                        // partial-unroll runs just before the scheduler; inert
                        // here (no loops in this candidate) but executes once.
                        ("partial-unroll".to_string(), 1),
                        // mem-pair-formation runs DEAD LAST; the early addr-mode
                        // pass already paired this candidate, so it is inert here
                        // but executes once.
                        ("mem-pair-formation".to_string(), 1),
                    ]
                );
                assert_eq!(stats.changes, 2);

                let block = func.block(func.entry);
                assert_eq!(block.insts.len(), 2);
                let pair_id = block.insts[0];
                let pair = func.inst(pair_id);
                assert_eq!(pair.opcode, AArch64Opcode::StpRI);
                assert_eq!(pair.operands, vec![vreg(0), vreg(1), vreg(2), imm(0)]);
                assert_eq!(func.inst(block.insts[1]).opcode, AArch64Opcode::Ret);
                assert_eq!(stats.proof_optimization_certificates.len(), 1);
                let cert = &stats.proof_optimization_certificates[0];
                assert_eq!(cert.kind, OptCertificateKind::PairCombined);
                assert_eq!(cert.route.admission, "proof-facts");
                assert!(
                    cert.consumed_facts
                        .iter()
                        .any(|fact| fact.payload().as_deref() == Some("16"))
                );
                assert_ne!(cert.proof_hash, 0);
                assert_ne!(cert.validation_hash, 0);
            },
        );
    }

    #[test]
    fn test_o2_pipeline_with_provenance_derives_source_trust_ir_hash() {
        fn run_with_trust_ir_origin(origin: TrustIrInstId) -> u128 {
            let mut func = make_no_overflow_pipeline_func();
            let mut provenance = ProvenanceMap::new();
            provenance.record_lowering(origin, &[InstId(0)], PassId::new("isel"));

            let pipeline = OptimizationPipeline::new(OptLevel::O2);
            let stats = pipeline.run_with_provenance(&mut func, &mut provenance);

            assert_eq!(stats.proof_optimization_certificates.len(), 1);
            stats.proof_optimization_certificates[0].source_region_hash
        }

        let first = run_with_trust_ir_origin(TrustIrInstId(41));
        let second = run_with_trust_ir_origin(TrustIrInstId(42));

        assert_ne!(first, 0);
        assert_ne!(second, 0);
        assert_ne!(first, second);
    }

    #[test]
    fn test_o2_pipeline_records_disabled_candidate_rejection_certificate() {
        let mut func = make_no_overflow_pipeline_func();
        let metadata = ProofOptimizationMetadata::new().with_disabled_candidate(
            InstId(0),
            "NoOverflow",
            "proof opts disabled by product config",
        );
        let pipeline =
            OptimizationPipeline::new(OptLevel::O2).with_proof_optimization_metadata(metadata);
        let stats = pipeline.run(&mut func);

        let cert = stats
            .proof_optimization_certificates
            .iter()
            .find(|cert| {
                cert.rejection.as_ref().is_some_and(|rejection| {
                    rejection.code == ProofDiagnosticCode::DisabledCandidate
                })
            })
            .expect("O2 pipeline should preserve disabled-candidate certificate");
        let rejection = cert.rejection.as_ref().unwrap();
        assert_eq!(rejection.fact, "NoOverflow");
        assert_eq!(rejection.detail, "proof opts disabled by product config");
    }

    #[test]
    fn test_o2_pipeline_records_failed_product_gate_rejection_certificate() {
        let mut func = make_no_overflow_pipeline_func();
        let metadata = ProofOptimizationMetadata::new().with_failed_product_gate(
            InstId(0),
            "NoOverflow",
            "release gate requires replayable certificate chain",
        );
        let pipeline =
            OptimizationPipeline::new(OptLevel::O2).with_proof_optimization_metadata(metadata);
        let stats = pipeline.run(&mut func);

        let cert = stats
            .proof_optimization_certificates
            .iter()
            .find(|cert| {
                cert.rejection.as_ref().is_some_and(|rejection| {
                    rejection.code == ProofDiagnosticCode::FailedProductGate
                })
            })
            .expect("O2 pipeline should preserve failed-product-gate certificate");
        let rejection = cert.rejection.as_ref().unwrap();
        assert_eq!(rejection.fact, "NoOverflow");
        assert_eq!(
            rejection.detail,
            "release gate requires replayable certificate chain"
        );
    }

    /// Regression test for issue #432 — CSE Movz/Movn miscompile.
    ///
    /// Before the fix, CSE keyed on `OpcodeCategory::MovRI` + operands,
    /// which collapsed `Movz Xd, #2` (materializes +2) into the same key as
    /// `Movn Xd, #2` (materializes ~2 = -3). The second instruction was
    /// eliminated and its uses rewritten to the first — silently producing
    /// `+2 + +2 = +4` instead of `+2 + -3 = -1`.
    ///
    /// This is a pipeline-context regression: it runs only the CSE pass
    /// (the one that contained the bug) on a MachFunction that exercises
    /// the O2 code path. Running the full `OptimizationPipeline` would
    /// have constant folding absorb the Movz/Movn into concrete integers
    /// before CSE ran, masking the underlying bug. The CSE pass itself is
    /// what ends up in the O1+/O2 pipeline; proving it correct in isolation
    /// is equivalent.
    ///
    /// See `cse::tests::test_cse_movz_movn_same_imm_not_merged` for the
    /// authoritative CSE-pass regression test (empirically verified to
    /// FAIL on pre-fix code and PASS after the fix).
    #[test]
    fn test_cse_pass_preserves_movz_movn_distinct() {
        use crate::cse::CommonSubexprElim;
        use crate::pass_manager::MachinePass;

        // v2 = Movz #2          (materializes +2)
        // v3 = Movn #2          (materializes ~2 = -3)
        // v4 = AddRR v2, v3     (should compute -1 at runtime)
        // ret
        let mz = MachInst::new(AArch64Opcode::Movz, vec![vreg(2), imm(2)]);
        let mn = MachInst::new(AArch64Opcode::Movn, vec![vreg(3), imm(2)]);
        let add = MachInst::new(AArch64Opcode::AddRR, vec![vreg(4), vreg(2), vreg(3)]);
        let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
        let mut func = make_func_with_insts(vec![mz, mn, add, ret]);

        // Run only the CSE pass (the one that contained the bug).
        let mut cse = CommonSubexprElim;
        let _changed = cse.run(&mut func);

        // Both Movz and Movn must survive.
        let block = func.block(func.entry);
        let mut saw_movz = false;
        let mut saw_movn = false;
        let mut add_srcs: Option<(MachOperand, MachOperand)> = None;
        for &inst_id in &block.insts {
            let inst = func.inst(inst_id);
            match inst.opcode {
                AArch64Opcode::Movz => saw_movz = true,
                AArch64Opcode::Movn => saw_movn = true,
                AArch64Opcode::AddRR => {
                    assert_eq!(inst.operands.len(), 3, "AddRR should have 3 operands");
                    add_srcs = Some((inst.operands[1].clone(), inst.operands[2].clone()));
                }
                _ => {}
            }
        }
        assert!(saw_movz, "CSE eliminated Movz (regression #432)");
        assert!(saw_movn, "CSE eliminated Movn (regression #432)");

        // The AddRR's two sources must be distinct vregs (one per Movz/Movn).
        // If CSE collapses them, both sources point at the same vreg — the
        // exact shape of the miscompile.
        let (src1, src2) = add_srcs.expect("AddRR must remain in the function");
        if let (MachOperand::VReg(a), MachOperand::VReg(b)) = (&src1, &src2) {
            assert_ne!(
                a.id, b.id,
                "AddRR sources collapsed to same vreg — CSE merged Movz+Movn (regression #432)"
            );
        } else {
            panic!(
                "AddRR sources should still be VRegs after CSE: got {:?}, {:?}",
                src1, src2
            );
        }
    }

    #[test]
    fn test_o3_iterates() {
        // Force declarative rewrite off so the count is independent of
        // Wave 3's default flip (#393). With default-on, O3 is 71 passes.
        with_declarative_rewrite_env(None, Some("1"), || {
            let pipeline = OptimizationPipeline::new(OptLevel::O3);
            let pm = pipeline.build_pass_manager();
            // 70 passes: inline + early addr-mode + proof-opts + const-fold +
            // copy-prop + cse + gvn + sroa + vectorize + licm +
            // strength-reduce + loop-unswitch + loop-unroll + peephole + addr-mode +
            // cmp-select + if-convert + cmp-branch-fusion + tail-call + dce +
            // cfg-simplify + aarch64-bounds-check-elim +
            // recurrence-store-forward + strided-store-unroll +
            // closed-form-reduction + loop-latch-layout +
            // neon-reduce + neon-array + neon-minmax + neon-predsum + neon-map + neon-fill +
            // neon-stencil + neon-fmap + neon-butterfly + neon-fpred +
            // neon-farray (widening-only default) + reduction-split +
            // scalar-unroll + ext-addr + ptr-iv-sr + select-fuse + eor-rotate-fuse +
            // mul-shift-reduce + shift-alu-fuse + lsr-and-ubfx + and-cmp-fuse +
            // xorshift-demanded-bits + csinc-fold + pressure-aware-scheduler +
            // resid-collapse + sincos-merge + loop-dead-pure-sink + the late
            // (post-unroll) sroa instance + latch-and-split (profile-gated,
            // inert without a profile) + call-unroll + partial-unroll.
            assert_eq!(pm.num_passes(), 73);
        });
    }

    #[test]
    fn profile_use_is_scheduled_only_for_o2_o3_with_profile() {
        let profile = crate::pgo::ProfData::new(0x396);

        let o1 = OptimizationPipeline::new(OptLevel::O1).with_profile_use(profile.clone());
        assert!(
            !o1.build_pass_manager()
                .pass_names()
                .contains(&"profile-use")
        );

        let o2 = OptimizationPipeline::new(OptLevel::O2).with_profile_use(profile.clone());
        assert_eq!(
            o2.build_pass_manager().pass_names().first(),
            Some(&"profile-use")
        );

        let o3 = OptimizationPipeline::new(OptLevel::O3).with_profile_use(profile);
        assert_eq!(
            o3.build_pass_manager().pass_names().first(),
            Some(&"profile-use")
        );
    }

    #[test]
    fn profile_use_runs_as_o2_noop_pass() {
        let profile = crate::pgo::ProfData::new(0x396);
        let pipeline = OptimizationPipeline::new(OptLevel::O2).with_profile_use(profile);
        let mut func = MachFunction::new(
            "profile_use_pipeline_smoke".to_string(),
            Signature::new(vec![], vec![]),
        );

        let stats = pipeline.run(&mut func);

        assert!(
            stats
                .runs
                .iter()
                .any(|(name, count)| name == "profile-use" && *count == 1),
            "profile-use pass should be callable from the O2 pipeline: {:?}",
            stats.runs
        );
    }

    #[test]
    fn profile_use_hotness_reaches_o2_vectorizer() {
        let disabled = concat!(
            "inline,addrmodeearly,proof,cfold,copyprop,cse,gvn,sroa,",
            "licm,strred,unroll,declrewrite,peep,addrmode,cmpsel,",
            "ifconv,cmpbr,looplatch,tailcall,dce,cfgsimp,sched,consttripnorm"
        );
        with_disable_passes_env(Some(disabled), || {
            let (mut hot_func, hot_adds) = make_profitable_small_vectorization_loop();
            let hot_profile = small_vectorization_profile(100, 100);
            let hot_pipeline =
                OptimizationPipeline::new(OptLevel::O2).with_profile_use(hot_profile);

            let hot_stats = hot_pipeline.run(&mut hot_func);

            assert!(
                hot_stats.changes > 0,
                "hot profile should let O2 vectorize the trip-count-4 loop"
            );
            assert!(
                hot_adds.iter().any(|&inst_id| {
                    hot_func.inst(inst_id).operands.iter().any(|operand| {
                        matches!(operand, MachOperand::VReg(vreg) if vreg.class == RegClass::Fpr128)
                    })
                }),
                "hot-profile vectorization should upgrade scalar operands"
            );

            let (mut cold_func, cold_adds) = make_profitable_small_vectorization_loop();
            let cold_profile = small_vectorization_profile(5, 100);
            let cold_pipeline =
                OptimizationPipeline::new(OptLevel::O2).with_profile_use(cold_profile);

            let cold_stats = cold_pipeline.run(&mut cold_func);

            assert_eq!(
                cold_stats.changes, 0,
                "cold profile should keep the default vectorization gate"
            );
            assert!(
                cold_adds.iter().all(|&inst_id| {
                    cold_func.inst(inst_id).operands.iter().all(|operand| {
                        !matches!(operand, MachOperand::VReg(vreg) if vreg.class == RegClass::Fpr128)
                    })
                }),
                "cold profile should not vectorize the small loop"
            );
        });
    }

    #[test]
    fn profile_use_hotness_reaches_o2_loop_unroll() {
        let disabled = concat!(
            "inline,addrmodeearly,proof,cfold,copyprop,cse,gvn,sroa,",
            "vec,licm,strred,declrewrite,peep,addrmode,cmpsel,",
            "ifconv,cmpbr,looplatch,tailcall,dce,cfgsimp,sched"
        );
        with_disable_passes_env(Some(disabled), || {
            let mut hot_func = make_pipeline_counting_loop(5);
            let hot_pipeline = OptimizationPipeline::new(OptLevel::O2)
                .with_profile_use(loop_unroll_profile(100, 100));

            let hot_stats = hot_pipeline.run(&mut hot_func);

            assert!(
                hot_stats
                    .runs
                    .iter()
                    .any(|(name, count)| name == "profile-use" && *count == 1),
                "profile-use should run before loop-unroll: {:?}",
                hot_stats.runs
            );
            assert!(
                hot_stats
                    .runs
                    .iter()
                    .any(|(name, count)| name == "loop-unroll" && *count == 1),
                "loop-unroll should be present in the focused O2 pipeline: {:?}",
                hot_stats.runs
            );
            assert!(
                !hot_func.block(BlockId(3)).succs.contains(&BlockId(1)),
                "hot profile should let O2 fully unroll a trip-count-5 loop"
            );

            let mut cold_func = make_pipeline_counting_loop(5);
            let cold_pipeline = OptimizationPipeline::new(OptLevel::O2)
                .with_profile_use(loop_unroll_profile(5, 100));

            cold_pipeline.run(&mut cold_func);

            assert!(
                cold_func.block(BlockId(3)).succs.contains(&BlockId(1)),
                "cold profile should keep the default loop-unroll gate"
            );

            let mut missing_func = make_pipeline_counting_loop(5);
            let missing_pipeline =
                OptimizationPipeline::new(OptLevel::O2).with_profile_use(ProfData::new(0x829));

            missing_pipeline.run(&mut missing_func);

            assert!(
                missing_func.block(BlockId(3)).succs.contains(&BlockId(1)),
                "missing profile should keep the default loop-unroll gate"
            );
        });
    }

    #[test]
    fn addrmodeearly_is_immediately_before_proof_at_o2_os_o3_only() {
        with_declarative_rewrite_env(None, Some("1"), || {
            for level in [OptLevel::O2, OptLevel::Os, OptLevel::O3] {
                let pm = OptimizationPipeline::new(level).build_pass_manager();
                let pass_names = pm.pass_names();
                let early_pos = pass_names
                    .iter()
                    .position(|name| *name == "addr-mode-early")
                    .expect("O2/Os/O3 must include addr-mode-early");
                let proof_pos = pass_names
                    .iter()
                    .position(|name| *name == "proof-opts")
                    .expect("O2/Os/O3 must include proof-opts");
                assert_eq!(
                    proof_pos,
                    early_pos + 1,
                    "addr-mode-early must be immediately before proof-opts at {level:?}"
                );
            }

            for level in [OptLevel::O0, OptLevel::O1] {
                let pm = OptimizationPipeline::new(level).build_pass_manager();
                let pass_names = pm.pass_names();
                assert!(
                    !pass_names.contains(&"addr-mode-early"),
                    "addr-mode-early is O2/Os/O3 only"
                );
            }
        });
    }

    #[test]
    fn disable_list_addrmodeearly_only_skips_early_addrmode() {
        with_disable_passes_env(Some("addrmodeearly"), || {
            let pm = OptimizationPipeline::new(OptLevel::O2).build_pass_manager();
            let pass_names = pm.pass_names();
            assert!(!pass_names.contains(&"addr-mode-early"));
            assert!(pass_names.contains(&"addr-mode"));
        });
    }

    #[test]
    fn disable_list_addrmode_still_skips_late_addrmode_only() {
        with_disable_passes_env(Some("addrmode"), || {
            let pm = OptimizationPipeline::new(OptLevel::O2).build_pass_manager();
            let pass_names = pm.pass_names();
            assert!(pass_names.contains(&"addr-mode-early"));
            assert!(!pass_names.contains(&"addr-mode"));
        });
    }

    #[test]
    fn lsr_and_ubfx_is_scheduled_after_shift_fusion_and_kill_switchable() {
        for level in [OptLevel::O1, OptLevel::O2, OptLevel::Os, OptLevel::O3] {
            let manager = OptimizationPipeline::new(level).build_pass_manager();
            let names = manager.pass_names();
            let shift = names
                .iter()
                .position(|name| *name == "shift-alu-fuse")
                .expect("optimized pipeline must include shift-alu-fuse");
            let ubfx = names
                .iter()
                .position(|name| *name == "lsr-and-ubfx")
                .expect("optimized pipeline must include lsr-and-ubfx");
            assert_eq!(ubfx, shift + 1, "UBFX fusion ordering drifted at {level:?}");
        }
        assert!(
            !OptimizationPipeline::new(OptLevel::O0)
                .build_pass_manager()
                .pass_names()
                .contains(&"lsr-and-ubfx")
        );
        with_disable_passes_env(Some("lsrandubfx"), || {
            for level in [OptLevel::O1, OptLevel::O2, OptLevel::Os, OptLevel::O3] {
                assert!(
                    !OptimizationPipeline::new(level)
                        .build_pass_manager()
                        .pass_names()
                        .contains(&"lsr-and-ubfx"),
                    "lsrandubfx bisect key ignored at {level:?}"
                );
            }
        });
    }

    #[test]
    fn neon_fill_scheduled_at_o2_o3_only_and_kill_switchable() {
        // Default-ON at O2/Os/O3 (immediately after neon-map), NEVER at O0/O1.
        for level in [OptLevel::O2, OptLevel::Os, OptLevel::O3] {
            let pm = OptimizationPipeline::new(level).build_pass_manager();
            let pass_names = pm.pass_names();
            assert!(
                pass_names.contains(&"neon-fill"),
                "neon-fill present at {level:?}"
            );
            let map_pos = pass_names.iter().position(|n| *n == "neon-map");
            let fill_pos = pass_names.iter().position(|n| *n == "neon-fill");
            assert!(
                map_pos.is_some() && fill_pos.is_some() && fill_pos > map_pos,
                "neon-fill runs after neon-map at {level:?}"
            );
        }
        for level in [OptLevel::O0, OptLevel::O1] {
            let pm = OptimizationPipeline::new(level).build_pass_manager();
            assert!(
                !pm.pass_names().contains(&"neon-fill"),
                "neon-fill NOT scheduled at {level:?}"
            );
        }
        // Kill switch removes it.
        with_disable_passes_env(Some("neon_fill"), || {
            let pm = OptimizationPipeline::new(OptLevel::O2).build_pass_manager();
            assert!(
                !pm.pass_names().contains(&"neon-fill"),
                "kill switch removes neon-fill"
            );
        });
    }

    #[test]
    fn strided_store_unroll_scheduled_at_o2_o3_only_and_kill_switchable() {
        // Default-ON at O2/Os/O3 (after aarch64-bounds-check-elim, before
        // closed-form-reduction and loop-latch-layout), NEVER at O0/O1.
        for level in [OptLevel::O2, OptLevel::Os, OptLevel::O3] {
            let pm = OptimizationPipeline::new(level).build_pass_manager();
            let pass_names = pm.pass_names();
            assert!(
                pass_names.contains(&"strided-store-unroll"),
                "strided-store-unroll present at {level:?}"
            );
            let bce_pos = pass_names
                .iter()
                .position(|n| *n == "aarch64-bounds-check-elim");
            let ssu_pos = pass_names.iter().position(|n| *n == "strided-store-unroll");
            let cfr_pos = pass_names
                .iter()
                .position(|n| *n == "closed-form-reduction");
            let latch_pos = pass_names.iter().position(|n| *n == "loop-latch-layout");
            assert!(
                bce_pos.is_some() && ssu_pos.is_some() && ssu_pos > bce_pos,
                "strided-store-unroll runs after aarch64-bounds-check-elim at {level:?}"
            );
            assert!(
                cfr_pos.is_some() && ssu_pos < cfr_pos,
                "strided-store-unroll runs before closed-form-reduction at {level:?}"
            );
            assert!(
                latch_pos.is_some() && ssu_pos < latch_pos,
                "strided-store-unroll runs before loop-latch-layout at {level:?}"
            );
        }
        for level in [OptLevel::O0, OptLevel::O1] {
            let pm = OptimizationPipeline::new(level).build_pass_manager();
            assert!(
                !pm.pass_names().contains(&"strided-store-unroll"),
                "strided-store-unroll NOT scheduled at {level:?}"
            );
        }
        // Per-pass bisect kill switch removes it.
        with_disable_passes_env(Some("strided_store_unroll"), || {
            let pm = OptimizationPipeline::new(OptLevel::O2).build_pass_manager();
            assert!(
                !pm.pass_names().contains(&"strided-store-unroll"),
                "kill switch removes strided-store-unroll"
            );
        });
    }

    #[test]
    fn recurrence_store_forward_scheduled_at_o2_o3_only_and_kill_switchable() {
        // Default-ON at O2/Os/O3 (right after aarch64-bounds-check-elim,
        // before strided-store-unroll and the later unrollers/vectorizers),
        // NEVER at O0/O1.
        for level in [OptLevel::O2, OptLevel::Os, OptLevel::O3] {
            let pm = OptimizationPipeline::new(level).build_pass_manager();
            let pass_names = pm.pass_names();
            assert!(
                pass_names.contains(&"recurrence-store-forward"),
                "recurrence-store-forward present at {level:?}"
            );
            let bce_pos = pass_names
                .iter()
                .position(|n| *n == "aarch64-bounds-check-elim");
            let rsf_pos = pass_names
                .iter()
                .position(|n| *n == "recurrence-store-forward");
            let ssu_pos = pass_names.iter().position(|n| *n == "strided-store-unroll");
            assert!(
                bce_pos.is_some() && rsf_pos.is_some() && rsf_pos > bce_pos,
                "recurrence-store-forward runs after aarch64-bounds-check-elim at {level:?}"
            );
            assert!(
                ssu_pos.is_some() && rsf_pos < ssu_pos,
                "recurrence-store-forward runs before strided-store-unroll at {level:?}"
            );
        }
        for level in [OptLevel::O0, OptLevel::O1] {
            let pm = OptimizationPipeline::new(level).build_pass_manager();
            assert!(
                !pm.pass_names().contains(&"recurrence-store-forward"),
                "recurrence-store-forward NOT scheduled at {level:?}"
            );
        }
        // Per-pass bisect kill switch removes it.
        with_disable_passes_env(Some("recurrence_store_fwd"), || {
            let pm = OptimizationPipeline::new(OptLevel::O2).build_pass_manager();
            assert!(
                !pm.pass_names().contains(&"recurrence-store-forward"),
                "kill switch removes recurrence-store-forward"
            );
        });
    }

    #[test]
    fn mac_row_unroll_scheduled_at_o2_o3_only_and_kill_switchable() {
        // Default-ON at O2/Os/O3 (right after strided-store-unroll, i.e. after
        // aarch64-bounds-check-elim and before closed-form-reduction and
        // loop-latch-layout), NEVER at O0/O1.
        for level in [OptLevel::O2, OptLevel::Os, OptLevel::O3] {
            let pm = OptimizationPipeline::new(level).build_pass_manager();
            let pass_names = pm.pass_names();
            assert!(
                pass_names.contains(&"mac-row-unroll"),
                "mac-row-unroll present at {level:?}"
            );
            let bce_pos = pass_names
                .iter()
                .position(|n| *n == "aarch64-bounds-check-elim");
            let mru_pos = pass_names.iter().position(|n| *n == "mac-row-unroll");
            let cfr_pos = pass_names
                .iter()
                .position(|n| *n == "closed-form-reduction");
            let latch_pos = pass_names.iter().position(|n| *n == "loop-latch-layout");
            assert!(
                bce_pos.is_some() && mru_pos.is_some() && mru_pos > bce_pos,
                "mac-row-unroll runs after aarch64-bounds-check-elim at {level:?}"
            );
            assert!(
                cfr_pos.is_some() && mru_pos < cfr_pos,
                "mac-row-unroll runs before closed-form-reduction at {level:?}"
            );
            assert!(
                latch_pos.is_some() && mru_pos < latch_pos,
                "mac-row-unroll runs before loop-latch-layout at {level:?}"
            );
        }
        for level in [OptLevel::O0, OptLevel::O1] {
            let pm = OptimizationPipeline::new(level).build_pass_manager();
            assert!(
                !pm.pass_names().contains(&"mac-row-unroll"),
                "mac-row-unroll NOT scheduled at {level:?}"
            );
        }
        // Per-pass bisect kill switch removes it.
        with_disable_passes_env(Some("mac_row_unroll"), || {
            let pm = OptimizationPipeline::new(OptLevel::O2).build_pass_manager();
            assert!(
                !pm.pass_names().contains(&"mac-row-unroll"),
                "kill switch removes mac-row-unroll"
            );
        });
    }

    #[test]
    fn without_redundancy_elimination_drops_cse_and_gvn_at_o2_and_o3() {
        for level in [OptLevel::O2, OptLevel::O3] {
            // Default pipeline runs both redundancy passes.
            let default_pm = OptimizationPipeline::new(level).build_pass_manager();
            let default_names = default_pm.pass_names();
            assert!(
                default_names.contains(&"cse"),
                "{level:?} should run cse by default"
            );
            assert!(
                default_names.contains(&"gvn"),
                "{level:?} should run gvn by default"
            );

            // With the opt-in builder, exactly cse + gvn are removed; every
            // other pass at that level is preserved.
            let trimmed_pm = OptimizationPipeline::new(level)
                .without_redundancy_elimination()
                .build_pass_manager();
            let trimmed_names = trimmed_pm.pass_names();
            assert!(
                !trimmed_names.contains(&"cse"),
                "{level:?} cse should be skipped"
            );
            assert!(
                !trimmed_names.contains(&"gvn"),
                "{level:?} gvn should be skipped"
            );
            let mut expected: Vec<&str> = default_names
                .iter()
                .copied()
                .filter(|n| *n != "cse" && *n != "gvn")
                .collect();
            let mut actual: Vec<&str> = trimmed_names.clone();
            expected.sort_unstable();
            actual.sort_unstable();
            assert_eq!(actual, expected, "{level:?} only cse+gvn should change");
        }
    }

    #[test]
    fn without_redundancy_elimination_is_noop_at_o1() {
        // O1 never schedules cse/gvn, so the builder leaves the pipeline intact.
        let default_pm = OptimizationPipeline::new(OptLevel::O1).build_pass_manager();
        let default_names = default_pm.pass_names();
        let trimmed_pm = OptimizationPipeline::new(OptLevel::O1)
            .without_redundancy_elimination()
            .build_pass_manager();
        let trimmed_names = trimmed_pm.pass_names();
        assert_eq!(trimmed_names, default_names);
    }

    // =========================================================================
    // Pipeline integration tests for NEON auto-vectorization
    // =========================================================================

    /// Verify that O2 pipeline fires vectorization on a simple i32 add loop.
    ///
    /// The add instruction's operands should be upgraded from Gpr32 to Fpr128
    /// (NEON SIMD) and an arrangement immediate should be appended.
    #[test]
    fn test_o2_vectorization_fires_on_loop() {
        let (mut func, add_id) = make_vectorizable_loop();

        // Precondition: add operands are Gpr32 before pipeline.
        let add_inst = func.inst(add_id);
        assert_eq!(add_inst.opcode, AArch64Opcode::AddRR);
        assert_eq!(add_inst.operands.len(), 3, "pre-pipeline: 3 operands");
        if let MachOperand::VReg(vreg) = &add_inst.operands[0] {
            assert_eq!(vreg.class, RegClass::Gpr32, "pre-pipeline: Gpr32");
        }

        let pipeline = OptimizationPipeline::new(OptLevel::O2);
        let stats = pipeline.run(&mut func);
        assert!(stats.changes > 0, "O2 pipeline should report changes");

        // Postcondition: the add instruction should have SIMD register class.
        // After vectorization, operands are Fpr128 and an arrangement
        // immediate is appended (4 operands: dst, src1, src2, arrangement).
        let add_inst = func.inst(add_id);
        let has_fpr128 = add_inst.operands.iter().any(|op| {
            if let MachOperand::VReg(vreg) = op {
                vreg.class == RegClass::Fpr128
            } else {
                false
            }
        });
        assert!(
            has_fpr128,
            "O2 pipeline should vectorize the add: operands should include Fpr128 registers"
        );

        // Arrangement immediate should be present (encoder code 5 for i32 4S).
        let has_arrangement = add_inst
            .operands
            .iter()
            .any(|op| matches!(op, MachOperand::Imm(5)));
        assert!(
            has_arrangement,
            "O2 pipeline should append arrangement encoding (Imm(5) for 4S)"
        );
    }

    /// Verify that O3 pipeline fires vectorization on a simple i32 add loop.
    #[test]
    fn test_o3_vectorization_fires_on_loop() {
        let (mut func, add_id) = make_vectorizable_loop();

        let pipeline = OptimizationPipeline::new(OptLevel::O3);
        let stats = pipeline.run(&mut func);
        assert!(stats.changes > 0, "O3 pipeline should report changes");

        // Same postcondition: Fpr128 after vectorization.
        let add_inst = func.inst(add_id);
        let has_fpr128 = add_inst.operands.iter().any(|op| {
            if let MachOperand::VReg(vreg) = op {
                vreg.class == RegClass::Fpr128
            } else {
                false
            }
        });
        assert!(
            has_fpr128,
            "O3 pipeline should vectorize the add: operands should include Fpr128 registers"
        );
    }

    /// Verify that O2 pipeline vectorizes multiple arithmetic ops in a loop.
    #[test]
    fn test_o2_vectorization_multi_op() {
        let (mut func, op_ids) = make_multi_op_vectorizable_loop();

        // Precondition: all ops have Gpr32 operands.
        for &id in &op_ids {
            let inst = func.inst(id);
            if let MachOperand::VReg(vreg) = &inst.operands[0] {
                assert_eq!(vreg.class, RegClass::Gpr32, "pre-pipeline: Gpr32");
            }
        }

        let pipeline = OptimizationPipeline::new(OptLevel::O2);
        let stats = pipeline.run(&mut func);
        assert!(stats.changes > 0, "O2 pipeline should report changes");

        // Postcondition: all three ops should be vectorized to Fpr128.
        for &id in &op_ids {
            let inst = func.inst(id);
            let has_fpr128 = inst.operands.iter().any(|op| {
                if let MachOperand::VReg(vreg) = op {
                    vreg.class == RegClass::Fpr128
                } else {
                    false
                }
            });
            assert!(
                has_fpr128,
                "O2 pipeline should vectorize {:?} (inst {:?}): expected Fpr128",
                inst.opcode, id,
            );
        }
    }

    /// Verify that O1 does NOT fire vectorization (not in O1 pipeline).
    #[test]
    fn test_o1_no_vectorization() {
        let (mut func, add_id) = make_vectorizable_loop();

        let pipeline = OptimizationPipeline::new(OptLevel::O1);
        pipeline.run(&mut func);

        // O1 has only scalar/proof rewrites plus scheduling -- no vectorization.
        // The add instruction should NOT have Fpr128 operands.
        let add_inst = func.inst(add_id);
        let has_fpr128 = add_inst.operands.iter().any(|op| {
            if let MachOperand::VReg(vreg) = op {
                vreg.class == RegClass::Fpr128
            } else {
                false
            }
        });
        assert!(
            !has_fpr128,
            "O1 pipeline should NOT vectorize (vectorization is O2+)"
        );
    }

    /// Verify that O2 pass count includes vectorization pass.
    ///
    /// Forces declarative rewrite off so this test measures the scalar
    /// pipeline shape independent of Wave 3's default flip (#393).
    #[test]
    fn test_o2_includes_vectorize_pass() {
        with_declarative_rewrite_env(None, Some("1"), || {
            let pipeline = OptimizationPipeline::new(OptLevel::O2);
            // O2 (decl-rewrite off) = 70 passes: inline + early addr-mode +
            // proof-opts + const-fold + copy-prop + cse + gvn + sroa +
            // vectorize + licm + strength-reduce + loop-unswitch +
            // loop-unroll + peephole +
            // addr-mode + cmp-select + if-convert + cmp-branch-fusion +
            // tail-call + dce + cfg-simplify + tiny-loop-diamond +
            // aarch64-bounds-check-elim +
            // strided-store-unroll + closed-form-reduction +
            // loop-latch-layout + neon-reduce + neon-array + neon-minmax +
            // neon-predsum + neon-map + neon-fill + neon-stencil +
            // neon-fmap + neon-butterfly + neon-fpred + neon-farray (widening-only default) +
            // reduction-split + scalar-unroll + ext-addr + ptr-iv-sr +
            // select-fuse + eor-rotate-fuse + mul-shift-reduce + shift-alu-fuse
            // + lsr-and-ubfx
            // + csinc-fold + pressure-aware-scheduler + alias-hoist + mac-row-unroll
            // + and-cmp-fuse + xorshift-demanded-bits + resid-collapse +
            // sincos-merge + loop-dead-pure-sink + the late (post-unroll) sroa
            // instance + latch-and-split (profile-gated, inert without a
            // profile) + call-unroll + partial-unroll.
            assert_eq!(pipeline.pass_count(), 73);
        });
    }

    // =========================================================================
    // Declarative rewrite flag tests (#393)
    // =========================================================================
    //
    // The pass is ON by default; the only opt-out is the general per-pass bisect
    // `TRUST_CG_DISABLE_PASSES=declrewrite`. Tests use a thread-local override
    // instead of mutating process-wide env, which keeps parallel `cargo test
    // --lib` runs deterministic while the production path reads the real
    // environment.

    /// Map the legacy `(enable, disable)` declarative-rewrite test semantics onto
    /// the one remaining mechanism: `TRUST_CG_DISABLE_PASSES=declrewrite`. The
    /// dedicated kill-switch env vars were removed; the pass is on by default. An
    /// explicit opt-in (`enable == Some("1")`) still wins over the kill switch.
    fn with_declarative_rewrite_env<R>(
        enable: Option<&str>,
        disable: Option<&str>,
        f: impl FnOnce() -> R,
    ) -> R {
        if disable == Some("1") && enable != Some("1") {
            with_disable_passes_env(Some("declrewrite"), f)
        } else {
            f()
        }
    }

    fn with_disable_passes_env<R>(disabled: Option<&str>, f: impl FnOnce() -> R) -> R {
        // Merge with any outer disable-passes override so nested calls accumulate
        // (disabling X then Y disables both). This preserves the behavior tests
        // relied on when declarative-rewrite had its own separate kill switch:
        // `with_declarative_rewrite_env(None, Some("1"), || with_disable_passes_env(Some("sroa"), ..))`
        // now turns OFF both `declrewrite` and `sroa`.
        let outer = test_env_override("TRUST_CG_DISABLE_PASSES").flatten();
        let merged: Option<String> = match (outer, disabled) {
            (Some(a), Some(b)) => Some(if a.is_empty() {
                b.to_owned()
            } else {
                format!("{a},{b}")
            }),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b.to_owned()),
            (None, None) => None,
        };
        let _disabled = set_test_env_override(TestEnvOverrideKey::DisablePasses, merged.as_deref());
        f()
    }

    #[test]
    fn explicit_disabled_passes_override_isolated_from_ambient_control() {
        with_disable_passes_env(Some("vec"), || {
            let inherited = OptimizationPipeline::new(OptLevel::O2).build_pass_manager();
            assert!(!inherited.pass_names().contains(&"vectorize"));

            let explicitly_enabled = OptimizationPipeline::new(OptLevel::O2)
                .with_disabled_passes("")
                .build_pass_manager();
            assert!(explicitly_enabled.pass_names().contains(&"vectorize"));

            let explicitly_disabled = OptimizationPipeline::new(OptLevel::O2)
                .with_disabled_passes("vec")
                .build_pass_manager();
            assert!(!explicitly_disabled.pass_names().contains(&"vectorize"));
        });
    }

    #[test]
    fn declarative_rewrite_defaults_on_o1() {
        // Wave 3 flipped default-on. Neither env var set → pass is in
        // the pipeline: DCE, proof-opts, declarative-rewrite, SROA,
        // RotateIdiom, EorRotateFuse, ShiftAluFuse, LsrAndUbfx, Scheduler = 9.
        // AndCmpFuse remains in the O2+ lane.
        with_declarative_rewrite_env(None, None, || {
            let pipeline = OptimizationPipeline::new(OptLevel::O1);
            assert_eq!(pipeline.pass_count(), 9);
        });
    }

    #[test]
    fn admitted_rewrite_pipeline_hook_is_disabled_by_default() {
        let base = make_declarative_rewrite_pass_with_report(
            &[],
            RewriteAdmissionLoaderConfig::disabled(),
        )
        .0;
        let base_rules = base.num_rules();
        let records = vec!["not-json".to_string()];
        let with_records = make_declarative_rewrite_pass_with_report(
            &records,
            RewriteAdmissionLoaderConfig::disabled(),
        )
        .0;

        assert_eq!(with_records.num_rules(), base_rules);
    }

    #[test]
    fn admitted_rewrite_pipeline_report_is_disabled_by_default() {
        with_declarative_rewrite_env(None, None, || {
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let mut func = make_func_with_insts(vec![ret]);
            let result = OptimizationPipeline::new(OptLevel::O1)
                .with_admitted_rewrite_records([admitted_rewrite_json()])
                .run_with_report(&mut func);

            assert!(
                result
                    .pipeline_report
                    .rewrite_admission_load_error
                    .is_none()
            );
            let report = result
                .pipeline_report
                .rewrite_admission_load_report
                .expect("O1 declarative rewrite hook should report admission load status");
            assert!(!report.loader_enabled);
            assert_eq!(report.input_records, 1);
            assert_eq!(report.parsed_records, 0);
            assert_eq!(report.eligible_records, 0);
            assert_eq!(report.registered_rules, 0);
            assert!(report.loaded_records.is_empty());
            assert!(
                result
                    .pass_stats
                    .runs
                    .iter()
                    .any(|(name, count)| name == "declarative-rewrite" && *count == 1)
            );
        });
    }

    #[test]
    fn admitted_rewrite_pipeline_report_exposes_enabled_preview_counts() {
        with_declarative_rewrite_env(None, None, || {
            let admitted = admitted_rewrite_json();
            let mut profile_only: serde_json::Value =
                serde_json::from_str(&admitted).expect("test admission JSON");
            profile_only["admission_state"] =
                serde_json::Value::String("proved_profile_only".to_string());
            let profile_only = profile_only.to_string();

            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let mut func = make_func_with_insts(vec![ret]);
            let result = OptimizationPipeline::new(OptLevel::O1)
                .with_admitted_rewrite_records([admitted, profile_only])
                .with_rewrite_admission_config(RewriteAdmissionLoaderConfig::enabled_for_preview())
                .run_with_report(&mut func);

            assert!(
                result
                    .pipeline_report
                    .rewrite_admission_load_error
                    .is_none()
            );
            let report = result
                .pipeline_report
                .rewrite_admission_load_report
                .expect("enabled preview should expose admission load counts");
            assert!(report.loader_enabled);
            assert_eq!(report.input_records, 2);
            assert_eq!(report.parsed_records, 2);
            assert_eq!(report.eligible_records, 1);
            assert_eq!(report.registered_rules, 1);
            assert_eq!(report.loaded_records.len(), 1);
            assert_eq!(
                report.loaded_records[0].transform_name,
                "ay_lra_sparse_add_zero"
            );
            assert!(
                result
                    .pass_stats
                    .runs
                    .iter()
                    .any(|(name, count)| name == "declarative-rewrite" && *count == 1)
            );
        });
    }

    #[test]
    fn admitted_rewrite_pipeline_hook_fails_closed_on_bad_json() {
        let base = make_declarative_rewrite_pass_with_report(
            &[],
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .0;
        let base_rules = base.num_rules();
        let records = vec!["not-json".to_string()];
        let with_bad_records = make_declarative_rewrite_pass_with_report(
            &records,
            RewriteAdmissionLoaderConfig::enabled_for_preview(),
        )
        .0;

        assert_eq!(with_bad_records.num_rules(), base_rules);
    }

    #[test]
    fn declarative_rewrite_kill_switch_o1() {
        // `TRUST_CG_DISABLE_PASSES=declrewrite` removes the declarative
        // pass: DCE, proof-opts, SROA, RotateIdiom, EorRotateFuse,
        // ShiftAluFuse, LsrAndUbfx, Scheduler = 8. AndCmpFuse remains in the
        // O2+ lane.
        with_declarative_rewrite_env(None, Some("1"), || {
            let pipeline = OptimizationPipeline::new(OptLevel::O1);
            assert_eq!(pipeline.pass_count(), 8);
        });
    }

    #[test]
    fn declarative_rewrite_defaults_on_o2() {
        // Wave 3 default: the 70-pass base pipeline (incl. SROA, early addr-mode,
        // aarch64-bounds-check-elim, strided-store-unroll,
        // closed-form-reduction, neon-reduce, neon-array, neon-minmax,
        // neon-predsum, neon-map, neon-fill, neon-stencil, neon-fmap,
        // neon-butterfly, neon-fpred,
        // neon-farray (widening-only default), reduction-split, scalar-unroll,
        // ext-addr, ptr-iv-sr, select-fuse, eor-rotate-fuse, mul-shift-reduce,
        // shift-alu-fuse, lsr-and-ubfx, and-cmp-fuse, xorshift-demanded-bits,
        // resid-collapse, sincos-merge, loop-unswitch, and profile-gated
        // latch-and-split, call-unroll, partial-unroll) plus 1
        // declarative-rewrite pass.
        with_declarative_rewrite_env(None, None, || {
            let pipeline = OptimizationPipeline::new(OptLevel::O2);
            assert_eq!(pipeline.pass_count(), 74);
        });
    }

    #[test]
    fn declarative_rewrite_kill_switch_o2() {
        // Kill switch drops back to 72 passes (base O2 incl. SROA,
        // aarch64-bounds-check-elim, strided-store-unroll,
        // closed-form-reduction, neon-reduce, neon-array, neon-minmax,
        // neon-predsum, neon-map, neon-fill, neon-stencil, neon-fmap,
        // neon-butterfly, neon-fpred,
        // neon-farray (widening-only default), reduction-split, scalar-unroll,
        // ext-addr, ptr-iv-sr, select-fuse, eor-rotate-fuse, mul-shift-reduce,
        // shift-alu-fuse, lsr-and-ubfx, and-cmp-fuse,
        // xorshift-demanded-bits, resid-collapse and mac-row-unroll, without
        // the declarative-rewrite pass; sincos-merge, loop-unswitch, and the
        // profile-gated latch-and-split are still present; call-unroll and
        // partial-unroll are present too).
        with_declarative_rewrite_env(None, Some("1"), || {
            let pipeline = OptimizationPipeline::new(OptLevel::O2);
            assert_eq!(pipeline.pass_count(), 73);
        });
    }

    #[test]
    fn declarative_rewrite_enable_var_still_honored_o1() {
        // Transitional: explicit opt-in wins over the disable variable.
        with_declarative_rewrite_env(Some("1"), Some("1"), || {
            let pipeline = OptimizationPipeline::new(OptLevel::O1);
            // Enable beats disable → pass included (8 total: DCE +
            // proof-opts + declarative-rewrite + SROA + RotateIdiom +
            // EorRotateFuse + ShiftAluFuse + LsrAndUbfx + Scheduler).
            assert_eq!(pipeline.pass_count(), 9);
        });
    }

    #[test]
    fn declarative_rewrite_respects_disable_list_o2() {
        // Per-pass bisect still works: TRUST_CG_DISABLE_PASSES=declrewrite
        // removes the pass even when default-on.
        with_declarative_rewrite_env(None, None, || {
            with_disable_passes_env(Some("declrewrite"), || {
                let pipeline = OptimizationPipeline::new(OptLevel::O2);
                // Declarative disabled via bisect list → 72 base passes
                // (incl. SROA, early addr-mode, aarch64-bounds-check-elim,
                // strided-store-unroll, closed-form-reduction,
                // neon-reduce, neon-array, neon-minmax, neon-predsum, neon-map,
                // neon-stencil, neon-fmap, neon-fpred, neon-farray
                // (widening-only default), reduction-split, scalar-unroll,
                // ext-addr, ptr-iv-sr, select-fuse, eor-rotate-fuse, mul-shift-reduce,
                // shift-alu-fuse, lsr-and-ubfx, and-cmp-fuse,
                // xorshift-demanded-bits, alias-hoist, mac-row-unroll,
                // resid-collapse, sincos-merge, the late (post-unroll) sroa
                // instance, loop-dead-pure-sink, loop-unswitch, and the
                // profile-gated latch-and-split, call-unroll,
                // partial-unroll).
                assert_eq!(pipeline.pass_count(), 73);
            });
        });
    }

    #[test]
    fn disable_list_skips_sroa_o1() {
        with_declarative_rewrite_env(None, Some("1"), || {
            with_disable_passes_env(Some("sroa"), || {
                let pipeline = OptimizationPipeline::new(OptLevel::O1);
                // declrewrite + sroa off → DCE, proof-opts, RotateIdiom,
                // EorRotateFuse, ShiftAluFuse, LsrAndUbfx,
                // Scheduler = 7.
                assert_eq!(pipeline.pass_count(), 7);
            });
        });
    }

    #[test]
    fn disable_list_skips_scheduler_o1() {
        with_declarative_rewrite_env(None, Some("1"), || {
            with_disable_passes_env(Some("sched"), || {
                let pipeline = OptimizationPipeline::new(OptLevel::O1);
                let pm = pipeline.build_pass_manager();
                let pass_names = pm.pass_names();
                // declrewrite + sched off → DCE, proof-opts, SROA,
                // RotateIdiom, EorRotateFuse, ShiftAluFuse,
                // LsrAndUbfx = 7.
                assert_eq!(pass_names.len(), 7);
                assert!(!pass_names.contains(&"instruction-scheduler"));
            });
        });
    }

    #[test]
    fn disable_list_skips_sroa_o3() {
        with_declarative_rewrite_env(None, Some("1"), || {
            with_disable_passes_env(Some("sroa"), || {
                let pipeline = OptimizationPipeline::new(OptLevel::O3);
                assert_eq!(pipeline.pass_count(), 71);
            });
        });
    }

    #[test]
    fn disable_list_skips_full_o3_passes() {
        with_declarative_rewrite_env(None, Some("1"), || {
            with_disable_passes_env(Some("licm,ifconv,sched"), || {
                let pipeline = OptimizationPipeline::new(OptLevel::O3);
                let pm = pipeline.build_pass_manager();
                let pass_names = pm.pass_names();
                assert_eq!(pass_names.len(), 70);
                assert!(!pass_names.contains(&"licm"));
                assert!(!pass_names.contains(&"if-convert"));
                assert!(!pass_names.contains(&"pressure-aware-scheduler"));
            });
        });
    }

    #[test]
    fn declarative_rewrite_fires_at_o1_by_default() {
        // Default-on: the declarative pass should rewrite
        // `add x, y, #0` → `mov x, y` (migrated pattern #1). The
        // declarative rewrite performs the normalization; DCE drops the
        // unused result. No env vars required.
        with_declarative_rewrite_env(None, None, || {
            let add = MachInst::new(AArch64Opcode::AddRI, vec![vreg(0), vreg(1), imm(0)]);
            let ret = MachInst::new(AArch64Opcode::Ret, vec![]);
            let mut func = make_func_with_insts(vec![add, ret]);

            let pipeline = OptimizationPipeline::new(OptLevel::O1);
            pipeline.run(&mut func);

            // DCE drops the unused result.
            let block = func.block(func.entry);
            assert_eq!(block.insts.len(), 1);
        });
    }
}
