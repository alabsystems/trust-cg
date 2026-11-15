// trust-cg-opt/tests/pipeline_small_stack.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Ordinary pipeline consumers keep their requested stack budget. These are
//! construction/order/runtime regression controls, not optimization proofs or
//! measured speed/memory claims.

use std::thread;

use trust_cg_ir::{
    AArch64Opcode, InstId, MachFunction, MachInst, PassId, ProvenanceMap, Signature, TrustIrInstId,
};
use trust_cg_opt::pipeline::OptimizationPipelineReport;
use trust_cg_opt::rewrite::RewriteAdmissionLoaderConfig;
use trust_cg_opt::{
    OptLevel, OptimizationPipeline, PassValidationConfig, PassValidationPolicy,
    PassValidationScope, ProfData,
};

const SMALL_STACK_BYTES: usize = 256 * 1024;

// Independent, complete registration-order controls, transcribed from the
// pre-split builder. In particular, the repeated SROA, neon-find and unfuse-FMA
// instances are intentional, not deduplicated by the construction repair.
const BASIC_PASS_NAMES: &[&str] = &[
    "i8-return-demanded-bits",
    "dce",
    "proof-opts",
    "declarative-rewrite",
    "sroa",
    "rotate-idiom",
    "eor-rotate-fuse",
    "shift-alu-fuse",
    "lsr-and-ubfx",
    "cfg-simplify",
    "instruction-scheduler",
];

const OPTIMIZED_PASS_NAMES: &[&str] = &[
    "i8-return-demanded-bits",
    "inline",
    "sincos-merge",
    "loop-dead-pure-sink",
    "addr-mode-early",
    "proof-opts",
    "const-fold",
    "copy-prop",
    "cse",
    "gvn",
    "sroa",
    "vectorize",
    "licm",
    "strength-reduce",
    "unfuse-serial-fma",
    "loop-unswitch",
    "loop-unroll",
    "sroa",
    "declarative-rewrite",
    "rotate-idiom",
    "eor-rotate-fuse",
    "addr-mode",
    "cmp-select",
    "if-convert",
    "and-cmp-fuse",
    "xorshift-demanded-bits",
    "cmp-branch-fusion",
    "latch-and-split",
    "tail-call",
    "dce",
    "cfg-simplify",
    "late-boolean-diamond",
    "tiny-loop-diamond",
    "aarch64-bounds-check-elim",
    "recurrence-store-forward",
    "const-trip-guard-normalize",
    "strided-store-unroll",
    "mac-reg-block",
    "mac-row-unroll",
    "swap-range-guard",
    "closed-form-reduction",
    "deadloop",
    "loop-latch-layout",
    "neon-reduce",
    "neon-array",
    "neon-bytesum",
    "neon-minmax",
    "neon-predsum",
    "neon-map",
    "neon-bitrev",
    "neon-fill",
    "neon-iota-fill",
    "neon-find",
    "neon-stencil",
    "neon-fmap",
    "neon-butterfly",
    "neon-find",
    "neon-fpred",
    "neon-farray",
    "reduction-split",
    "scalar-unroll",
    "resid-collapse",
    "unfuse-serial-fma",
    "ext-addr",
    "post-index",
    "ptr-iv-sr",
    "call-unroll",
    "alias-hoist",
    "select-fuse",
    "mul-shift-reduce",
    "shift-alu-fuse",
    "lsr-and-ubfx",
    "csinc-fold",
    "partial-unroll",
    "xorshift-pair-fusion",
    "const-chain-dedup",
    "pressure-aware-scheduler",
    "mem-pair-formation",
];

#[derive(Clone, Copy, Debug)]
enum Configuration {
    Default,
    ProfileAndTargetFeatures,
    TrimmedJit,
    DisabledAdmission,
    InvalidPreviewAdmission,
}

fn pipeline(level: OptLevel, configuration: Configuration) -> OptimizationPipeline {
    // Explicit overrides isolate these order controls from ambient bisect
    // settings, without changing the production environment handling.
    let pipeline = OptimizationPipeline::new(level).with_disabled_passes("");
    match configuration {
        Configuration::Default => pipeline,
        Configuration::ProfileAndTargetFeatures => pipeline
            .with_profile_use(ProfData::new(0x396))
            .with_target_is_darwin(true)
            .with_aarch64_dotprod(true)
            .with_contains4_scanner_batch_rewrite(true)
            .with_certified_pass_execution(),
        Configuration::TrimmedJit => pipeline
            .without_redundancy_elimination()
            .without_tail_calls()
            .with_disabled_passes(
                " sroa, neon_find, unfusefma, profileuse, cfold, dce, sched, proof ",
            ),
        Configuration::DisabledAdmission => pipeline
            .with_admitted_rewrite_records(["not-json"])
            .with_rewrite_admission_config(RewriteAdmissionLoaderConfig::disabled()),
        Configuration::InvalidPreviewAdmission => pipeline
            .with_admitted_rewrite_records(["not-json"])
            .with_rewrite_admission_config(RewriteAdmissionLoaderConfig::enabled_for_preview()),
    }
}

fn expected_names(level: OptLevel, configuration: Configuration) -> Vec<&'static str> {
    let mut names = match level {
        OptLevel::O0 => vec![],
        OptLevel::O1 => BASIC_PASS_NAMES.to_vec(),
        OptLevel::O2 | OptLevel::Os | OptLevel::O3 => OPTIMIZED_PASS_NAMES.to_vec(),
    };
    match configuration {
        Configuration::ProfileAndTargetFeatures
            if matches!(level, OptLevel::O2 | OptLevel::Os | OptLevel::O3) =>
        {
            names.insert(1, "profile-use");
        }
        Configuration::TrimmedJit => names.retain(|name| {
            !matches!(
                *name,
                "sroa"
                    | "neon-find"
                    | "unfuse-serial-fma"
                    | "profile-use"
                    | "const-fold"
                    | "dce"
                    | "instruction-scheduler"
                    | "pressure-aware-scheduler"
                    | "proof-opts"
                    | "cse"
                    | "gvn"
                    | "tail-call"
            )
        }),
        _ => {}
    }
    names
}

fn assert_report(
    level: OptLevel,
    configuration: Configuration,
    report: &OptimizationPipelineReport,
) {
    if level == OptLevel::O0 {
        assert_eq!(*report, OptimizationPipelineReport::default());
        return;
    }
    if matches!(configuration, Configuration::InvalidPreviewAdmission) {
        assert!(report.rewrite_admission_load_error.is_some());
        assert!(report.rewrite_admission_load_report.is_none());
        return;
    }
    assert!(report.rewrite_admission_load_error.is_none());
    let admission = report
        .rewrite_admission_load_report
        .as_ref()
        .expect("every optimized ladder retains declarative rewrite");
    assert!(!admission.loader_enabled);
    assert_eq!(
        admission.input_records,
        usize::from(matches!(configuration, Configuration::DisabledAdmission)),
    );
    assert_eq!(admission.parsed_records, 0);
    assert_eq!(admission.eligible_records, 0);
    assert_eq!(admission.registered_rules, 0);
    assert!(admission.loaded_records.is_empty());
}

#[test]
fn all_levels_preserve_order_and_reports_on_256kib_stack() {
    // Build and drop inside the bounded thread, never transferring a
    // PassManager (whose passes need not be Send) to another thread. No parent
    // construction warms the shared migrated engine before the first O1 build.
    thread::Builder::new()
        .name("pipeline-registration-256kib".into())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            for configuration in [
                Configuration::Default,
                Configuration::ProfileAndTargetFeatures,
                Configuration::TrimmedJit,
                Configuration::DisabledAdmission,
                Configuration::InvalidPreviewAdmission,
            ] {
                // O1 goes first so the default shared-engine initialization is
                // exercised on this bounded stack in this integration process.
                for level in [
                    OptLevel::O1,
                    OptLevel::O0,
                    OptLevel::O2,
                    OptLevel::Os,
                    OptLevel::O3,
                ] {
                    let expected = expected_names(level, configuration);
                    let pipeline = pipeline(level, configuration);
                    for _ in 0..2 {
                        let (manager, report) = pipeline.build_pass_manager_with_report();
                        assert_eq!(
                            manager.pass_names(),
                            expected,
                            "{level:?} {configuration:?}",
                        );
                        assert_eq!(manager.num_passes(), expected.len());
                        assert_report(level, configuration, &report);
                        drop(manager);
                    }
                }
            }
        })
        .expect("spawn bounded pipeline consumer")
        .join()
        .expect("bounded pipeline construction must complete");
}

fn return_function() -> MachFunction {
    let mut func = MachFunction::new("small_stack_return".into(), Signature::new(vec![], vec![]));
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(func.entry, ret);
    func
}

#[test]
fn o0_provenance_execution_preserves_function_on_256kib_stack() {
    thread::Builder::new()
        .name("pipeline-provenance-256kib".into())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let mut func = return_function();
            let before = format!("{func:?}");
            let mut provenance = ProvenanceMap::new();
            provenance.record_lowering(TrustIrInstId(11), &[InstId(0)], PassId::new("isel"));
            let pipeline = OptimizationPipeline::new(OptLevel::O0).with_disabled_passes("");
            let stats = pipeline.run_with_provenance(&mut func, &mut provenance);
            assert_eq!(format!("{func:?}"), before);
            assert_eq!(stats.changes, 0);
            assert_eq!(stats.total_pass_runs(), 0);
            assert!(stats.id_admission.is_ok());
            let entry = provenance.get_entry(InstId(0)).expect("original origin");
            assert_eq!(entry.trust_ir_origins, vec![TrustIrInstId(11)]);
            assert_eq!(entry.transforms.len(), 1);
        })
        .expect("spawn bounded provenance consumer")
        .join()
        .expect("bounded ordinary O0 execution must complete");
}

#[test]
fn selected_validation_config_reaches_manager_on_256kib_stack() {
    thread::Builder::new()
        .name("pipeline-validation-256kib".into())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            for config in [
                PassValidationConfig::diagnostic(),
                PassValidationConfig::enforce(),
                PassValidationConfig {
                    policy: PassValidationPolicy::RequireCoverage,
                    scope: PassValidationScope::AllPasses,
                },
            ] {
                // An empty O0 manager exposes its actual final validation
                // setting through the public stats contract, without adding
                // a policy getter or changing optimized admission.
                let pipeline = OptimizationPipeline::new(OptLevel::O0)
                    .with_disabled_passes("")
                    .with_pass_validation(config);
                let mut manager = pipeline.build_pass_manager();
                let mut func = return_function();
                let stats = manager.run_once_with_stats(&mut func);
                assert!(stats.id_admission.is_ok());
                assert_eq!(stats.pass_validation.config, config);
                assert_eq!(stats.total_pass_runs(), 0);
            }
        })
        .expect("spawn bounded validation consumer")
        .join()
        .expect("bounded configured manager must complete");
}
