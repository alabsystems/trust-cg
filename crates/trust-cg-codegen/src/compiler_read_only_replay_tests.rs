// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Mandatory original-source all-part replay at the real compiler endpoints.
//! Finite comparisons, a partial replay and AY self-checking are not proof.

use crate::CoreHostJitTarget;
use crate::pipeline::{OptLevel, Pipeline, PipelineConfig, encode_function_with_fixups_and_sites};
use trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode;
use trust_cg_verify::read_only_replay::{ReadOnlyCompilerRelations, ReadOnlyRelationStage};
use trust_cg_verify::source_bound_frame::bind_read_only_source;
use trust_cg_verify::verify::VerificationResult;
use trust_cg_verify::{FunctionVerifier, VerificationConfig};

#[test]
fn actual_original_ty_read_only_endpoints_require_all_part_independent_replay() {
    trust_cg_process_env::with_env_overrides(
        &[
            ("TCG_REFINE_SOLVER", "1"),
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            let capture: serde_json::Value = serde_json::from_str(include_str!(
                "../../trust-cg-verify/tests/fixtures/ty_original_read_only_predicate.json"
            ))
            .unwrap();
            let original: trust_ir::Module =
                serde_json::from_value(capture["module"].clone()).unwrap();
            assert!(original.target_info.is_none());
            let host = CoreHostJitTarget::detect().expect("actual supported Mac host");
            let mut module = original.clone();
            module.target_info = Some(host.trust_ir_target_info().clone());
            let mut restored = module.clone();
            restored.target_info = None;
            assert_eq!(
                serde_json::to_value(restored).unwrap(),
                serde_json::to_value(original).unwrap(),
                "only the ordinary explicit JIT target context changes"
            );
            let function = &module.functions[0];
            assert_eq!(function.id.index(), 60_004);
            let (lir, proof_context) = trust_cg_lower::translate_function_with_license(
                function,
                &module,
                &crate::license_test_support::permit_unlicensed(),
            )
            .unwrap();
            let source = bind_read_only_source(&module, 0, &lir).unwrap();
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            let mut failures = Vec::new();
            for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let pipeline = Pipeline::new(PipelineConfig {
                    opt_level: level,
                    verify: false,
                    ..PipelineConfig::for_target(host.target_spec().triple())
                });
                let (machine, _) = pipeline
                    .prepare_function_with_metrics_and_trust_ir_module(
                        &lir,
                        Some(&proof_context),
                        &module,
                        function,
                    )
                    .unwrap();
                let (code, fixups, _) = encode_function_with_fixups_and_sites(&machine).unwrap();
                assert!(fixups.is_empty(), "actual complete post-encoding endpoint");
                let relations = ReadOnlyCompilerRelations::bind(&source, &machine, &code)
                    .expect("all real endpoints must bind, not skip");
                assert_eq!(relations.len(), 28);
                for (stage, expected) in [
                    (ReadOnlyRelationStage::CoreToLir, 4),
                    (ReadOnlyRelationStage::CoreToMachine, 12),
                    (ReadOnlyRelationStage::CoreToFinalBytes, 12),
                ] {
                    assert_eq!(
                        relations.parts().filter(|p| p.id().stage == stage).count(),
                        expected
                    );
                }
                let report = relations.replay(&request);
                assert!(std::ptr::eq(report.relations(), &relations));
                assert!(std::ptr::eq(report.request(), &request));
                assert_eq!(report.outcomes().len(), relations.len());
                for (outcome, part) in report.outcomes().iter().zip(relations.parts()) {
                    assert_eq!(outcome.id(), part.id());
                    println!(
                        "TY_READ_ONLY_REQUIRED_REPLAY level={level:?} part={:?} attempted={} verdict={:?} why={:?} instruction_credit=false native_credit=false",
                        outcome.id(),
                        outcome.attempted(),
                        outcome.verdict(),
                        outcome.why()
                    );
                }
                if let Some(certificate) = report.certificate() {
                    assert!(std::ptr::eq(certificate.relations(), &relations));
                    assert!(std::ptr::eq(certificate.request(), &request));
                    assert!(report.outcomes().iter().all(|outcome| {
                        outcome.attempted()
                            && matches!(outcome.verdict(), Some(VerificationResult::Valid))
                    }));
                } else {
                    let first = report.outcomes().iter().find(|outcome| {
                        !matches!(outcome.verdict(), Some(VerificationResult::Valid))
                    });
                    failures.push(format!(
                        "{level:?}: refusal={:?}, first={first:?}",
                        report.refusal()
                    ));
                }
            }
            assert!(
                failures.is_empty(),
                "mandatory all-part original TY replay failed: {}; no skipped positive row, partial credit or finite/native substitute",
                failures.join("; ")
            );
        },
    );
}
