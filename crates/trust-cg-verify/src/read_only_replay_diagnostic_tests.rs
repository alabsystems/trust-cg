// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Actual raw proof inspection of the first mandatory original-Core/LIR query.
//! The test-only captured-authority helper retains query/proof/checker results
//! before temporary cleanup. Inspection is NOT replay credit or an all-part
//! certificate; the mandatory codegen acceptance assertion is unchanged.

use super::*;
use crate::function_request::FunctionDischargeContext;
use crate::source_bound_frame::bind_read_only_source;
use crate::{FunctionVerifier, VerificationConfig};
use sha2::{Digest, Sha256};
use trust_cg_codegen::CoreHostJitTarget;

#[test]
fn actual_original_ty_first_core_lir_return_raw_proof_is_inspected_before_cleanup() {
    crate::env_lock::with_env_overrides(
        &[
            ("TCG_REFINE_SOLVER", "1"),
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            // Same committed projection, host context and ordinary adapter as
            // compiler_read_only_replay_tests.rs. No different source, body,
            // target layout, source annotation or lowering is substituted.
            let capture: serde_json::Value = serde_json::from_str(include_str!(
                "../tests/fixtures/ty_original_read_only_predicate.json"
            ))
            .unwrap();
            assert_eq!(
                capture["format"],
                "ty-original-read-only-predicate-source-v1"
            );
            assert_eq!(capture["selection"]["unit_key"], "inv:Second");
            assert_eq!(capture["original_core_instruction_count"], 59);
            let original: trust_ir::Module =
                serde_json::from_value(capture["module"].clone()).unwrap();
            assert!(original.target_info.is_none());
            assert_eq!(original.functions.len(), 1);
            let host = CoreHostJitTarget::detect().expect("actual supported host target");
            let mut module = original.clone();
            module.target_info = Some(host.trust_ir_target_info().clone());
            let mut restored = module.clone();
            restored.target_info = None;
            assert_eq!(
                serde_json::to_value(restored).unwrap(),
                serde_json::to_value(&original).unwrap(),
                "only ordinary explicit host target context changes"
            );
            let function = &module.functions[0];
            assert_eq!(function.id.index(), 60_004);
            assert_eq!(function.name, "tyw1_u3");
            assert_eq!(function.blocks.len(), 12);
            let (lir, proof_context) = trust_cg_lower::translate_function_with_license(
                function,
                &module,
                &crate::license_test_support::permit_unlicensed(),
            )
            .unwrap();
            let source = bind_read_only_source(&module, 0, &lir)
                .expect("the exact authentic original Core/LIR query must bind");
            assert_eq!(source.read_requirements().len(), 3);
            assert_eq!(source.load_obligations().len(), 3);

            // The production inventory's FIRST part borrows this exact
            // original source obligation before considering either target.
            // Construct this private test-only view without inventing MachIR
            // or bytes to stand in for the actual compiler endpoints.
            let first = ReadOnlyReplayPart {
                id: ReadOnlyRelationId {
                    stage: ReadOnlyRelationStage::CoreToLir,
                    kind: ReadOnlyRelationKind::Return,
                    index: 0,
                },
                obligation: source.return_obligation(),
            };
            assert!(std::ptr::eq(first.obligation(), source.return_obligation()));
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            assert!(!request.recording_active(), "diagnostic is not a recorder");
            assert!(
                request.reuse_identity().is_none(),
                "same mandatory fresh nonreusable request policy"
            );
            let scope = FunctionDischargeContext::new(&request);
            let diagnostic = request.with_policy(|| {
                let config = crate::verdict_db::live_source_bound_config();
                let diagnostic = request
                    .ay()
                    .inspect_fresh_source_bound(&first, &config)
                    .expect("captured exact original return proof inspection must run, not skip");
                assert_eq!(
                    diagnostic.smt2,
                    crate::ay_bridge::generate_smt2_query_raw(first.obligation(), &config),
                    "no query simplification or proof-model substitution"
                );
                assert_eq!(diagnostic.timeout_ms, config.timeout_ms);
                diagnostic
            });
            let query_sha256 = format!("{:x}", Sha256::digest(diagnostic.smt2.as_bytes()));
            // Equality is a diagnostic fact about the current transcription,
            // never a substitute for the mandatory independent raw replay.
            let original_return_expressions_structurally_equal =
                first.obligation().trust_ir_expr == first.obligation().aarch64_expr;
            println!(
                "TY_READ_ONLY_FIRST_RAW_PROOF query_sha256={query_sha256} query_bytes={} proof_bytes={:?} original_return_expressions_structurally_equal={original_return_expressions_structurally_equal} source_geometry_premises={} solver_sha256={} candidate={} checker_accepted={:?} all_part_certificate=false instruction_credit=false native_credit=false",
                diagnostic.smt2.len(),
                diagnostic.proof.as_ref().map(String::len),
                first.obligation().preconditions.len(),
                diagnostic.solver_sha256,
                diagnostic.candidate_debug,
                diagnostic.checker_accepted,
            );
            // Emit before verdict/artifact assertions so actual missing,
            // incomplete, rejected or unexpected evidence remains in the log.
            println!("TY_READ_ONLY_FIRST_RAW_PROOF_ARTIFACT_BEGIN");
            println!(
                "{}",
                serde_json::to_string(&serde_json::json!({
                    "format": "ty-read-only-first-original-return-raw-proof-v1",
                    "scope": "FIRST original Core-to-LIR return query only; no allocated-machine/final-word/all-part certificate",
                    "fixture": "crates/trust-cg-verify/tests/fixtures/ty_original_read_only_predicate.json",
                    "selection": capture["selection"],
                    "original_function_ordinal": 0,
                    "original_function_id": function.id.index(),
                    "original_function_name": function.name,
                    "target_binding": "ordinary CoreHostJitTarget metadata-only binding, identical to mandatory codegen gate",
                    "targeted_original_module": &module,
                    "actual_lir_debug": format!("{lir:#?}"),
                    "actual_adapter_proof_context_debug": format!("{proof_context:#?}"),
                    "part": format!("{:?}", first.id()),
                    "original_return_expressions_structurally_equal": original_return_expressions_structurally_equal,
                    "source_geometry_premises": first.obligation().preconditions.len(),
                    "query_sha256": query_sha256,
                    "diagnostic": &diagnostic,
                    "authority_credit": false,
                }))
                .unwrap()
            );
            println!("TY_READ_ONLY_FIRST_RAW_PROOF_ARTIFACT_END");

            // Inspect the production-selected print view before asserting the
            // raw artifact gate. A raw refusal must not erase the later compact
            // producer's real stderr/proof evidence. The checker still receives
            // the exact ORIGINAL raw script, never the producer spelling.
            let producer = request.with_policy(|| {
                let config = crate::verdict_db::live_source_bound_config();
                request
                    .ay()
                    .inspect_fresh_source_bound_producer(&first, &config)
                    .expect("production-selected original return inspection must run, not skip")
            });
            assert_eq!(producer.smt2, diagnostic.smt2);
            assert_eq!(producer.timeout_ms, diagnostic.timeout_ms);
            assert_eq!(producer.solver_sha256, diagnostic.solver_sha256);
            assert_eq!(producer.checker_sha256, diagnostic.checker_sha256);
            println!(
                "TY_READ_ONLY_FIRST_PRODUCER_PROOF query_sha256={query_sha256} original_bytes={} producer_bytes={} producer_compact={} candidate={} checker_accepted={:?} all_part_certificate=false instruction_credit=false native_credit=false",
                producer.smt2.len(),
                producer.producer_smt2.len(),
                producer.producer_compact,
                producer.candidate_debug,
                producer.checker_accepted,
            );
            println!("TY_READ_ONLY_FIRST_PRODUCER_PROOF_ARTIFACT_BEGIN");
            println!("{}", serde_json::to_string(&serde_json::json!({
                "format": "ty-read-only-first-original-return-producer-proof-v1",
                "scope": "FIRST original Core-to-LIR return query only; producer spelling supplies no replay receipt",
                "selection": capture["selection"],
                "query_sha256": query_sha256,
                "diagnostic": &producer,
                "authority_credit": false,
            })).unwrap());
            println!("TY_READ_ONLY_FIRST_PRODUCER_PROOF_ARTIFACT_END");

            assert_eq!(
                diagnostic.solver_sha256,
                request
                    .ay_solver()
                    .expect("captured admitted solver")
                    .sha256()
            );
            assert!(
                diagnostic.proof_error.is_none(),
                "actual proof read failure: {:?}",
                diagnostic.proof_error
            );
            assert!(
                diagnostic
                    .proof
                    .as_ref()
                    .is_some_and(|proof| !proof.is_empty()),
                "actual readable Alethe artifact required, not a solver-status substitute"
            );
            assert!(
                diagnostic.checker_error.is_none(),
                "actual checker failure: {:?}",
                diagnostic.checker_error
            );
            assert!(
                diagnostic.checker_accepted.is_some(),
                "exact proof must be independently inspected"
            );
            assert!(scope.replays_bound(), "diagnostic minted no replay receipt");
            if diagnostic.candidate_debug != "SolverUnsat" {
                assert!(
                    diagnostic.candidate_debug.starts_with("Unknown("),
                    "expected a proof candidate/refusal, not a different solver verdict"
                );
                assert_eq!(
                    diagnostic.checker_accepted,
                    Some(false),
                    "an incomplete/unknown raw proof must not be independently accepted"
                );
            }
        },
    );
}
