// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Independent qualification of an untrusted producer against the original
//! whole-module Core/LIR parts. These diagnostics mint no all-part certificate,
//! caller, instruction, native or cache authority. The mandatory full gate stays.

use super::*;
use crate::ay_bridge::{AYConfig, AYResult, AyVerdict, AyVerdictSource};
use crate::legacy_module_capture::assert_legacy_module_image as assert_capture;
use crate::source_bound_frame::{ScalarMemorySourceQueries, bind_scalar_memory_source};
use crate::{FunctionVerifier, VerificationConfig};
use sha2::{Digest, Sha256};
use trust_cg_codegen::CoreHostJitTarget;
use trust_ir::{CallingConv, Linkage, Module, Ty};

/// Retain the entire authentic source capture; only actual host metadata is
/// added, never a source projection, altered body, ID or proof annotation.
fn targeted_original() -> Module {
    let capture: serde_json::Value = serde_json::from_str(include_str!(
        "../tests/fixtures/ty_original_scalar_action.json"
    ))
    .unwrap();
    assert_eq!(capture["format"], "ty-original-scalar-action-source-v1");
    assert_eq!(capture["selection"]["function_id"], 60_002);
    assert_eq!(capture["selection"]["original_function_ordinal"], 3);
    assert_eq!(capture["selection"]["unit_key"], "next:Next@91-101");
    let mut module: Module = serde_json::from_value(capture["module"].clone()).unwrap();
    assert!(module.target_info.is_none());
    assert_eq!(module.functions.len(), 10);
    assert_capture(&module, &capture["module"], "original whole-module image");
    module.target_info = Some(
        CoreHostJitTarget::detect()
            .expect("actual supported Mac host")
            .trust_ir_target_info()
            .clone(),
    );
    let mut restored = module.clone();
    restored.target_info = None;
    assert_capture(&restored, &capture["module"], "restored whole-module image");
    let function = &module.functions[3];
    assert_eq!(function.id.index(), 60_002);
    assert_eq!(function.linkage, Linkage::Internal);
    assert_eq!(function.calling_conv, CallingConv::C);
    assert_eq!(function.blocks.len(), 16);
    assert_eq!(
        function
            .blocks
            .iter()
            .map(|block| block.body.len())
            .sum::<usize>(),
        117,
    );
    module
}

#[test]
fn historical_original_scalar_action_byte_gep_query_is_reproducible() {
    let module = targeted_original();
    let (mut lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[3],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let config = crate::verdict_db::live_source_bound_config();
    {
        let current = bind_scalar_memory_source(&module, 3, &lir).unwrap();
        let raw = crate::ay_bridge::generate_smt2_query_raw(current.status_obligation(), &config);
        let spine = crate::ay_bridge::legacy_right_spine_query_for_test(
            current.status_obligation(),
            &config,
        );
        println!(
            "CURRENT_SCALAR_BYTE_GEP_QUERY canonical_bytes={} canonical_sha256={:x} right_spine_bytes={} right_spine_sha256={:x}",
            raw.len(),
            Sha256::digest(raw.as_bytes()),
            spine.len(),
            Sha256::digest(spine.as_bytes())
        );
    }
    // Test-only reconstruction of the pre-b79533c9c7 adapter spelling.
    // It supplies no production query, fallback, certificate or receipt.
    let mut replaced = 0;
    for block in lir.blocks.values_mut() {
        for instruction in &mut block.instructions {
            if matches!(
                instruction.opcode,
                trust_cg_lower::instructions::Opcode::ArrayGep {
                    elem_ty: trust_cg_lower::Type::I8
                }
            ) {
                instruction.opcode = trust_cg_lower::instructions::Opcode::Iadd;
                replaced += 1;
            }
        }
    }
    assert_eq!(
        replaced, 16,
        "exact original fixture's sixteen byte offsets"
    );
    let historical = bind_scalar_memory_source(&module, 3, &lir).unwrap();
    let raw = crate::ay_bridge::generate_smt2_query_raw(historical.status_obligation(), &config);
    assert_eq!(
        format!("{:x}", Sha256::digest(raw.as_bytes())),
        "e25d4c05aa24bd53d09f39f415267eac1294e0e36e5a8d88efc818df1cc77843"
    );
    let spine = crate::ay_bridge::legacy_right_spine_query_for_test(
        historical.status_obligation(),
        &config,
    );
    assert_eq!(
        format!("{:x}", Sha256::digest(spine.as_bytes())),
        "b543c29858e91207f5fdd28483901928b8be7b74207d1458e7986bc49b5ee9c7"
    );
}

fn original_parts<'a>(
    source: &'a ScalarMemorySourceQueries<'_>,
) -> [ScalarMemoryReplayPart<'a>; 2] {
    [
        (ScalarMemoryRelationKind::Status, source.status_obligation()),
        (
            ScalarMemoryRelationKind::FinalMemory,
            source.memory_obligation(),
        ),
    ]
    .map(|(kind, obligation)| {
        assert!(
            obligation.preconditions.iter().eq(source
                .source_geometry()
                .iter()
                .chain(source.encoding_definitions()))
        );
        ScalarMemoryReplayPart {
            id: ScalarMemoryRelationId {
                stage: ScalarMemoryRelationStage::CoreToLir,
                kind,
                index: 0,
            },
            obligation,
        }
    })
}

fn assert_constructive(source: &AyVerdictSource, checker_sha256: &str) {
    let AyVerdictSource::ClosedDefinitionProof {
        producer_verifier_source_sha256,
        checker_sha256: actual_checker,
    } = source
    else {
        panic!(
            "the genuine original must independently replay through its attributed constructive producer: {source:?}"
        )
    };
    let recorded = env!("VERIFIER_SOURCE_SHA256");
    assert_eq!(
        recorded.len(),
        64,
        "a recorded verifier SOURCE identity is required"
    );
    assert!(
        recorded
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    );
    assert_eq!(producer_verifier_source_sha256, recorded);
    assert_eq!(actual_checker, checker_sha256);
}

fn assert_positive_journal(why: Option<&str>, checker_sha256: &str) {
    let why = why.expect("Valid constructive replay must retain truthful positive provenance");
    assert!(why.contains("closed-definition-proof"), "{why}");
    assert!(why.contains("ay-ran=false"), "{why}");
    assert!(why.contains(env!("VERIFIER_SOURCE_SHA256")), "{why}");
    assert!(why.contains(checker_sha256), "{why}");
}

#[test]
fn actual_original_all_core_lir_read_and_write_demands_independently_replay() {
    crate::env_lock::with_env_overrides(
        &[
            ("TCG_REFINE_SOLVER", "1"),
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            let module = targeted_original();
            let original_module = serde_json::to_value(&module).unwrap();
            let (lir, context) = trust_cg_lower::translate_function_with_license(
                &module.functions[3],
                &module,
                &crate::license_test_support::permit_unlicensed(),
            )
            .unwrap();
            let original_lir = serde_json::to_value(&lir).unwrap();
            let original_context = format!("{context:#?}");
            let source = bind_scalar_memory_source(&module, 3, &lir).unwrap();
            assert!(std::ptr::eq(source.module(), &module));
            assert!(std::ptr::eq(source.source(), &module.functions[3]));
            assert!(std::ptr::eq(source.lir(), &lir));
            assert_eq!(source.source_reads().len(), 10);
            assert_eq!(source.lowering_reads().len(), 10);
            assert_eq!(source.source_writes().len(), 5);
            assert_eq!(source.lowering_writes().len(), 5);
            assert_eq!(source.source_geometry().len(), 31);
            assert_eq!(source.encoding_definitions().len(), 118);
            let geometry = source.source_geometry();
            let definitions = source.encoding_definitions();
            let parts: Vec<_> = [
                (ScalarMemoryRelationKind::Read, source.read_obligations()),
                (ScalarMemoryRelationKind::Write, source.write_obligations()),
            ]
            .into_iter()
            .flat_map(|(kind, obligations)| {
                obligations
                    .iter()
                    .enumerate()
                    .map(move |(index, obligation)| {
                        assert_eq!(obligation.preconditions.len(), 149);
                        assert!(
                            obligation
                                .preconditions
                                .iter()
                                .eq(geometry.iter().chain(definitions))
                        );
                        ScalarMemoryReplayPart {
                            id: ScalarMemoryRelationId {
                                stage: ScalarMemoryRelationStage::CoreToLir,
                                kind,
                                index,
                            },
                            obligation,
                        }
                    })
            })
            .collect();
            assert_eq!(parts.len(), 15);
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            assert!(!request.recording_active());
            assert!(request.reuse_identity().is_none());
            let scope = FunctionDischargeContext::new(&request);
            request.with_policy(|| {
                let config = crate::verdict_db::live_source_bound_config();
                let mut diagnostics = Vec::with_capacity(parts.len());
                let mut failures = Vec::new();
                for part in &parts {
                    let diagnostic = request.ay()
                        .inspect_source_bound_closed_definitions(part, &config)
                        .expect("retain the original access query, candidate and checker verdict");
                    let raw = crate::ay_bridge::generate_smt2_query_raw(part.obligation(), &config);
                    assert_eq!(diagnostic.smt2, raw);
                    assert_eq!(diagnostic.timeout_ms, config.timeout_ms);
                    println!(
                        "TY_ORIGINAL_CLOSED_DEFINITION_ACCESS part={:?} query_sha256={:x} query_bytes={} proof_bytes={} premises={} definitions={} steps={} compose_error={:?} checker_accepted={:?} checker_error={:?} ay_ran=false all_part_certificate=false caller_credit=false instruction_credit=false native_credit=false",
                        part.id(), Sha256::digest(raw.as_bytes()), raw.len(),
                        diagnostic.proof.as_ref().map_or(0, String::len),
                        diagnostic.premises, diagnostic.definitions, diagnostic.steps,
                        diagnostic.compose_error, diagnostic.checker_accepted, diagnostic.checker_error,
                    );
                    if diagnostic.compose_error.is_some()
                        || diagnostic.premises != 149
                        || diagnostic.definitions != 118
                        || diagnostic.checker_accepted != Some(true)
                        || diagnostic.checker_error.is_some()
                        || diagnostic.proof.is_none()
                    {
                        failures.push(format!(
                            "{:?}: compose={:?}, premises={}, definitions={}, checker={:?}, error={:?}",
                            part.id(), diagnostic.compose_error, diagnostic.premises,
                            diagnostic.definitions, diagnostic.checker_accepted, diagnostic.checker_error,
                        ));
                    }
                    diagnostics.push(diagnostic);
                }
                // Keep every original query/proof, even if an earlier positive
                // failed. The JSON retains the whole unchanged module and the
                // actual ordinary adapter endpoints once, not a reconstruction.
                println!("TY_ORIGINAL_CLOSED_DEFINITION_ARTIFACT_BEGIN");
                println!("{}", serde_json::to_string(&serde_json::json!({
                    "format": "ty-original-closed-definition-access-diagnostic-v1",
                    "fixture": "crates/trust-cg-verify/tests/fixtures/ty_original_scalar_action.json",
                    "selection": {"function_id": 60002, "original_function_ordinal": 3},
                    "original_targeted_module": &module,
                    "actual_lir": &lir,
                    "actual_adapter_proof_context_debug": &original_context,
                    "geometry": source.source_geometry().iter().map(ToString::to_string).collect::<Vec<_>>(),
                    "definitions": source.encoding_definitions().iter().map(ToString::to_string).collect::<Vec<_>>(),
                    "parts": parts.iter().zip(&diagnostics).map(|(part, diagnostic)| serde_json::json!({
                        "id": format!("{:?}", part.id()),
                        "query_sha256": format!("{:x}", Sha256::digest(diagnostic.smt2.as_bytes())),
                        "diagnostic": diagnostic,
                    })).collect::<Vec<_>>(),
                    "ay_ran": false,
                    "authority_credit": false,
                })).unwrap());
                println!("TY_ORIGINAL_CLOSED_DEFINITION_ARTIFACT_END");

                for (index, (part, diagnostic)) in parts.iter().zip(&diagnostics).enumerate() {
                    let Some(proof) = diagnostic.proof.as_deref() else {
                        // A missing positive remains in failures above; it is
                        // never recast as a passing negative or omitted row.
                        continue;
                    };
                    let macro_line = proof.lines().find(|line|
                        line.starts_with("(define-fun ") && line.contains(" () Bool "),
                    ).expect("the actual guarded demand has a Boolean proof-local macro");
                    let (header, definition) = macro_line.split_once(" () Bool ").unwrap();
                    let definition = definition.strip_suffix(')').unwrap();
                    let tampered = proof.replacen(macro_line,
                        &format!("{header} () Bool (not {definition}))"), 1);
                    assert_ne!(tampered, proof);
                    let changed_macro = request.ay().inspect_source_bound_definition_proof(
                        part, &config, &tampered,
                    ).unwrap();
                    assert_eq!(changed_macro.0, Some(false),
                        "{:?}: a changed Boolean macro is not an original premise", part.id());
                    let mut lines = proof.lines().collect::<Vec<_>>();
                    lines.pop().expect("remove only the actual final refutation");
                    let missing_refutation = request.ay().inspect_source_bound_definition_proof(
                        part, &config, &lines.join("\n"),
                    ).unwrap();
                    assert_eq!(missing_refutation.0, Some(false),
                        "{:?}: a missing refutation cannot be accepted", part.id());
                    let foreign = parts.iter().zip(&diagnostics).enumerate().find(|(other, (owner, evidence))|
                        *other != index && evidence.proof.is_some()
                            && owner.obligation().negated_equivalence() != part.obligation().negated_equivalence(),
                    ).expect("another original demand has a distinct complete assumed formula");
                    let foreign_part = request.ay().inspect_source_bound_definition_proof(
                        part, &config, foreign.1.1.proof.as_deref().unwrap(),
                    ).unwrap();
                    assert_eq!(foreign_part.0, Some(false),
                        "{:?}: another original part's assumption is not this complete query", part.id());
                    println!(
                        "TY_ORIGINAL_CLOSED_DEFINITION_ACCESS_CONTROL part={:?} changed_macro={changed_macro:?} missing_refutation={missing_refutation:?} foreign_part={:?} foreign_verdict={foreign_part:?} credit=false",
                        part.id(), foreign.1.0.id(),
                    );
                }
                assert!(scope.replays_bound(), "inspection minted no replay receipt");
                assert!(failures.is_empty(),
                    "all original 10 read and 5 write demands require independent acceptance; failed rows: {failures:?}");
            });
            assert!(!crate::verdict_db::recording_active());
            assert_eq!(serde_json::to_value(&module).unwrap(), original_module);
            assert_eq!(serde_json::to_value(&lir).unwrap(), original_lir);
            assert_eq!(format!("{context:#?}"), original_context);
        },
    );
}

#[test]
fn actual_original_fresh_production_replay_retains_constructive_attribution() {
    crate::env_lock::with_env_overrides(
        &[
            ("TCG_REFINE_SOLVER", "1"),
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            let module = targeted_original();
            let original_module = serde_json::to_value(&module).unwrap();
            let (lir, context) = trust_cg_lower::translate_function_with_license(
                &module.functions[3],
                &module,
                &crate::license_test_support::permit_unlicensed(),
            )
            .unwrap();
            let original_lir = serde_json::to_value(&lir).unwrap();
            let original_context = format!("{context:#?}");
            let source = bind_scalar_memory_source(&module, 3, &lir).unwrap();
            assert!(std::ptr::eq(source.module(), &module));
            assert!(std::ptr::eq(source.lir(), &lir));
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            assert!(!request.recording_active());
            assert!(request.reuse_identity().is_none());
            request.with_policy(|| {
                let config = crate::verdict_db::live_source_bound_config();
                for part in original_parts(&source) {
                    let original = crate::ay_bridge::generate_smt2_query_raw(part.obligation(), &config);
                    let query_sha256 = format!("{:x}", Sha256::digest(original.as_bytes()));
                    if part.id().kind == ScalarMemoryRelationKind::Status {
                        assert_eq!(query_sha256,
                            "7e6fa1b81d4a6713480708bf5ef396e9ec2e222b2cd2d8a87fe0210b5d6c0903",
                            "pin the current byte-GEP canonical original query");
                        let legacy = crate::ay_bridge::legacy_right_spine_query_for_test(
                            part.obligation(), &config,
                        );
                        assert_eq!(format!("{:x}", Sha256::digest(legacy.as_bytes())),
                            "d9d638b7586520eef2c1499df4d3c94f664e47e4ea863c9493ba10bfa081bf63");
                        assert_eq!(original.len(), legacy.len());
                        assert_ne!(original, legacy, "explicit canonical identity migration");
                    }
                    // The existing bounded inspection obtains THIS request's
                    // actual checker identity and independently accepts the
                    // original query. It supplies no synthetic Valid verdict.
                    let diagnostic = request.ay()
                        .inspect_source_bound_closed_definitions(&part, &config).unwrap();
                    assert_eq!(diagnostic.smt2, original);
                    assert_eq!(diagnostic.checker_accepted, Some(true));
                    let checker = diagnostic.checker_sha256.as_deref().unwrap();
                    let verdict = request.ay().verify_fresh_source_bound_attributed(&part, &config);
                    assert_eq!(verdict.result, AYResult::Verified,
                        "genuine original production refutation is mandatory: {verdict:?}");
                    assert_constructive(&verdict.source, checker);
                    assert_eq!(verdict.solver.as_ref().map(|solver| solver.sha256()),
                        request.ay_solver().map(|solver| solver.sha256()));
                    assert_positive_journal(Some(&verdict.provenance()), checker);
                    let (result, bound, why) =
                        crate::verdict_db::live_source_bound_replay_explained(&part, &request);
                    assert!(matches!(result, Some(VerificationResult::Valid)));
                    assert!(!bound, "a constructive proof is not an AY reuse receipt");
                    assert_positive_journal(why.as_deref(), checker);
                    assert_eq!(crate::ay_bridge::generate_smt2_query_raw(part.obligation(), &config), original);
                    println!(
                        "TY_ORIGINAL_CLOSED_DEFINITION_PRODUCTION route=fresh part={:?} query_sha256={query_sha256} result={:?} provenance={} bound={bound} why={why:?} all_part_certificate=false caller_credit=false instruction_credit=false native_credit=false",
                        part.id(), verdict.result, verdict.provenance(),
                    );
                }
            });
            assert!(!crate::verdict_db::recording_active());
            assert_eq!(serde_json::to_value(&module).unwrap(), original_module);
            assert_eq!(serde_json::to_value(&lir).unwrap(), original_lir);
            assert_eq!(format!("{context:#?}"), original_context);
        },
    );
}

#[test]
fn actual_original_cache_enabled_production_proofs_never_become_ay_reuse() {
    let store = tempfile::tempdir().unwrap();
    crate::env_lock::with_env_edits(|environment| {
        for key in [
            "TCG_NO_PROOF_CACHE",
            "TCG_NO_CERT_STORE",
            "TCG_NO_VERDICT_DB",
        ] {
            environment.remove(key);
        }
        environment.set("TCG_PROOF_CERT_STORE", store.path());
        environment.set("TCG_REFINE_SOLVER", "1");
        environment.set("TCG_BLOCKING_IDENTITY", "1");
        let module = targeted_original();
        let original_module = serde_json::to_value(&module).unwrap();
        let (lir, context) = trust_cg_lower::translate_function_with_license(
            &module.functions[3],
            &module,
            &crate::license_test_support::permit_unlicensed(),
        )
        .unwrap();
        let original_lir = serde_json::to_value(&lir).unwrap();
        let original_context = format!("{context:#?}");
        let source = bind_scalar_memory_source(&module, 3, &lir).unwrap();
        let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        assert!(!request.recording_active());
        assert!(
            request.may_reuse(),
            "the test genuinely enables ordinary reuse policy"
        );
        assert!(
            request.reuse_identity().is_some(),
            "installed captured authority must be ready"
        );
        request.with_policy(|| {
            let config = crate::verdict_db::live_source_bound_config();
            for part in original_parts(&source) {
                let original = crate::ay_bridge::generate_smt2_query_raw(part.obligation(), &config);
                let diagnostic = request.ay()
                    .inspect_source_bound_closed_definitions(&part, &config).unwrap();
                assert_eq!(diagnostic.smt2, original);
                assert_eq!(diagnostic.checker_accepted, Some(true));
                let checker = diagnostic.checker_sha256.as_deref().unwrap();
                let query = request.ay().prepare_source_bound(&part, AYConfig {
                    solver: config.solver.clone(),
                    timeout_ms: config.timeout_ms,
                    produce_models: config.produce_models,
                })
                    .expect("genuine reusable prepared source-bound query");
                assert_eq!(query.query_key(), crate::ay_bridge::verdict_cache_key_v2(
                    request.ay_solver().unwrap().sha256(), &original,
                ));
                let certificate_path = store.path().join(format!("{}.alethecert", query.query_key()));
                assert!(!certificate_path.exists(), "new isolated store has no AY certificate");
                assert!(!crate::ay_bridge::session_cache_contains(query.query_key()));
                for attempt in 0..2 {
                    let captured = query.execute_without_portable();
                    assert_eq!(captured.result(), &AYResult::Verified,
                        "genuine original prepared refutation is mandatory");
                    assert_constructive(captured.source(), checker);
                    assert!(captured.matches_request(&query), "retain original query/request identity");
                    assert!(!captured.reusable_for(&query),
                        "no AY reuse receipt even when caches are genuinely enabled");
                    assert!(!crate::ay_bridge::session_cache_contains(query.query_key()),
                        "constructive success must not prime an AY-positive session memo");
                    assert!(!certificate_path.exists(),
                        "constructive proof must not be persisted as AY-produced certificate");
                    let verdict: AyVerdict = captured.verdict();
                    assert_positive_journal(Some(&verdict.provenance()), checker);
                    println!(
                        "TY_ORIGINAL_CLOSED_DEFINITION_PRODUCTION route=prepared attempt={attempt} part={:?} query_key={} provenance={} reusable=false ay_certificate=false ay_session_positive=false all_part_certificate=false caller_credit=false instruction_credit=false native_credit=false",
                        part.id(), query.query_key(), verdict.provenance(),
                    );
                }
                let (result, bound, why) =
                    crate::verdict_db::live_source_bound_replay_explained(&part, &request);
                assert!(matches!(result, Some(VerificationResult::Valid)));
                assert!(!bound);
                assert_positive_journal(why.as_deref(), checker);
                assert!(!crate::ay_bridge::session_cache_contains(query.query_key()));
                assert!(!certificate_path.exists());
                assert_eq!(crate::ay_bridge::generate_smt2_query_raw(part.obligation(), &config), original);
            }
        });
        assert!(!crate::verdict_db::recording_active());
        assert_eq!(serde_json::to_value(&module).unwrap(), original_module);
        assert_eq!(serde_json::to_value(&lir).unwrap(), original_lir);
        assert_eq!(format!("{context:#?}"), original_context);
    });
}

#[test]
fn actual_original_ty_core_lir_status_and_final_memory_definition_proofs_replay() {
    crate::env_lock::with_env_overrides(
        &[
            ("TCG_REFINE_SOLVER", "1"),
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            let capture: serde_json::Value = serde_json::from_str(include_str!(
                "../tests/fixtures/ty_original_scalar_action.json"
            ))
            .unwrap();
            assert_eq!(capture["format"], "ty-original-scalar-action-source-v1");
            assert_eq!(capture["selection"]["unit_role"], "Next");
            assert_eq!(capture["selection"]["unit_key"], "next:Next@91-101");
            assert_eq!(capture["selection"]["function_id"], 60_002);
            assert_eq!(capture["selection"]["original_function_ordinal"], 3);
            let mut module: Module = serde_json::from_value(capture["module"].clone()).unwrap();
            assert!(module.target_info.is_none());
            assert_eq!(module.functions.len(), 10);
            assert_capture(&module, &capture["module"], "original whole-module image");
            module.target_info = Some(
                CoreHostJitTarget::detect()
                    .expect("actual supported Mac host")
                    .trust_ir_target_info()
                    .clone(),
            );
            let mut restored = module.clone();
            restored.target_info = None;
            assert_capture(&restored, &capture["module"], "restored whole-module image");
            let function = &module.functions[3];
            assert_eq!(function.id.index(), 60_002);
            assert_eq!(function.linkage, Linkage::Internal);
            assert_eq!(function.calling_conv, CallingConv::C);
            assert_eq!(function.blocks.len(), 16);
            assert_eq!(
                function
                    .blocks
                    .iter()
                    .map(|block| block.body.len())
                    .sum::<usize>(),
                117,
            );
            let signature = &module.func_types[function.ty.index() as usize];
            assert_eq!(signature.params, [Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::Ptr]);
            assert_eq!(signature.returns, [Ty::U64]);
            assert!(!signature.is_vararg);
            let original_module = serde_json::to_value(&module).unwrap();
            let (lir, context) = trust_cg_lower::translate_function_with_license(
                function,
                &module,
                &crate::license_test_support::permit_unlicensed(),
            )
            .unwrap();
            let original_lir = serde_json::to_value(&lir).unwrap();
            let original_context = format!("{context:#?}");
            let source = bind_scalar_memory_source(&module, 3, &lir).unwrap();
            assert!(std::ptr::eq(source.module(), &module));
            assert!(std::ptr::eq(source.source(), function));
            assert!(std::ptr::eq(source.lir(), &lir));
            assert_eq!(source.read_obligations().len(), 10);
            assert_eq!(source.write_obligations().len(), 5);
            assert_eq!(source.source_geometry().len(), 31);
            assert_eq!(source.encoding_definitions().len(), 118);
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            assert!(!request.recording_active());
            assert!(request.reuse_identity().is_none());
            let scope = FunctionDischargeContext::new(&request);
            request.with_policy(|| {
                let config = crate::verdict_db::live_source_bound_config();
                let mut status_proof = None;
                for (kind, obligation) in [
                    (ScalarMemoryRelationKind::Status, source.status_obligation()),
                    (ScalarMemoryRelationKind::FinalMemory, source.memory_obligation()),
                ] {
                    assert!(obligation.preconditions.iter().eq(
                        source.source_geometry().iter().chain(source.encoding_definitions()),
                    ));
                    let part = ScalarMemoryReplayPart {
                        id: ScalarMemoryRelationId {
                            stage: ScalarMemoryRelationStage::CoreToLir,
                            kind,
                            index: 0,
                        },
                        obligation,
                    };
                    let diagnostic = request.ay()
                        .inspect_source_bound_closed_definitions(&part, &config)
                        .expect("retain original constructive candidate and checker refusal");
                    assert_eq!(diagnostic.smt2,
                        crate::ay_bridge::generate_smt2_query_raw(obligation, &config));
                    assert_eq!(diagnostic.timeout_ms, config.timeout_ms);
                    let query_sha256 = format!("{:x}", Sha256::digest(diagnostic.smt2.as_bytes()));
                    if kind == ScalarMemoryRelationKind::Status {
                        assert_eq!(query_sha256,
                            "7e6fa1b81d4a6713480708bf5ef396e9ec2e222b2cd2d8a87fe0210b5d6c0903",
                            "pin the current byte-GEP canonical original query");
                        let legacy = crate::ay_bridge::legacy_right_spine_query_for_test(
                            obligation, &config,
                        );
                        assert_eq!(format!("{:x}", Sha256::digest(legacy.as_bytes())),
                            "d9d638b7586520eef2c1499df4d3c94f664e47e4ea863c9493ba10bfa081bf63",
                            "pin current byte-GEP right-spine query; historical reconstruction is separate");
                        assert_eq!(diagnostic.smt2.len(), legacy.len());
                        assert_ne!(diagnostic.smt2, legacy, "explicit canonical identity migration");
                    }
                    println!(
                        "TY_ORIGINAL_CLOSED_DEFINITION_PROOF part={kind:?} query_sha256={query_sha256} query_bytes={} proof_bytes={} premises={} definitions={} steps={} compose_error={:?} checker_accepted={:?} checker_error={:?} ay_ran=false all_part_certificate=false caller_credit=false instruction_credit=false native_credit=false",
                        diagnostic.smt2.len(),
                        diagnostic.proof.as_ref().map_or(0, String::len),
                        diagnostic.premises,
                        diagnostic.definitions,
                        diagnostic.steps,
                        diagnostic.compose_error,
                        diagnostic.checker_accepted,
                        diagnostic.checker_error,
                    );
                    println!("TY_ORIGINAL_CLOSED_DEFINITION_ARTIFACT_BEGIN");
                    println!("{}", serde_json::to_string(&serde_json::json!({
                        "format": "ty-original-closed-definition-proof-diagnostic-v1",
                        "fixture": "crates/trust-cg-verify/tests/fixtures/ty_original_scalar_action.json",
                        "selection": capture["selection"],
                        "original_targeted_module": &module,
                        "actual_lir": &lir,
                        "actual_adapter_proof_context_debug": &original_context,
                        "part": format!("{:?}", part.id()),
                        "geometry": source.source_geometry().iter().map(ToString::to_string).collect::<Vec<_>>(),
                        "definitions": source.encoding_definitions().iter().map(ToString::to_string).collect::<Vec<_>>(),
                        "query_sha256": query_sha256,
                        "diagnostic": &diagnostic,
                        "ay_ran": false,
                        "authority_credit": false,
                    })).unwrap());
                    println!("TY_ORIGINAL_CLOSED_DEFINITION_ARTIFACT_END");
                    assert!(diagnostic.compose_error.is_none(), "original {kind:?}: {diagnostic:?}");
                    assert_eq!(diagnostic.premises, obligation.preconditions.len());
                    assert_eq!(diagnostic.definitions, source.encoding_definitions().len());
                    assert_eq!(diagnostic.checker_accepted, Some(true),
                        "strict original {kind:?} candidate independent replay failed; no skip");
                    assert!(diagnostic.checker_error.is_none());
                    let proof = diagnostic.proof.as_deref().expect("accepted original proof text");
                    let projection = |index: usize| {
                        proof.lines().find(|line|
                            line.contains(":rule and ")
                                && line.contains(":premises (cd0)")
                                && line.contains(&format!(":args ({index})")),
                        ).expect("actual canonical root has both child projections")
                    };
                    let [left, right] = [projection(0), projection(1)];
                    let clause = |line: &str| {
                        line.split_once(" (cl ").unwrap().1
                            .split_once(") :rule and ").unwrap().0.to_owned()
                    };
                    assert_ne!(clause(left), clause(right), "nontrivial root children");
                    let wrong_index = proof.replacen(
                        left, &left.replacen(":args (0)", ":args (1)", 1), 1,
                    );
                    assert_eq!(request.ay().inspect_source_bound_definition_proof(
                        &part, &config, &wrong_index,
                    ).unwrap().0, Some(false),
                        "wrong canonical child index cannot prove the original left clause");
                    let macro_line = proof.lines().find(|line|
                        line.starts_with("(define-fun ") && line.contains(" () Bool "),
                    ).expect("actual original Boolean compound has a proof-local macro");
                    let (header, _) = macro_line.split_once(" () Bool ").unwrap();
                    let tampered = proof.replacen(macro_line, &format!("{header} () Bool false)"), 1);
                    assert_eq!(request.ay().inspect_source_bound_definition_proof(
                        &part, &config, &tampered,
                    ).unwrap().0, Some(false),
                        "a changed proof-local definition is not a new premise or source truth");
                    let mut lines = proof.lines().collect::<Vec<_>>();
                    lines.pop().expect("remove only the final refutation");
                    let truncated = lines.join("\n");
                    assert_eq!(request.ay().inspect_source_bound_definition_proof(
                        &part, &config, &truncated,
                    ).unwrap().0, Some(false), "a missing refutation cannot be accepted");
                    if kind == ScalarMemoryRelationKind::Status {
                        status_proof = Some(proof.to_owned());
                    } else {
                        assert_eq!(request.ay().inspect_source_bound_definition_proof(
                            &part, &config, status_proof.as_deref().unwrap(),
                        ).unwrap().0, Some(false), "another original part's proof is not this part's");
                    }
                    assert!(scope.replays_bound(), "inspection minted no replay receipt");
                }
            });
            assert_eq!(serde_json::to_value(&module).unwrap(), original_module);
            assert_eq!(serde_json::to_value(&lir).unwrap(), original_lir);
            assert_eq!(format!("{context:#?}"), original_context);
        },
    );
}
