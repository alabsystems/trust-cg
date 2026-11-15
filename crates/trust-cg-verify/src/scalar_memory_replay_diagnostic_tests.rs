// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Retain the real first original action query and both producer transcripts.
//! This is diagnostic custody only: neither a timeout nor a producer proof
//! supplies replay, caller, native or cache authority. The mandatory all-part
//! compiler gate remains unchanged and still requires every original part.

use super::*;
use crate::legacy_module_capture::assert_legacy_module_image as assert_capture;
use crate::source_bound_frame::bind_scalar_memory_source;
use crate::{FunctionVerifier, VerificationConfig};
use sha2::{Digest, Sha256};
use trust_cg_codegen::CoreHostJitTarget;
use trust_ir::{CallingConv, Linkage, Module, Ty};

#[test]
fn actual_original_ty_first_core_lir_status_raw_and_producer_failures_are_retained() {
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
            let original: Module = serde_json::from_value(capture["module"].clone()).unwrap();
            assert!(original.target_info.is_none());
            assert_eq!(original.functions.len(), 10, "retain the whole module");
            assert_capture(&original, &capture["module"], "original whole-module image");
            let mut module = original.clone();
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
            assert_eq!(function.name, "tyw1_u1");
            assert_eq!(function.linkage, Linkage::Internal);
            assert_eq!(function.calling_conv, CallingConv::C);
            assert_eq!(function.blocks.len(), 16);
            assert_eq!(
                function
                    .blocks
                    .iter()
                    .map(|block| block.body.len())
                    .sum::<usize>(),
                117
            );
            let signature = &module.func_types[function.ty.index() as usize];
            assert_eq!(signature.params, [Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::Ptr]);
            assert_eq!(signature.returns, [Ty::U64]);
            assert!(!signature.is_vararg);
            let module_json = serde_json::to_value(&module).unwrap();
            let (lir, context) = trust_cg_lower::translate_function_with_license(
                function,
                &module,
                &crate::license_test_support::permit_unlicensed(),
            )
            .unwrap();
            let lir_json = serde_json::to_value(&lir).unwrap();
            let context_debug = format!("{context:#?}");
            let source = bind_scalar_memory_source(&module, 3, &lir).unwrap();
            assert!(std::ptr::eq(source.module(), &module));
            assert!(std::ptr::eq(source.source(), function));
            assert!(std::ptr::eq(source.lir(), &lir));
            assert_eq!(source.read_obligations().len(), 10);
            assert_eq!(source.write_obligations().len(), 5);
            let first = ScalarMemoryReplayPart {
                id: ScalarMemoryRelationId {
                    stage: ScalarMemoryRelationStage::CoreToLir,
                    kind: ScalarMemoryRelationKind::Status,
                    index: 0,
                },
                obligation: source.status_obligation(),
            };
            assert!(std::ptr::eq(first.obligation(), source.status_obligation()));
            assert!(
                first.obligation().preconditions.iter().eq(source
                    .source_geometry()
                    .iter()
                    .chain(source.encoding_definitions()))
            );
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            assert!(!request.recording_active());
            assert!(request.reuse_identity().is_none());
            let scope = FunctionDischargeContext::new(&request);
            let diagnostics = request.with_policy(|| {
                let config = crate::verdict_db::live_source_bound_config();
                let raw = request
                    .ay()
                    .inspect_fresh_source_bound(&first, &config)
                    .expect("retain the actual original raw outcome, not skip it");
                let producer = request
                    .ay()
                    .inspect_fresh_source_bound_producer(&first, &config)
                    .expect("retain the production-selected spelling outcome, not skip it");
                for diagnostic in [&raw, &producer] {
                    assert_eq!(
                        diagnostic.smt2,
                        crate::ay_bridge::generate_smt2_query_raw(first.obligation(), &config)
                    );
                    assert_eq!(diagnostic.timeout_ms, config.timeout_ms);
                    assert_eq!(
                        diagnostic.solver_sha256,
                        request
                            .ay_solver()
                            .expect("captured admitted solver")
                            .sha256()
                    );
                }
                assert_eq!(raw.producer_smt2, raw.smt2);
                assert!(!raw.producer_compact);
                assert_eq!(raw.smt2, producer.smt2);
                (raw, producer)
            });
            for (route, diagnostic) in [("raw", &diagnostics.0), ("producer", &diagnostics.1)] {
                let query_sha256 = format!("{:x}", Sha256::digest(diagnostic.smt2.as_bytes()));
                println!(
                    "TY_SCALAR_FIRST_STATUS_DIAGNOSTIC route={route} query_sha256={query_sha256} query_bytes={} producer_bytes={} producer_compact={} geometry={} core_definitions={} all_definitions={} candidate={} checker_accepted={:?} all_part_certificate=false caller_credit=false instruction_credit=false native_credit=false",
                    diagnostic.smt2.len(),
                    diagnostic.producer_smt2.len(),
                    diagnostic.producer_compact,
                    source.source_geometry().len(),
                    source.original_encoding_definitions().len(),
                    source.encoding_definitions().len(),
                    diagnostic.candidate_debug,
                    diagnostic.checker_accepted,
                );
                println!("TY_SCALAR_FIRST_STATUS_DIAGNOSTIC_ARTIFACT_BEGIN");
                println!("{}", serde_json::to_string(&serde_json::json!({
                    "format": "ty-scalar-first-original-status-diagnostic-v1",
                    "route": route,
                    "fixture": "crates/trust-cg-verify/tests/fixtures/ty_original_scalar_action.json",
                    "selection": capture["selection"],
                    "target_binding": "ordinary CoreHostJitTarget metadata only; original whole module retained",
                    "targeted_original_module": &module,
                    "actual_lir": &lir,
                    "actual_adapter_proof_context_debug": &context_debug,
                    "part": format!("{:?}", first.id()),
                    "source_geometry_smt2": source.source_geometry().iter().map(ToString::to_string).collect::<Vec<_>>(),
                    "original_encoding_definitions_smt2": source.original_encoding_definitions().iter().map(ToString::to_string).collect::<Vec<_>>(),
                    "all_encoding_definitions_smt2": source.encoding_definitions().iter().map(ToString::to_string).collect::<Vec<_>>(),
                    "query_sha256": query_sha256,
                    "diagnostic": diagnostic,
                    "authority_credit": false,
                })).unwrap());
                println!("TY_SCALAR_FIRST_STATUS_DIAGNOSTIC_ARTIFACT_END");
            }
            assert!(scope.replays_bound(), "inspection minted no replay receipt");
            assert_eq!(serde_json::to_value(&module).unwrap(), module_json);
            assert_eq!(serde_json::to_value(&lir).unwrap(), lir_json);
            assert_eq!(format!("{context:#?}"), context_debug);
        },
    );
}

/// Capture the same original action's first allocated-machine status relation,
/// not a reconstructed machine fixture or a smaller substitute query. Neither
/// successful inspection nor an AY failure discharges the mandatory 87-part
/// compiler gate. The existing source-only diagnostic above stays unchanged.
#[test]
fn actual_original_ty_first_core_machine_status_raw_and_producer_failures_are_retained() {
    use crate::memory_proofs::memory_sort;
    use crate::read_only_target::{ScalarMemoryTargetEndpoint, bind_scalar_memory_machine};
    use crate::smt::SmtExpr;
    use std::collections::HashSet;
    use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};

    crate::env_lock::with_env_overrides(
        &[
            ("TCG_REFINE_SOLVER", "1"),
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            let fixture_text = include_str!("../tests/fixtures/ty_original_scalar_action.json");
            let fixture_sha256 = format!("{:x}", Sha256::digest(fixture_text.as_bytes()));
            let capture: serde_json::Value = serde_json::from_str(fixture_text).unwrap();
            assert_eq!(capture["format"], "ty-original-scalar-action-source-v1");
            assert_eq!(capture["selection"]["unit_role"], "Next");
            assert_eq!(capture["selection"]["unit_key"], "next:Next@91-101");
            assert_eq!(capture["selection"]["function_id"], 60_002);
            assert_eq!(capture["selection"]["original_function_ordinal"], 3);
            let original: Module = serde_json::from_value(capture["module"].clone()).unwrap();
            assert!(original.target_info.is_none());
            assert_eq!(original.functions.len(), 10, "retain the whole module");
            assert_capture(&original, &capture["module"], "original whole-module image");
            let host = CoreHostJitTarget::detect().expect("actual supported Mac host");
            let mut module = original.clone();
            module.target_info = Some(host.trust_ir_target_info().clone());
            let mut restored = module.clone();
            restored.target_info = None;
            assert_capture(&restored, &capture["module"], "restored whole-module image");
            let function = &module.functions[3];
            assert_eq!(function.id.index(), 60_002);
            assert_eq!(function.name, "tyw1_u1");
            assert_eq!(function.linkage, Linkage::Internal);
            assert_eq!(function.calling_conv, CallingConv::C);
            assert_eq!(function.blocks.len(), 16);
            assert_eq!(
                function
                    .blocks
                    .iter()
                    .map(|block| block.body.len())
                    .sum::<usize>(),
                117
            );
            let signature = &module.func_types[function.ty.index() as usize];
            assert_eq!(signature.params, [Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::Ptr]);
            assert_eq!(signature.returns, [Ty::U64]);
            assert!(!signature.is_vararg);
            let module_json = serde_json::to_value(&module).unwrap();
            let (lir, context) = trust_cg_lower::translate_function_with_license(
                function,
                &module,
                &crate::license_test_support::permit_unlicensed(),
            )
            .expect("ordinary adapter on the unchanged original Core");
            let lir_json = serde_json::to_value(&lir).unwrap();
            let context_debug = format!("{context:#?}");
            let source = bind_scalar_memory_source(&module, 3, &lir)
                .expect("the original whole action source must bind");
            assert!(std::ptr::eq(source.module(), &module));
            assert!(std::ptr::eq(source.source(), function));
            assert!(std::ptr::eq(source.lir(), &lir));
            // Fixture qualification, not proof or a production admission rule.
            assert_eq!(source.read_obligations().len(), 10);
            assert_eq!(source.write_obligations().len(), 5);
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            // ONE authority and policy snapshot, captured before all preparation.
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            assert!(!request.recording_active());
            assert!(request.reuse_identity().is_none());
            let scope = FunctionDischargeContext::new(&request);
            for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let pipeline = Pipeline::new(PipelineConfig {
                    opt_level: level,
                    verify: false,
                    ..PipelineConfig::for_target(host.target_spec().triple())
                });
                let (machine, _) = pipeline
                    .prepare_function_with_metrics_and_trust_ir_module(
                        &lir,
                        Some(&context),
                        &module,
                        function,
                    )
                    .expect("actual allocated endpoint, never a substituted fixture");
                let machine_debug = format!("{machine:#?}");
                let target = bind_scalar_memory_machine(&source, &machine)
                    .expect("the complete actual machine endpoint must bind");
                assert!(std::ptr::eq(target.source(), &source));
                match target.endpoint() {
                    ScalarMemoryTargetEndpoint::Machine(endpoint) => {
                        assert!(std::ptr::eq(endpoint, &machine));
                    }
                    ScalarMemoryTargetEndpoint::FinalBytes(_) => panic!("wrong machine endpoint"),
                }
                let first = ScalarMemoryReplayPart {
                    id: ScalarMemoryRelationId {
                        stage: ScalarMemoryRelationStage::CoreToMachine,
                        kind: ScalarMemoryRelationKind::Status,
                        index: 0,
                    },
                    obligation: target
                        .return_obligations()
                        .first()
                        .expect("retain the actual first return relation"),
                };
                assert!(std::ptr::eq(
                    first.obligation(),
                    &target.return_obligations()[0]
                ));
                assert_eq!(
                    first.obligation().name,
                    "Original scalar-memory Core -> actual MachIR full status 0"
                );
                assert!(
                    first.obligation().preconditions.iter().eq(source
                        .source_geometry()
                        .iter()
                        .chain(source.original_encoding_definitions())
                        .chain(target.encoding_definitions()))
                );
                let mut expected_inputs = source.status_obligation().inputs.clone();
                let abi_arity = source.lir().signature.params.len();
                expected_inputs.extend((abi_arity..31).map(|i| (format!("entry_x{i}"), 64)));
                expected_inputs
                    .extend(["entry_n", "entry_z", "entry_c", "entry_v"].map(|n| (n.into(), 1)));
                assert_eq!(first.obligation().inputs, expected_inputs);
                assert_eq!(expected_inputs[abi_arity], ("observe".into(), 64));
                assert_eq!(
                    expected_inputs[abi_arity + 1],
                    (format!("entry_x{abi_arity}"), 64),
                    "the observer is not the next architectural argument"
                );
                // Inspect original syntax only: retain arbitrary entry_memory,
                // and never initialize a target register from the observer.
                // No evaluation or rewrite supplies a proof here.
                let mut pending: Vec<_> = first.obligation().preconditions.iter().collect();
                pending.push(&first.obligation().trust_ir_expr);
                pending.push(&first.obligation().aarch64_expr);
                let mut seen = HashSet::new();
                let mut entry_memory_present = false;
                while let Some(node) = pending.pop() {
                    if !seen.insert(node as *const SmtExpr) {
                        continue;
                    }
                    if let SmtExpr::UF {
                        name,
                        args,
                        ret_sort,
                    } = node
                        && name == "entry_memory"
                    {
                        assert!(args.is_empty());
                        assert_eq!(*ret_sort, memory_sort());
                        entry_memory_present = true;
                    }
                    node.for_each_child(&mut |child| pending.push(child));
                }
                assert!(
                    entry_memory_present,
                    "no concrete/uniform memory substitute"
                );
                let mut pending: Vec<_> = target.encoding_definitions().iter().collect();
                let mut seen = HashSet::new();
                while let Some(node) = pending.pop() {
                    if !seen.insert(node as *const SmtExpr) {
                        continue;
                    }
                    if let SmtExpr::Var { name, .. } = node {
                        assert_ne!(name, "observe", "observer is not architectural state");
                    }
                    node.for_each_child(&mut |child| pending.push(child));
                }
                let diagnostics = request.with_policy(|| {
                    let config = crate::verdict_db::live_source_bound_config();
                    // Inspect the untrusted constructive candidate against
                    // THIS unchanged original machine relation. Capture its
                    // actual refusal separately from the ordinary AY outcome;
                    // neither inspection supplies an all-part certificate.
                    let constructive = request.ay()
                        .inspect_source_bound_closed_definitions(&first, &config)
                        .expect("retain the actual original machine candidate outcome");
                    assert_eq!(constructive.smt2,
                        crate::ay_bridge::generate_smt2_query_raw(first.obligation(), &config));
                    assert_eq!(constructive.timeout_ms, config.timeout_ms);
                    println!("TY_SCALAR_MACHINE_CONSTRUCTIVE_DIAGNOSTIC level={level:?} ay_ran=false all_part_certificate=false native_credit=false {}",
                        serde_json::to_string(&constructive).unwrap());
                    let raw = request
                        .ay()
                        .inspect_fresh_source_bound(&first, &config)
                        .expect("retain the original raw solve outcome, not skip it");
                    let producer = request
                        .ay()
                        .inspect_fresh_source_bound_producer(&first, &config)
                        .expect("retain the production spelling outcome, not skip it");
                    for diagnostic in [&raw, &producer] {
                        assert_eq!(
                            diagnostic.smt2,
                            crate::ay_bridge::generate_smt2_query_raw(first.obligation(), &config)
                        );
                        assert_eq!(diagnostic.timeout_ms, config.timeout_ms);
                        assert_eq!(
                            diagnostic.solver_sha256,
                            request
                                .ay_solver()
                                .expect("captured admitted solver")
                                .sha256()
                        );
                    }
                    assert_eq!(raw.producer_smt2, raw.smt2);
                    assert!(!raw.producer_compact);
                    assert_eq!(raw.smt2, producer.smt2);
                    assert_eq!(raw.solver_path, producer.solver_path);
                    assert_eq!(raw.checker_path, producer.checker_path);
                    assert_eq!(raw.checker_sha256, producer.checker_sha256);
                    (raw, producer)
                });
                for (route, diagnostic) in [("raw", &diagnostics.0), ("producer", &diagnostics.1)] {
                    let query_sha256 = format!("{:x}", Sha256::digest(diagnostic.smt2.as_bytes()));
                    println!(
                        "TY_SCALAR_FIRST_MACHINE_STATUS_DIAGNOSTIC level={level:?} route={route} query_sha256={query_sha256} query_bytes={} producer_bytes={} producer_compact={} geometry={} core_definitions={} machine_definitions={} candidate={} solve_error={:?} checker_accepted={:?} all_part_certificate=false caller_credit=false instruction_credit=false native_credit=false",
                        diagnostic.smt2.len(),
                        diagnostic.producer_smt2.len(),
                        diagnostic.producer_compact,
                        source.source_geometry().len(),
                        source.original_encoding_definitions().len(),
                        target.encoding_definitions().len(),
                        diagnostic.candidate_debug,
                        diagnostic.solve_error,
                        diagnostic.checker_accepted,
                    );
                    println!("TY_SCALAR_FIRST_MACHINE_STATUS_DIAGNOSTIC_ARTIFACT_BEGIN");
                    println!("{}", serde_json::to_string(&serde_json::json!({
                        "format": "ty-scalar-first-original-machine-status-diagnostic-v1",
                        "level": format!("{level:?}"),
                        "route": route,
                        "fixture": "crates/trust-cg-verify/tests/fixtures/ty_original_scalar_action.json",
                        "fixture_sha256": fixture_sha256,
                        "selection": capture["selection"],
                        "source_provenance": capture["source_provenance"],
                        "literal_pool": capture["literal_pool"],
                        "literal_pool_u64le_sha256": capture["literal_pool_u64le_sha256"],
                        "target_binding": "ordinary CoreHostJitTarget metadata only; original whole module retained",
                        "targeted_original_module": &module,
                        "actual_lir": &lir,
                        "actual_adapter_proof_context_debug": &context_debug,
                        "actual_complete_prepared_machine_debug": &machine_debug,
                        "part": format!("{:?}", first.id()),
                        "query_name": &first.obligation().name,
                        "query_inputs": &first.obligation().inputs,
                        "source_expression_smt2": first.obligation().trust_ir_expr.to_string(),
                        "machine_expression_smt2": first.obligation().aarch64_expr.to_string(),
                        "source_geometry_smt2": source.source_geometry().iter().map(ToString::to_string).collect::<Vec<_>>(),
                        "original_encoding_definitions_smt2": source.original_encoding_definitions().iter().map(ToString::to_string).collect::<Vec<_>>(),
                        "machine_encoding_definitions_smt2": target.encoding_definitions().iter().map(ToString::to_string).collect::<Vec<_>>(),
                        "machine_inventory_counts": {
                            "statuses": target.return_obligations().len(),
                            "final_memories": target.memory_obligations().len(),
                            "read_demands": target.read_obligations().len(),
                            "write_demands": target.write_obligations().len(),
                        },
                        "query_sha256": query_sha256,
                        "diagnostic": diagnostic,
                        "authority_credit": false,
                        "mandatory_all_87_gate_changed": false,
                    })).unwrap());
                    println!("TY_SCALAR_FIRST_MACHINE_STATUS_DIAGNOSTIC_ARTIFACT_END");
                }
                assert!(
                    scope.replays_bound(),
                    "inspection performed no promoted replay"
                );
                assert_eq!(serde_json::to_value(&module).unwrap(), module_json);
                assert_eq!(serde_json::to_value(&lir).unwrap(), lir_json);
                assert_eq!(format!("{context:#?}"), context_debug);
                assert_eq!(format!("{machine:#?}"), machine_debug);
            }
        },
    );
}
