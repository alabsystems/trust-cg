// Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use crate::source_bound_body::read_only_source::scalar_returns::tests::ordinary;
use crate::source_bound_frame::bind_scalar_return_source;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, encode_function_with_fixups};

fn target(
    module: &trust_ir::Module,
    opt: OptLevel,
) -> (trust_cg_lower::Function, MachFunction, Vec<u8>) {
    let (lir, context) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: opt,
        verify: false,
        ..PipelineConfig::for_target("aarch64-apple-darwin")
    });
    let (machine, _) = pipeline
        .prepare_function_with_metrics_and_trust_ir_module(
            &lir,
            Some(&context),
            module,
            &module.functions[0],
        )
        .unwrap();
    let (bytes, fixups) = encode_function_with_fixups(&machine).unwrap();
    assert!(fixups.is_empty());
    (lir, machine, bytes)
}

#[test]
fn scalar_return_producer_actual_five_results_memory_and_both_branches() {
    for memory in [false, true] {
        let module = ordinary(memory);
        for opt in [OptLevel::O0, OptLevel::O2] {
            let (lir, machine, bytes) = target(&module, opt);
            let source = bind_scalar_return_source(&module, 0, &lir).unwrap();
            let relations = ScalarReturnCompilerRelations::bind(&source, &machine, &bytes).unwrap();
            assert_eq!(source.return_codecs().len(), 5);
            for queries in [relations.machine_queries(), relations.byte_queries()] {
                assert!(!queries.memory_obligations().is_empty());
                assert_eq!(
                    queries.return_obligations().len(),
                    5 * queries.memory_obligations().len()
                );
                assert_eq!(queries.reads().is_empty(), !memory);
                assert_eq!(queries.writes().is_empty(), !memory);
            }
            assert_eq!(
                relations
                    .parts()
                    .filter(|p| p.id().stage == ScalarMemoryRelationStage::CoreToLir
                        && p.id().kind == ScalarReturnRelationKind::OrderedResult)
                    .count(),
                5
            );
            println!(
                "MULTIRESULT_PRODUCER opt={opt:?} memory={memory} parts={} bytes={} source_results=5",
                relations.len(),
                bytes.len()
            );
        }
    }
}

#[test]
fn scalar_return_producer_incomplete_return_metadata_and_policy_refuse() {
    let module = ordinary(true);
    let (lir, mut machine, bytes) = target(&module, OptLevel::O0);
    let source = bind_scalar_return_source(&module, 0, &lir).unwrap();
    let relations = ScalarReturnCompilerRelations::bind(&source, &machine, &bytes).unwrap();
    let request = FunctionVerificationRequest::capture(
        VerificationConfig::for_proof_promotion(),
        ProvenanceXCheckMode::Warn,
    );
    let report = relations.replay(&request);
    assert_eq!(
        report.refusal(),
        Some(ScalarMemoryReplayRefusal::ProvenanceNotEnforced)
    );
    assert!(report.certificate().is_none());
    assert_eq!(report.outcomes().len(), relations.len());
    assert!(
        report
            .outcomes()
            .iter()
            .all(|outcome| !outcome.attempted() && outcome.verdict().is_none())
    );
    drop(report);
    drop(relations);
    let mut changed = 0;
    for inst in &mut machine.insts {
        if inst.opcode == trust_cg_ir::AArch64Opcode::Ret {
            inst.implicit_uses = &[];
            changed += 1;
        }
    }
    assert!(changed > 0);
    assert!(ScalarReturnCompilerRelations::bind(&source, &machine, &bytes).is_err());
}

#[test]
fn scalar_return_producer_original_e1_keeps_aggregate_provider_refusal() {
    let module = trust_cg_codegen::pipeline::decode_tmbc(include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reports/2026-11-12-original-e1-machine/fixture/core.tmbc"
    )))
    .unwrap();
    let (lowerings, validation) =
        trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::AArch64,
            trust_cg_lower::TlsDialect::MachOTlv,
            &crate::license_test_support::permit_unlicensed(),
        )
        .unwrap();
    validation
        .replay_strict_call_bindings_exhaustive(&lowerings)
        .unwrap();
    let ordinal = module
        .functions
        .iter()
        .position(|f| f.name == "tla_def_0")
        .unwrap();
    let lir = &lowerings
        .iter()
        .find(|(f, _)| f.name == "tla_def_0")
        .unwrap()
        .0;
    assert_eq!(lir.signature.returns.len(), 5);
    let error = bind_scalar_return_source(&module, ordinal, lir)
        .err()
        .unwrap();
    assert_eq!(
        error,
        crate::source_bound_frame::ReadOnlySourceError::Source(
            "scalar-return calls require a checked callee/aggregate ABI owner"
        )
    );
    let declared = lir
        .blocks
        .values()
        .flat_map(|b| &b.instructions)
        .filter_map(|i| match &i.opcode {
            trust_cg_lower::instructions::Opcode::Call {
                binding:
                    trust_cg_lower::instructions::DirectCallBinding::DeclaredExternalFunction {
                        function,
                    },
                ..
            } => Some(*function),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(declared.len(), 2);
    assert!(declared.contains(&4));
    assert!(declared.contains(&5));
    println!(
        "MULTIRESULT_ORIGINAL_E1 results=5 declared_functions={declared:?} refusal={error} provider_credit=false"
    );
}

fn straight_memory_results() -> trust_ir::Module {
    use trust_ir::{CallingConv, Ty};
    use trust_ir_build::ModuleBuilder;
    let host = trust_cg_codegen::CoreHostJitTarget::detect().unwrap();
    let mut m = ModuleBuilder::new_with_target_info(
        "ordinary_live_multiresult",
        host.trust_ir_target_info().clone(),
    );
    let ty = m.add_func_type(
        vec![Ty::Ptr, Ty::U64],
        vec![Ty::Ptr, Ty::U64, Ty::I64, Ty::U64, Ty::U64],
    );
    let mut f = m.function("memory_results", ty);
    f.set_calling_conv(CallingConv::Fast);
    let entry = f.create_block();
    let pointer = f.add_block_param(entry, Ty::Ptr);
    let seed = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let old = f.load(Ty::U64, pointer);
    f.store(Ty::U64, pointer, seed);
    let negative = f.iconst(Ty::I64, -23);
    let seventeen = f.iconst(Ty::U64, 17);
    f.ret(vec![pointer, seed, negative, old, seventeen]);
    f.build();
    m.build().unwrap()
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn scalar_return_producer_live_complete_results_memory_and_causal_controls() {
    crate::env_lock::with_env_overrides(
        &[
            ("TCG_REFINE_SOLVER", "1"),
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            let module = straight_memory_results();
            let (lir, machine, bytes) = target(&module, OptLevel::O0);
            println!(
                "MULTIRESULT_INPUT={}",
                serde_json::json!({"control":"positive", "module":&module, "lir_debug":format!("{lir:#?}"), "machine_debug":format!("{machine:#?}"), "bytes":&bytes})
            );
            let source = bind_scalar_return_source(&module, 0, &lir).unwrap();
            let verifier =
                crate::FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            let relations = ScalarReturnCompilerRelations::bind(&source, &machine, &bytes).unwrap();
            let config = crate::verdict_db::live_source_bound_config();
            for part in relations.parts() {
                println!(
                    "MULTIRESULT_RAW_QUERY={}",
                    serde_json::json!({"control":"positive", "id":format!("{:?}",part.id()), "query":crate::ay_bridge::generate_smt2_query_raw(part.obligation(), &config)})
                );
            }
            let report = relations.replay(&request);
            for outcome in report.outcomes() {
                eprintln!(
                    "MULTIRESULT_LIVE {:?} {:?} {:?}",
                    outcome.id(),
                    outcome.verdict(),
                    outcome.why()
                );
            }
            if report.certificate().is_none() {
                for part in relations.parts() {
                    if report.outcomes().iter().any(|outcome| {
                        outcome.id() == part.id()
                            && outcome.attempted()
                            && !matches!(outcome.verdict(), Some(VerificationResult::Valid))
                    }) {
                        let diagnostic = request
                            .with_policy(|| {
                                request
                                    .ay()
                                    .inspect_source_bound_closed_definitions(&part, &config)
                            })
                            .unwrap();
                        println!(
                            "MULTIRESULT_FAILED_PROOF={}",
                            serde_json::json!({"id":format!("{:?}",part.id()), "diagnostic":diagnostic})
                        );
                    }
                }
            }
            assert!(
                report.certificate().is_some(),
                "every original source/machine/byte part must independently replay"
            );
            assert!(report.outcomes().iter().all(|outcome| outcome.attempted()
                && matches!(outcome.verdict(), Some(VerificationResult::Valid))));
            let mut proofs = std::collections::HashMap::new();
            for part in relations.parts() {
                let diagnostic = request
                    .with_policy(|| {
                        request
                            .ay()
                            .inspect_source_bound_closed_definitions(&part, &config)
                    })
                    .unwrap();
                if diagnostic.checker_accepted == Some(true) {
                    proofs.insert(part.id(), diagnostic.proof.as_ref().unwrap().clone());
                    println!(
                        "MULTIRESULT_PROOF={}",
                        serde_json::json!({
                            "id":format!("{:?}",part.id()), "route":"closed-definition", "diagnostic":diagnostic
                        })
                    );
                } else {
                    let diagnostic = request
                        .with_policy(|| {
                            request
                                .ay()
                                .inspect_fresh_source_bound_producer(&part, &config)
                        })
                        .unwrap();
                    println!(
                        "MULTIRESULT_PROOF={}",
                        serde_json::json!({
                            "id":format!("{:?}",part.id()), "route":"ay", "diagnostic":diagnostic
                        })
                    );
                    assert_eq!(diagnostic.checker_accepted, Some(true));
                    proofs.insert(part.id(), diagnostic.proof.as_ref().unwrap().clone());
                }
            }
            let ret = 0xd65f03c0u32.to_le_bytes();
            assert!(bytes.ends_with(&ret));
            for (label, word, failed_kind) in [
                (
                    "wrong-last-result",
                    0xd2800244u32,
                    ScalarReturnRelationKind::OrderedResult,
                ),
                (
                    "wrong-final-memory",
                    0xf9000004u32,
                    ScalarReturnRelationKind::FinalMemory,
                ),
            ] {
                let mut changed = bytes[..bytes.len() - 4].to_vec();
                changed.extend_from_slice(&word.to_le_bytes());
                changed.extend_from_slice(&ret);
                let wrong =
                    ScalarReturnCompilerRelations::bind(&source, &machine, &changed).unwrap();
                let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
                let report = wrong.replay(&request);
                assert!(report.certificate().is_none(), "{label}");
                let first = report
                    .outcomes()
                    .iter()
                    .find(|outcome| {
                        outcome.attempted()
                            && !matches!(outcome.verdict(), Some(VerificationResult::Valid))
                    })
                    .unwrap();
                println!(
                    "MULTIRESULT_REJECTION={}",
                    serde_json::json!({"control":label, "id":format!("{:?}",first.id()), "verdict":format!("{:?}",first.verdict()), "why":first.why(), "bytes":&changed})
                );
                assert!(
                    matches!(first.verdict(), Some(VerificationResult::Invalid { .. })),
                    "{label}: {:?} {:?}",
                    first.verdict(),
                    first.why()
                );
                assert_eq!(
                    first.id().stage,
                    ScalarMemoryRelationStage::CoreToFinalBytes
                );
                assert_eq!(first.id().kind, failed_kind);
                let part = wrong.parts().find(|part| part.id() == first.id()).unwrap();
                let checked = request
                    .with_policy(|| {
                        request.ay().inspect_source_bound_definition_proof(
                            &part,
                            &config,
                            &proofs[&part.id()],
                        )
                    })
                    .unwrap();
                println!(
                    "MULTIRESULT_WRONG_PROOF={}",
                    serde_json::json!({
                        "control":label, "id":format!("{:?}",part.id()), "accepted":checked.0, "why":checked.1
                    })
                );
                assert_eq!(
                    checked.0,
                    Some(false),
                    "old proof must reject the changed semantic goal"
                );
                println!(
                    "MULTIRESULT_RAW_QUERY={}",
                    serde_json::json!({"control":label,"id":format!("{:?}",part.id()),"query":crate::ay_bridge::generate_smt2_query_raw(part.obligation(), &config)})
                );
            }
        },
    );
}
