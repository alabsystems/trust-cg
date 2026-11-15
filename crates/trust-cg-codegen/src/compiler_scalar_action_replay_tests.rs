// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Mandatory all-part independent replay of the unchanged ORIGINAL TY action.
//! Preparation, encoding, concrete native results, pending queries and partial
//! replay do not satisfy this positive gate. Even a complete conditional
//! certificate establishes no caller permission, instruction credit or native
//! publication authority; those remain separate contracts.

#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

use crate::CoreHostJitTarget;
use crate::legacy_module_capture::assert_legacy_module_image as assert_capture;
use crate::pipeline::{OptLevel, Pipeline, PipelineConfig, encode_function_with_fixups_and_sites};
use std::collections::HashSet;
use trust_cg_verify::lowering_proof::ProofObligation;
use trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode;
use trust_cg_verify::read_only_replay::{
    ScalarMemoryCompilerRelations, ScalarMemoryRelationKind, ScalarMemoryRelationStage,
};
use trust_cg_verify::read_only_target::{ScalarMemoryTargetEndpoint, ScalarMemoryTargetQueries};
use trust_cg_verify::smt::SmtExpr;
use trust_cg_verify::source_bound_frame::{ScalarMemorySourceQueries, bind_scalar_memory_source};
use trust_cg_verify::verify::VerificationResult;
use trust_cg_verify::{FunctionVerifier, VerificationConfig};
use trust_ir::{CallingConv, Linkage, Module, Ty};

fn verdict_label(verdict: Option<&VerificationResult>) -> &'static str {
    match verdict {
        Some(VerificationResult::Valid) => "Valid",
        Some(VerificationResult::Invalid { .. }) => "Invalid",
        Some(VerificationResult::Unknown { .. }) => "Unknown",
        None => "None",
    }
}

fn source_obligation<'q>(
    source: &'q ScalarMemorySourceQueries<'_>,
    kind: ScalarMemoryRelationKind,
    index: usize,
) -> &'q ProofObligation {
    match kind {
        ScalarMemoryRelationKind::Status => {
            assert_eq!(index, 0);
            source.status_obligation()
        }
        ScalarMemoryRelationKind::FinalMemory => {
            assert_eq!(index, 0);
            source.memory_obligation()
        }
        ScalarMemoryRelationKind::Read => &source.read_obligations()[index],
        ScalarMemoryRelationKind::Write => &source.write_obligations()[index],
    }
}

fn target_obligation<'q>(
    target: &'q ScalarMemoryTargetQueries<'_>,
    kind: ScalarMemoryRelationKind,
    index: usize,
) -> &'q ProofObligation {
    match kind {
        ScalarMemoryRelationKind::Status => &target.return_obligations()[index],
        ScalarMemoryRelationKind::FinalMemory => &target.memory_obligations()[index],
        ScalarMemoryRelationKind::Read => &target.read_obligations()[index],
        ScalarMemoryRelationKind::Write => &target.write_obligations()[index],
    }
}

fn assert_target_inputs(target: &ScalarMemoryTargetQueries<'_>) {
    let source = target.source();
    assert_eq!(source.lir().signature.params.len(), 4);
    let mut architectural_inputs: Vec<_> = (0..4).map(|i| (format!("abi_x{i}"), 64)).collect();
    architectural_inputs.extend((4..31).map(|i| (format!("entry_x{i}"), 64)));
    architectural_inputs
        .extend(["entry_n", "entry_z", "entry_c", "entry_v"].map(|name| (name.into(), 1)));
    let mut expected_inputs = source.status_obligation().inputs.clone();
    expected_inputs.extend(architectural_inputs[4..].iter().cloned());
    assert_eq!(expected_inputs[4], ("observe".into(), 64));
    assert_eq!(expected_inputs[5], ("entry_x4".into(), 64));
    assert_eq!(
        target.return_obligations().len(),
        target.memory_obligations().len()
    );
    assert_eq!(target.read_obligations().len(), target.reads().len());
    assert_eq!(target.write_obligations().len(), target.writes().len());
    for query in target
        .return_obligations()
        .iter()
        .chain(target.memory_obligations())
        .chain(target.read_obligations())
        .chain(target.write_obligations())
    {
        assert_eq!(
            query.inputs, expected_inputs,
            "{} original ABI declarations",
            query.name
        );
        assert_eq!(
            query.preconditions.len(),
            source.source_geometry().len()
                + source.original_encoding_definitions().len()
                + target.encoding_definitions().len()
        );
        assert!(
            query.preconditions.iter().eq(source
                .source_geometry()
                .iter()
                .chain(source.original_encoding_definitions())
                .chain(target.encoding_definitions())),
            "{} exact original Core and endpoint premises, not count-only coverage",
            query.name
        );
    }
    // Declarations alone would miss a driver which initialized X4 from the
    // observer. Its actual equations must contain architectural inputs only.
    let mut pending: Vec<_> = target.encoding_definitions().iter().collect();
    let mut seen = HashSet::new();
    while let Some(node) = pending.pop() {
        if !seen.insert(node as *const SmtExpr) {
            continue;
        }
        if let SmtExpr::Var { name, width } = node {
            assert!(
                architectural_inputs
                    .iter()
                    .any(|(allowed, bits)| allowed == name && bits == width),
                "nonarchitectural target input {name}:{width}"
            );
        }
        node.for_each_child(&mut |child| pending.push(child));
    }
}

#[test]
fn actual_original_ty_scalar_action_endpoints_require_all_87_independent_replays() {
    trust_cg_process_env::with_env_overrides(
        &[
            ("TCG_REFINE_SOLVER", "1"),
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            let capture: serde_json::Value = serde_json::from_str(include_str!(
                "../../trust-cg-verify/tests/fixtures/ty_original_scalar_action.json"
            ))
            .unwrap();
            assert_eq!(capture["format"], "ty-original-scalar-action-source-v1");
            assert_eq!(capture["selection"]["unit_role"], "Next");
            assert_eq!(capture["selection"]["unit_key"], "next:Next@91-101");
            assert_eq!(capture["selection"]["function_id"], 60_002);
            assert_eq!(capture["selection"]["original_function_ordinal"], 3);
            let original: Module = serde_json::from_value(capture["module"].clone()).unwrap();
            assert!(original.target_info.is_none());
            assert_eq!(
                original.functions.len(),
                10,
                "no selected-function projection"
            );
            assert_capture(&original, &capture["module"], "original whole-module image");
            let host = CoreHostJitTarget::detect().expect("actual supported Mac host");
            let mut module = original.clone();
            module.target_info = Some(host.trust_ir_target_info().clone());
            let mut restored = module.clone();
            restored.target_info = None;
            assert_capture(
                &restored,
                &capture["module"],
                "host target metadata is the ONLY binding change",
            );
            let ordinal = 3;
            let function = &module.functions[ordinal];
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
            let (lir, proof_context) = trust_cg_lower::translate_function_with_license(
                function,
                &module,
                &crate::license_test_support::permit_unlicensed(),
            )
            .expect("ordinary original Core adapter");
            let lir_json = serde_json::to_value(&lir).unwrap();
            let context_debug = format!("{proof_context:#?}");
            let source = bind_scalar_memory_source(&module, ordinal, &lir)
                .expect("original scalar action source must bind");
            assert!(std::ptr::eq(source.module(), &module));
            assert!(std::ptr::eq(source.source(), function));
            assert!(std::ptr::eq(source.lir(), &lir));
            assert_eq!(source.read_obligations().len(), 10);
            assert_eq!(source.write_obligations().len(), 5);
            let mut source_inputs: Vec<_> = (0..4).map(|i| (format!("abi_x{i}"), 64)).collect();
            source_inputs.push(("observe".into(), 64));
            for query in [source.status_obligation(), source.memory_obligation()]
                .into_iter()
                .chain(source.read_obligations())
                .chain(source.write_obligations())
            {
                assert_eq!(query.inputs, source_inputs);
            }
            // Capture ONCE before any optimization-level preparation. Every
            // replay uses this exact enforced request and promotion config.
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
                    .expect("actual original action preparation");
                let machine_debug = format!("{machine:#?}");
                let (code, fixups, _) = encode_function_with_fixups_and_sites(&machine)
                    .expect("actual final encoder endpoint");
                assert!(
                    fixups.is_empty(),
                    "actual complete post-encoding endpoint; no omitted relocation"
                );
                let relations = ScalarMemoryCompilerRelations::bind(&source, &machine, &code)
                    .expect("all actual endpoints must bind, never skip");
                assert!(std::ptr::eq(relations.source(), &source));
                assert!(std::ptr::eq(relations.machine(), &machine));
                assert!(std::ptr::eq(relations.final_bytes(), code.as_slice()));
                assert!(std::ptr::eq(relations.machine_queries().source(), &source));
                assert!(std::ptr::eq(relations.byte_queries().source(), &source));
                match relations.machine_queries().endpoint() {
                    ScalarMemoryTargetEndpoint::Machine(endpoint) => {
                        assert!(std::ptr::eq(endpoint, &machine))
                    }
                    ScalarMemoryTargetEndpoint::FinalBytes(_) => panic!("wrong machine endpoint"),
                }
                match relations.byte_queries().endpoint() {
                    ScalarMemoryTargetEndpoint::FinalBytes(endpoint) => {
                        assert!(std::ptr::eq(endpoint, code.as_slice()))
                    }
                    ScalarMemoryTargetEndpoint::Machine(_) => panic!("wrong final-byte endpoint"),
                }
                assert_eq!(relations.len(), 87);
                assert!(!relations.is_empty());
                for (stage, expected) in [
                    (ScalarMemoryRelationStage::CoreToLir, 17),
                    (ScalarMemoryRelationStage::CoreToMachine, 35),
                    (ScalarMemoryRelationStage::CoreToFinalBytes, 35),
                ] {
                    assert_eq!(
                        relations
                            .parts()
                            .filter(|part| part.id().stage == stage)
                            .count(),
                        expected
                    );
                }
                assert_target_inputs(relations.machine_queries());
                assert_target_inputs(relations.byte_queries());
                for part in relations.parts() {
                    let id = part.id();
                    let exact = match id.stage {
                        ScalarMemoryRelationStage::CoreToLir => {
                            source_obligation(&source, id.kind, id.index)
                        }
                        ScalarMemoryRelationStage::CoreToMachine => {
                            target_obligation(relations.machine_queries(), id.kind, id.index)
                        }
                        ScalarMemoryRelationStage::CoreToFinalBytes => {
                            target_obligation(relations.byte_queries(), id.kind, id.index)
                        }
                    };
                    assert!(
                        std::ptr::eq(part.obligation(), exact),
                        "original borrowed obligation identity"
                    );
                }
                let report = relations.replay(&request);
                assert!(std::ptr::eq(report.relations(), &relations));
                assert!(std::ptr::eq(report.request(), &request));
                assert_eq!(
                    report.outcomes().len(),
                    87,
                    "failure cannot erase later inventory rows"
                );
                for (outcome, part) in report.outcomes().iter().zip(relations.parts()) {
                    assert_eq!(outcome.id(), part.id());
                    println!(
                        "TY_SCALAR_ACTION_REQUIRED_REPLAY level={level:?} part={:?} attempted={} verdict={} why={:?} instruction_credit=false caller_credit=false native_credit=false",
                        outcome.id(),
                        outcome.attempted(),
                        verdict_label(outcome.verdict()),
                        outcome.why()
                    );
                }
                let first_nonvalid = report.outcomes().iter().position(|outcome| {
                    !matches!(outcome.verdict(), Some(VerificationResult::Valid))
                });
                if let Some(index) = first_nonvalid {
                    assert!(
                        report.outcomes()[index + 1..]
                            .iter()
                            .all(|outcome| !outcome.attempted() && outcome.verdict().is_none()),
                        "strict replay stops after first non-Valid and retains all later not-run rows"
                    );
                }
                if let Some(certificate) = report.certificate() {
                    assert!(std::ptr::eq(certificate.relations(), &relations));
                    assert!(std::ptr::eq(certificate.request(), &request));
                    assert!(report.refusal().is_none());
                    assert!(first_nonvalid.is_none());
                    assert!(report.outcomes().iter().all(|outcome| outcome.attempted()
                        && matches!(outcome.verdict(), Some(VerificationResult::Valid))));
                    println!(
                        "TY_SCALAR_ACTION_REQUIRED_REPLAY_COMPLETE level={level:?} parts=87 certificate=true transport={:?} caller_credit=false native_credit=false",
                        certificate.transport()
                    );
                } else {
                    let first = first_nonvalid.map(|index| &report.outcomes()[index]);
                    println!(
                        "TY_SCALAR_ACTION_REQUIRED_REPLAY_COMPLETE level={level:?} parts=87 certificate=false refusal={:?} first_part={:?}",
                        report.refusal(),
                        first.map(|outcome| outcome.id())
                    );
                    failures.push(format!("{level:?}: refusal={:?}, first_part={:?}, attempted={:?}, verdict={}, why={:?}", report.refusal(), first.map(|outcome| outcome.id()), first.map(|outcome| outcome.attempted()), verdict_label(first.and_then(|outcome| outcome.verdict())), first.and_then(|outcome| outcome.why())));
                }
                assert_eq!(serde_json::to_value(&module).unwrap(), module_json);
                assert_eq!(serde_json::to_value(&lir).unwrap(), lir_json);
                assert_eq!(format!("{proof_context:#?}"), context_debug);
                assert_eq!(format!("{machine:#?}"), machine_debug);
            }
            assert!(
                failures.is_empty(),
                "mandatory all-87 original TY scalar-action replay failed: {}; no skipped positive row, partial credit, synthetic proof or finite/native substitute",
                failures.join("; ")
            );
        },
    );
}
