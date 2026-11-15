// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Actual independent source definitions through normal CG Core admission.
//! Source-call equations do not grant machine/body/frame/final-link authority.
#![cfg(all(feature = "verify", target_arch = "aarch64", target_os = "macos"))]

use cg::compiler::{CompileError, CoreAddressFreeMachineCompilationError};
use cg::{CoreDeclaredImportManifest, admit_identity_core_module_for_host_jit};
use sha2::{Digest, Sha256};
use trust_cg_codegen as cg;
use trust_ir::proof::{ProofEvidence, ProofLineageId};
use trust_ir::{BodyGate, FuncId, Inst};
#[cfg(feature = "source-defined-call")]
use trust_ir_build::{
    ValidationConfig,
    clean_kernel::{Expr, Name},
};
use trust_ir_build::{
    certify_identity_lineage_rung_island_bound, certify_source_bound_call_family,
    lineage_closed_with_validated_authority,
};
#[path = "common/defined_call_fixture.rs"]
mod fixture;
use fixture::*;

#[test]
fn genuine_same_island_calls_replay_and_enter_ordinary_core_planning() {
    let (module, target, lineage) = certified(42).expect("authentic defined-call family");
    lineage_closed_with_validated_authority(&module, &lineage).unwrap();
    let bytes = trust_ir::binary::serialize_module(&module).unwrap();
    let round = trust_ir::binary::deserialize_module(&bytes).unwrap();
    assert_eq!(round.proof_certificates, module.proof_certificates);
    source_validation(&round).unwrap();
    println!(
        "CG_DEFINED_CALL_MODULE_JSON={}",
        serde_json::to_string(&round).unwrap()
    );
    println!("CG_DEFINED_CALL_MODULE_SHA256={:x}", Sha256::digest(&bytes));
    let encoded: String = bytes.iter().map(|byte| format!("{byte:02x}")).collect();
    println!("CG_DEFINED_CALL_TMBC_HEX={encoded}");
    let plan = qualified_plan(round, target);
    println!("CG_DEFINED_CALL_PLAN_ID={:?}", plan.identity());
    assert_eq!(plan.retained_strict_function_count(), 2);
    assert_eq!(plan.retained_exact_module_call_count(), 1);
    assert_eq!(plan.retained_declared_external_call_count(), 0);
    println!("CG_DEFINED_CALL_SOURCE_AND_PLAN=PASS functions=2 exact_calls=1 imports=0");
}

#[test]
fn wrong_independent_callee_and_missing_binding_are_not_source_authority() {
    let error = certified(43).expect_err("different independent source must refuse");
    assert!(error.contains("kernel refusal"), "{error}");
    let (module, _, _, caller) = raw_module();
    let (island, digest) = source_island(42);
    assert!(
        certify_source_bound_call_family(
            &module,
            ProofLineageId::new(0),
            trust_ir::value::ProofId::new(0),
            transform(),
            &island,
            &[(caller, source("DefinedCalls.entry", digest))],
        )
        .is_err()
    );
    let error = certify_identity_lineage_rung_island_bound(
        &module,
        ProofLineageId::new(0),
        trust_ir::value::ProofId::new(0),
        transform(),
        caller,
        &island,
        source("DefinedCalls.entry", digest),
    )
    .unwrap_err();
    assert!(error.contains("slice 2"), "old contract: {error}");
}

#[test]
fn missing_callee_certificate_and_source_none_refuse_normal_cg_admission() {
    let (mut module, target, _) = certified(42).unwrap();
    let leaf_obligation = module
        .proof_obligations
        .iter()
        .find(|o| o.function == Some(FuncId::new(0)))
        .unwrap()
        .id;
    module
        .proof_certificates
        .retain(|c| c.obligation != leaf_obligation);
    assert!(source_validation(&module).is_err());
    assert!(
        admit_identity_core_module_for_host_jit(
            module,
            &target,
            CoreDeclaredImportManifest::empty()
        )
        .is_err()
    );
    let (mut module, target, _) = certified(42).unwrap();
    for certificate in &mut module.proof_certificates {
        if let ProofEvidence::CleanCic {
            kernel_recheck: Some(recheck),
            ..
        } = &mut certificate.evidence
        {
            recheck.binding.as_deref_mut().unwrap().source = None;
        }
    }
    assert!(source_validation(&module).is_err());
    assert!(
        admit_identity_core_module_for_host_jit(
            module,
            &target,
            CoreDeclaredImportManifest::empty()
        )
        .is_err()
    );
}

#[test]
fn changed_actual_body_cannot_keep_its_authentic_source_family() {
    let (mut module, target, _) = certified(42).unwrap();
    let leaf = module
        .functions
        .iter_mut()
        .find(|f| f.id == FuncId::new(0))
        .unwrap();
    let constant = leaf
        .blocks
        .iter_mut()
        .flat_map(|b| b.body.iter_mut())
        .find(|i| matches!(&i.inst, Inst::Const { .. }))
        .unwrap();
    let Inst::Const { value, .. } = &mut constant.inst else {
        unreachable!()
    };
    *value = trust_ir::Constant::Int(43);
    let digest = module.function_body_digest(FuncId::new(0)).unwrap();
    let leaf = module
        .functions
        .iter_mut()
        .find(|f| f.id == FuncId::new(0))
        .unwrap();
    let Some(BodyGate::Gated {
        evidence: Some(evidence),
        ..
    }) = &mut leaf.body_gate
    else {
        unreachable!()
    };
    evidence.body_digest = digest; // avoid relying only on a stale GateEvidence checksum
    assert!(source_validation(&module).is_err());
    assert!(
        admit_identity_core_module_for_host_jit(
            module,
            &target,
            CoreDeclaredImportManifest::empty()
        )
        .is_err()
    );
}

#[test]
fn source_defined_calls_do_not_mint_missing_complete_machine_authority() {
    let (module, target, _) = certified(42).unwrap();
    let independent_source = module.clone();
    let independent_strict = cg::strict_adapter::translate_core_module_for_target_with_validation(
        &independent_source,
        target.target_spec(),
    )
    .unwrap();
    assert_eq!(independent_strict.exact_module_call_count(), 1);
    let independent_lir = &independent_strict
        .functions()
        .iter()
        .find(|(function, _)| function.name == "entry")
        .unwrap()
        .0;
    let source_modules =
        trust_cg_verify::FunctionSourceModules::capture(&independent_source, &independent_source)
            .unwrap();
    let plan = qualified_plan(module, target);
    let identity = plan.identity();
    let refusal = plan
        .compile_for_installation()
        .expect_err("source equations alone cannot close call/body/frame/final-link proof");
    assert_eq!(refusal.plan().identity(), identity);
    assert_eq!(refusal.plan().retained_exact_module_call_count(), 1);
    assert!(
        matches!(refusal.reason(),
        CoreAddressFreeMachineCompilationError::Compile(CompileError::ProofPromotionRejected {
            target: cg::Target::Aarch64, reason
        }) if reason.contains("opcode_inventory_instruction_0 in entry")
            && reason.contains("2 uncovered non-pseudo opcode(s)")
            && reason.contains("[AArch64::AddRI, AArch64::Bl]")),
        "{refusal}"
    );
    let rejected = refusal
        .machine_rejection()
        .expect("the failed ordinary proof gate must retain its actual input");
    assert_eq!(rejected.source_function(), FuncId::new(1));
    assert_eq!(rejected.machine().name, "entry");
    assert!(rejected.captured().matches_aarch64_input_with_modules(
        rejected.machine(),
        Some(independent_lir),
        &source_modules,
    ));
    let mut wrong_machine = rejected.machine().clone();
    wrong_machine.name.push_str("_foreign");
    assert!(!rejected.captured().matches_aarch64_input_with_modules(
        &wrong_machine,
        Some(independent_lir),
        &source_modules,
    ));
    let mut wrong_module = independent_source.clone();
    wrong_module.name.push_str("_foreign");
    let wrong_modules =
        trust_cg_verify::FunctionSourceModules::capture(&wrong_module, &wrong_module).unwrap();
    assert!(!rejected.captured().matches_aarch64_input_with_modules(
        rejected.machine(),
        Some(independent_lir),
        &wrong_modules,
    ));
    let context = refusal
        .rejected_frame_context()
        .expect("same whole rejected input");
    assert!(std::ptr::eq(context.rejected(), rejected));
    assert_eq!(context.source_function(), FuncId::new(1));
    assert_eq!(context.source_ordinal(), 1);
    assert_eq!(context.source_modules().original().functions.len(), 2);
    assert!(rejected.captured().matches_aarch64_input_with_modules(
        rejected.machine(),
        Some(context.lir()),
        context.source_modules()
    ));
    assert!(
        rejected
            .captured()
            .matches_request_capture(context.request())
    );
    let geometry = context
        .check_static_envelopes()
        .expect("actual complete envelope");
    assert_eq!(geometry.image(), rejected.bytes());
    assert_eq!(geometry.layout_claim().total_bytes, 16);
    assert_eq!(geometry.conditional_exits().len(), 1);
    assert_eq!(
        geometry
            .unresolved_body()
            .iter()
            .map(|b| b.calls.len())
            .sum::<usize>(),
        1
    );
    assert_eq!(context.pending_patches().len(), 1);
    let mut wrong_lir = context.lir().clone();
    wrong_lir.name.push_str("_foreign");
    assert!(!rejected.captured().matches_aarch64_input_with_modules(
        rejected.machine(),
        Some(&wrong_lir),
        context.source_modules()
    ));
    let foreign_request = trust_cg_verify::FunctionVerifier::new().capture_request();
    assert!(
        !rejected
            .captured()
            .matches_request_capture(&foreign_request)
    );
    let check =
        |claim, candidates, patches: &[trust_cg_verify::aarch64_static_frame::FrameImagePatch]| {
            trust_cg_verify::aarch64_static_frame::check_static_frame_envelopes(
                context.lir(),
                rejected.machine(),
                rejected.bytes(),
                claim,
                candidates,
                patches,
            )
            .is_err()
        };
    let mut wrong_claim = context.layout_claim().clone();
    wrong_claim.total_bytes += 16;
    assert!(check(
        &wrong_claim,
        context.envelope_candidates(),
        context.pending_patches()
    ));
    let mut omitted_exit = context.envelope_candidates().clone();
    omitted_exit.epilogues.clear();
    assert!(check(
        context.layout_claim(),
        &omitted_exit,
        context.pending_patches()
    ));
    let wrong_patches = [trust_cg_verify::aarch64_static_frame::FrameImagePatch {
        offset: 0,
        bytes: 4,
    }];
    assert!(check(
        context.layout_claim(),
        context.envelope_candidates(),
        &wrong_patches
    ));
    println!(
        "CG_REJECTED_FRAME_CONTEXT=PASS frame=16 exits=1 unresolved_calls=1 pending_patches=1 authority=none"
    );
    let inventory = rejected.captured().report().emitted_opcode_inventory();
    assert_eq!(inventory.function_name, rejected.machine().name);
    for row in inventory.uncovered_non_pseudo_opcodes() {
        assert_eq!(
            trust_cg_verify::InstructionOpcode::AArch64(
                rejected.machine().insts[row.inst_index].opcode,
            ),
            row.opcode,
            "inventory coordinate must select the retained actual operand row"
        );
    }
    assert_eq!(rejected.fixup_sites().len(), 1);
    let prior = rejected.prior_replayed_functions().collect::<Vec<_>>();
    assert_eq!(prior.len(), 1);
    assert_eq!(prior[0].0, FuncId::new(0));
    assert_eq!(prior[0].1, "leaf");
    assert!(prior[0].3.has_checked_semantics());
    assert!(prior[0].3.replay_check());
    let attached = refusal
        .reattach_replayed_defined_callee(FuncId::new(0))
        .expect("same genuine callee/source/LIR/bytes/original request reattach");
    assert_eq!(attached.summary().function(), FuncId::new(0));
    assert!(attached.summary().parameter_bits().is_empty());
    assert_eq!(
        attached.summary().effects().required_private_stack_bytes(),
        0
    );
    let result = attached.instantiate_result(&[]).unwrap().unwrap();
    assert_eq!(
        result.as_ref(),
        &trust_cg_verify::smt::SmtExpr::bv_const(42, 64)
    );
    assert!(
        refusal
            .reattach_replayed_defined_callee(FuncId::new(1))
            .is_err()
    );
    assert!(
        refusal
            .reattach_replayed_defined_callee(FuncId::new(999))
            .is_err()
    );
    println!(
        "CG_DEFINED_CALL_REPLAYED_CALLEE_RELATION=PASS result={result:?} \
         private_stack_bytes=0 caller_authority=false"
    );
    println!(
        "CG_DEFINED_CALL_PRIOR_REPLAYED_FUNCTION={:?}",
        (prior[0].0, prior[0].1, prior[0].2, prior[0].3)
    );
    println!("CG_DEFINED_CALL_REJECTED_MACHINE_INPUT={rejected:#?}");
    println!("CG_DEFINED_CALL_MACHINE_REFUSAL={refusal}");
    println!("CG_DEFINED_CALL_RETURNED_MACHINE_ARTIFACTS=0");
}

#[cfg(feature = "source-defined-call")]
#[test]
fn genuine_source_call_replays_whole_original_core_entry_before_native_credit() {
    use trust_cg_verify::core_defined_call_entry::{
        DefinedCallSourceSelection, derive_core_defined_call_source,
    };
    let (module, _target, _) = certified(42).unwrap();
    let report = trust_ir_build::validate_module_with_config(
        &module,
        &ValidationConfig::pinned()
            .with_bound_certificates(true)
            .with_source_bound_certificates(true)
            .with_gate_evidence(true),
    );
    assert!(report.is_ok(), "{:?}", report.errors());
    // Independently authored source; never infer a result from module bytes.
    let (island, digest) = source_island(42);
    let selection = DefinedCallSourceSelection {
        caller: FuncId::new(1),
        callee: FuncId::new(0),
        island,
        caller_source: source("DefinedCalls.entry", digest),
        callee_source: source("DefinedCalls.leaf", digest),
    };
    let checked = derive_core_defined_call_source(&report, &selection).unwrap();
    assert_eq!(
        checked.functions_in(&module).unwrap(),
        (FuncId::new(1), FuncId::new(0))
    );
    assert!(checked.functions_in(&module.clone()).is_err());
    assert!(
        checked
            .environment()
            .audit_certification(checked.judgment(), checked.proof())
            .is_certified()
    );
    let mut names = std::collections::HashSet::new();
    checked.judgment().collect_kernel_reads_into(&mut names);
    assert!(names.contains(&Name::from_string("DefinedCalls.entry")));
    println!("CG_SOURCE_CALL_WHOLE_CORE_ENTRY=PASS original_call_count=1 native_credit=false");
}

#[cfg(feature = "source-defined-call")]
#[test]
fn original_source_call_checks_actual_linked_semantics_and_preserves_failed_rows() {
    use trust_cg_verify::core_defined_call_entry::DefinedCallSourceSelection;
    use trust_ir_build::clean_kernel::{KernelTypeError, TypeChecker};
    let selection = |literal| {
        let (island, digest) = source_island(literal);
        DefinedCallSourceSelection {
            caller: FuncId::new(1),
            callee: FuncId::new(0),
            island,
            caller_source: source("DefinedCalls.entry", digest),
            callee_source: source("DefinedCalls.leaf", digest),
        }
    };
    let (module, target, _) = certified(42).unwrap();
    let refusal = qualified_plan(module, target)
        .compile_for_installation()
        .expect_err("retain the unchanged ordinary row-proof frontier");
    let linked = refusal.link_defined_call().unwrap();
    let identity = linked.identity();
    let unsafe_context = trust_cg_process_env::with_env_overrides(
        &[("TCG_UNTRACKED_DEFINED_CALL_ENTRY_SCOPE", "1")],
        || linked.check_source(&selection(42)),
    )
    .unwrap_err();
    assert!(
        unsafe_context.reason().contains("unkeyed controls"),
        "{unsafe_context}"
    );
    assert_eq!(unsafe_context.predecessor().identity(), identity);
    let linked = unsafe_context.into_predecessor();
    let wrong_source = linked.check_source(&selection(43)).unwrap_err();
    assert!(
        wrong_source
            .reason()
            .starts_with("original source/Core entry:"),
        "wrong-stage refusal: {wrong_source}"
    );
    assert_eq!(wrong_source.predecessor().identity(), identity);
    let checked = match wrong_source.into_predecessor().check_source(&selection(42)) {
        Ok(checked) => checked,
        Err(error) => {
            // Preserve exact normal checker/producer inputs on a real frontier.
            // Diagnostic output never promotes a failed/unknown replay.
            let linked = error.predecessor();
            let endpoints = linked.verification_endpoints().unwrap();
            let bytes = endpoints.check_bytes().unwrap();
            let trace = trust_cg_verify::source_bound_defined_call::DefinedCallTrace::build(&bytes)
                .unwrap();
            let (original, producer) = trace.replay_queries(endpoints.request()).unwrap();
            let directory = std::env::temp_dir().join(".ubd").join(format!(
                "trust-cg-defined-call-replay-{}",
                std::process::id()
            ));
            std::fs::create_dir_all(&directory).unwrap();
            std::fs::write(directory.join("original.smt2"), original).unwrap();
            if let Some(producer) = producer {
                std::fs::write(directory.join("producer.smt2"), producer).unwrap();
            }
            panic!(
                "same original source/Core and actual linked trace replay: {error}; exact diagnostic inputs: {}",
                directory.display()
            );
        }
    };
    assert_eq!(checked.caller(), FuncId::new(1));
    assert_eq!(checked.callee(), FuncId::new(0));
    assert_eq!(checked.executed_words(), 7);
    assert!(checked.replayed_native_parts() > 1);
    assert_eq!(checked.required_private_stack_bytes(), 16);
    assert_eq!(checked.linked().identity(), identity);
    assert_eq!(
        checked
            .linked()
            .predecessor()
            .machine_rejection()
            .unwrap()
            .captured()
            .report()
            .emitted_opcode_inventory()
            .uncovered_non_pseudo_opcodes()
            .len(),
        2,
        "aggregate evidence must not overwrite the rejected row report"
    );
    let mut kernel = TypeChecker::new(checked.source_environment());
    kernel.set_allow_unsafe(false);
    kernel.set_allow_partial(false);
    kernel.set_heartbeat_limit(20_000_000);
    kernel.set_max_cache_entries(200_000);
    kernel
        .check_type(checked.source_proof(), checked.source_judgment())
        .unwrap();
    let error = kernel
        .check_type(checked.source_proof(), &Expr::const_str("False"))
        .expect_err("a true complete entry proof cannot prove False");
    assert!(
        matches!(error, KernelTypeError::TypeMismatch { .. }),
        "{error:?}"
    );
    assert!(
        checked
            .source_environment()
            .audit_certification(checked.source_judgment(), checked.source_proof())
            .is_certified()
    );
    assert!(checked.native_obligation().is_genuinely_proven());
    println!(
        "CG_SOURCE_CALL_LINKED_SEMANTIC_ENTRY=PASS actual_bl=true actual_trace_words=7 \
         rejected_rows_preserved=2 publication=false installation=false"
    );
}

#[cfg(feature = "source-defined-call")]
#[test]
fn original_checked_call_installs_with_distinct_replay_policy_and_owned_stack() {
    use cg::compile_service::CompileGeneration;
    use cg::jit::entry_stack::{EntryStackError, OwnedEntryStack};
    use cg::jit_contract::*;
    use trust_cg_verify::core_defined_call_entry::DefinedCallSourceSelection;
    let (module, target, _) = certified(42).unwrap();
    let (island, source_digest) = source_island(42);
    let selection = DefinedCallSourceSelection {
        caller: FuncId::new(1),
        callee: FuncId::new(0),
        island,
        caller_source: source("DefinedCalls.entry", source_digest),
        callee_source: source("DefinedCalls.leaf", source_digest),
    };
    let checked = qualified_plan(module, target)
        .compile_for_installation()
        .unwrap_err()
        .link_defined_call()
        .unwrap()
        .check_source(&selection)
        .unwrap();
    let checked_identity = checked.identity();
    let expected_image = checked.linked().image_digest();
    let entry_offset = checked
        .linked()
        .functions()
        .iter()
        .find(|f| f.function() == checked.caller())
        .unwrap()
        .range()
        .start as u64;
    let manifest = |policy: ProofPolicy, wrong_argument: bool| {
        let target = TargetDescriptor::for_trust_cg_host_jit();
        let abi = AbiDescriptor::for_trust_cg_target_os(
            cg::target::Target::Aarch64,
            target.operating_system.clone(),
        );
        let layout = LayoutManifest::lp64(Endianness::Little, 16);
        let invalidation = InvalidationKey::new(
            "source:DefinedCalls.entry",
            "sealed-core-aggregate",
            target.checksum(),
            abi.checksum(),
            layout.checksum(),
            policy.checksum(),
            1,
        );
        let mut manifest = ArtifactManifestV1::new(
            "source-call-owned-entry",
            JitArtifactKind::ExecutableMemory,
            target,
            abi,
            layout,
            invalidation,
            policy,
        );
        manifest.symbols.push(ArtifactSymbol {
            name: "entry".into(),
            visibility: SymbolVisibility::Exported,
            signature: SymbolSignature::extern_c(
                if wrong_argument {
                    vec![AbiValue::new(AbiValueKind::I64)]
                } else {
                    vec![]
                },
                vec![AbiValue::new(AbiValueKind::I64)],
            ),
            offset_bytes: Some(entry_offset),
            checksum: None,
        });
        manifest
    };
    let literal = ProofPolicy::require_certificates(std::iter::empty::<String>());
    let failure = checked
        .install_owned_stack_entry(manifest(literal.clone(), false), CompileGeneration::new(1))
        .unwrap_err();
    assert!(
        failure.reason().contains("literal per-function"),
        "{failure}"
    );
    assert_eq!(failure.predecessor().identity(), checked_identity);
    let mut replay = literal;
    replay.mode = ProofMode::RequireReplay;
    replay.require_jit_certificate = false;
    replay.required_strength = RequiredEvidenceStrength::Complete;
    let failure = failure
        .into_predecessor()
        .install_owned_stack_entry(manifest(replay.clone(), true), CompileGeneration::new(1))
        .unwrap_err();
    assert_eq!(failure.predecessor().identity(), checked_identity);
    let (entry, installed_manifest) = failure
        .into_predecessor()
        .install_owned_stack_entry(manifest(replay, false), CompileGeneration::new(1))
        .unwrap();
    assert_eq!(entry.source_function(), FuncId::new(1));
    assert_eq!(entry.required_private_stack_bytes(), 16);
    let retained = entry.aggregate_evidence().unwrap();
    assert_eq!(retained.identity(), checked_identity);
    assert_eq!(retained.linked().image_digest(), expected_image);
    assert_eq!(
        retained
            .linked()
            .predecessor()
            .machine_rejection()
            .unwrap()
            .captured()
            .report()
            .emitted_opcode_inventory()
            .uncovered_non_pseudo_opcodes()
            .len(),
        2
    );
    let proof = entry.proof_evidence();
    assert!(matches!(
        proof.strength,
        EvidenceStrength::IndependentReplay { .. }
    ));
    assert_eq!(
        proof
            .metadata
            .get("actual_jit_certificate_count")
            .map(String::as_str),
        Some("1")
    );
    assert_eq!(
        proof
            .metadata
            .get("all_function_semantics_verified")
            .map(String::as_str),
        Some("false")
    );
    assert!(
        installed_manifest
            .metadata
            .contains_key("native_payload_sha256")
    );
    let mut insufficient = OwnedEntryStack::allocate(0).unwrap();
    assert!(matches!(
        entry.invoke0_u64(&mut insufficient),
        Err(EntryStackError::Insufficient { .. })
    ));
    let mut stack = OwnedEntryStack::allocate(65_536).unwrap();
    assert_eq!(entry.invoke0_u64(&mut stack).unwrap(), 42);
    assert_eq!(entry.invoke0_u64(&mut stack).unwrap(), 42);
    println!(
        "CG_SOURCE_CALL_OWNED_NATIVE_ENTRY=PASS actual_bl=true result=42 aggregate_replay=true rejected_rows=2 caller_jit_certificate=false"
    );
}
