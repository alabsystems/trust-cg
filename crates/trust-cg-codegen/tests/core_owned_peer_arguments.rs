// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Independently authored scalar argument flowing through the actual framed
//! source caller, exact defined callee, and owned native entry.
#![cfg(all(feature = "verify", target_arch = "aarch64", target_os = "macos"))]

use sha2::{Digest, Sha256};
use trust_cg_codegen as cg;
use trust_ir::proof::{
    IslandEnvironment, ProofDigest, ProofLineageId, SourceDefinitionRef,
    encode_island_declarations_v1,
};
use trust_ir::{BodyGate, FuncId, GateEvidence, Linkage, Module, Ty};
use trust_ir_build::clean_kernel::{BinderInfo, Declaration, Expr, Name};
use trust_ir_build::{ModuleBuilder, certify_source_bound_call_family};

#[path = "common/defined_call_fixture.rs"]
mod fixture;

#[derive(Clone, Copy)]
enum CallerRoute {
    Forward,
    ConstantArgument,
    WrongSourceArgument,
    ReturnInput,
}

fn forwarding_source_with_leaf(
    use_input: bool,
    increment: bool,
) -> Result<(Module, cg::CoreHostJitTarget), String> {
    forwarding_source(use_input, increment, CallerRoute::Forward)
}

fn forwarding_source(
    use_input: bool,
    increment: bool,
    route: CallerRoute,
) -> Result<(Module, cg::CoreHostJitTarget), String> {
    let target = cg::CoreHostJitTarget::detect().expect("supported actual host");
    let mut builder = ModuleBuilder::new_with_target_info(
        "independent_forwarded_peer",
        target.trust_ir_target_info().clone(),
    );
    let signature = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut leaf = builder.function("leaf", signature);
    let entry = leaf.create_block();
    let input = leaf.add_block_param(entry, Ty::U64);
    leaf.switch_to_block(entry);
    let result = if increment {
        let seven = leaf.iconst(Ty::U64, 7);
        leaf.add(Ty::U64, input, seven)
    } else {
        input
    };
    leaf.ret(vec![result]);
    let leaf_id = leaf.build();
    let mut caller = builder.function("entry", signature);
    let entry = caller.create_block();
    let input = caller.add_block_param(entry, Ty::U64);
    caller.switch_to_block(entry);
    let argument = if matches!(route, CallerRoute::ConstantArgument) {
        caller.iconst(Ty::U64, 0)
    } else {
        input
    };
    let returned = caller.call(leaf_id, vec![argument]);
    caller.ret(vec![if matches!(route, CallerRoute::ReturnInput) {
        input
    } else {
        returned
    }]);
    let caller_id = caller.build();
    let mut module = builder.build().expect("ordinary typed argument and call");
    module
        .functions
        .iter_mut()
        .find(|f| f.id == leaf_id)
        .unwrap()
        .linkage = Linkage::Internal;

    let nat = Expr::const_str("Nat");
    let definitions = [
        Declaration::Definition {
            name: Name::from_string("ForwardedCalls.leaf"),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
            value: Expr::lam(
                BinderInfo::Default,
                nat.clone(),
                if !use_input {
                    Expr::nat_lit(0)
                } else if increment {
                    Expr::apps(
                        Expr::const_str("Nat.mod"),
                        [
                            Expr::apps(
                                Expr::const_str("Nat.add"),
                                [Expr::bvar(0), Expr::nat_lit(7)],
                            ),
                            Expr::nat_lit_u128(1u128 << 64),
                        ],
                    )
                } else {
                    Expr::bvar(0)
                },
            ),
            is_reducible: true,
        },
        Declaration::Definition {
            name: Name::from_string("ForwardedCalls.entry"),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
            value: Expr::lam(
                BinderInfo::Default,
                nat,
                if matches!(route, CallerRoute::ReturnInput) {
                    Expr::bvar(0)
                } else {
                    Expr::app(
                        Expr::const_str("ForwardedCalls.leaf"),
                        if matches!(
                            route,
                            CallerRoute::ConstantArgument | CallerRoute::WrongSourceArgument
                        ) {
                            Expr::nat_lit(0)
                        } else {
                            Expr::bvar(0)
                        },
                    )
                },
            ),
            is_reducible: true,
        },
    ];
    let bytes = encode_island_declarations_v1(&definitions).unwrap();
    let digest = ProofDigest::sha256(Sha256::digest(&bytes).into());
    let island = IslandEnvironment::new(bytes);
    let source = |name: &str| SourceDefinitionRef {
        decl: name.into(),
        closure_digest: digest,
    };
    let family = certify_source_bound_call_family(
        &module,
        ProofLineageId::new(0),
        trust_ir::value::ProofId::new(0),
        fixture::transform(),
        &island,
        &[
            (caller_id, source("ForwardedCalls.entry")),
            (leaf_id, source("ForwardedCalls.leaf")),
        ],
    )
    .map_err(|error| format!("{error:?}"))?;
    let gates: Vec<_> = module
        .functions
        .iter()
        .map(|function| {
            let obligation = family
                .obligations
                .iter()
                .find(|o| o.function == Some(function.id))
                .unwrap();
            (
                function.id,
                obligation.id,
                module.function_body_digest(function.id).unwrap(),
            )
        })
        .collect();
    for (function, obligation, body_digest) in gates {
        let function = module
            .functions
            .iter_mut()
            .find(|f| f.id == function)
            .unwrap();
        function.body_gate = Some(BodyGate::Gated {
            authority: cg::CLEAN_KERNEL_TV_AUTHORITY.into(),
            evidence: Some(GateEvidence {
                obligation,
                body_digest,
            }),
        });
    }
    module.proof_obligations.extend(family.obligations);
    module.proof_certificates.extend(family.certificates);
    Ok((module, target))
}

fn manifest(arguments: usize) -> cg::jit_contract::ArtifactManifestV1 {
    use cg::jit_contract::*;
    let target = TargetDescriptor::for_trust_cg_host_jit();
    let abi = AbiDescriptor::for_trust_cg_target_os(
        cg::target::Target::Aarch64,
        target.operating_system.clone(),
    );
    let layout = LayoutManifest::lp64(Endianness::Little, 16);
    let policy = ProofPolicy::require_certificates(std::iter::empty::<String>());
    let invalidation = InvalidationKey::new(
        "source:ForwardedCalls.entry",
        "sealed-core",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        policy.checksum(),
        1,
    );
    let mut manifest = ArtifactManifestV1::new(
        "source-bound-forwarded-peer",
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
            vec![AbiValue::new(AbiValueKind::I64); arguments],
            vec![AbiValue::new(AbiValueKind::I64)],
        ),
        offset_bytes: None,
        checksum: None,
    });
    manifest
}

#[test]
fn one_argument_source_executes_through_the_actual_framed_peer() {
    use cg::jit::entry_stack::{EntryStackError, OwnedEntryStack};
    let (module, target) = forwarding_source_with_leaf(true, true).unwrap();
    fixture::source_validation(&module).expect("actual source, complete family, unchanged license");
    let source_bytes = trust_ir::binary::serialize_module(&module).unwrap();
    println!(
        "CORE_FORWARDED_SOURCE_MODULE_SHA256={:x}",
        Sha256::digest(&source_bytes)
    );
    println!(
        "CORE_FORWARDED_SOURCE_MODULE_HEX={}",
        source_bytes
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>()
    );
    let round = trust_ir::binary::deserialize_module(&source_bytes).unwrap();
    fixture::source_validation(&round).expect("serialized original source and proof family replay");
    let conditional = fixture::qualified_plan(round, target)
        .compile_for_owned_peer_entry("entry")
        .expect("one-word original caller, callee, frame and final BL must replay");
    assert_eq!(conditional.source_function(), FuncId::new(1));
    assert_eq!(conditional.required_private_stack_bytes(), 16);
    assert_eq!(
        conditional.diagnostic_report().genuinely_verified_count(),
        0
    );
    let (mut entry, _) = conditional
        .install_owned_stack(
            OwnedEntryStack::allocate(65_536).unwrap(),
            manifest(1),
            cg::compile_service::CompileGeneration::new(1),
        )
        .expect("actual private stack and installed source-call owner");
    assert!(matches!(
        entry.invoke0_u64(),
        Err(EntryStackError::ArgumentCount {
            expected: 1,
            actual: 0
        })
    ));
    for value in [0, 1, 42, 1u64 << 63, u64::MAX, 0xdead_beef_0123_4567] {
        let actual = entry.invoke1_u64(value).unwrap();
        assert_eq!(actual, value.wrapping_add(7));
        println!("CORE_FORWARDED_NATIVE_INPUT={value:016x} OUTPUT={actual:016x}");
    }
    println!("CORE_ORIGINAL_FORWARDED_PEER_NATIVE=PASS arguments=1 high_bit=true frame_bytes=16");
}

#[test]
fn zero_argument_peer_rejects_the_one_argument_entry_route() {
    use cg::jit::entry_stack::{EntryStackError, OwnedEntryStack};
    let (module, target, _) = fixture::certified(42).unwrap();
    let conditional = fixture::qualified_plan(module, target)
        .compile_for_owned_peer_entry("entry")
        .unwrap();
    let (mut entry, _) = conditional
        .install_owned_stack(
            OwnedEntryStack::allocate(65_536).unwrap(),
            manifest(0),
            cg::compile_service::CompileGeneration::new(1),
        )
        .unwrap();
    assert!(matches!(
        entry.invoke1_u64(u64::MAX),
        Err(EntryStackError::ArgumentCount {
            expected: 0,
            actual: 1
        })
    ));
    assert_eq!(entry.invoke0_u64().unwrap(), 42);
}

#[test]
fn forwarded_peer_rejects_a_zero_argument_manifest() {
    use cg::jit::entry_stack::OwnedEntryStack;
    let (module, target) = forwarding_source_with_leaf(true, true).unwrap();
    let conditional = fixture::qualified_plan(module, target)
        .compile_for_owned_peer_entry("entry")
        .unwrap();
    let error = conditional
        .install_owned_stack(
            OwnedEntryStack::allocate(65_536).unwrap(),
            manifest(0),
            cg::compile_service::CompileGeneration::new(1),
        )
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("compile.manifest_signature_mismatch"),
        "{error}"
    );
}

#[test]
fn forwarded_peer_requires_the_genuine_original_parameter_result() {
    let error = forwarding_source_with_leaf(false, true).unwrap_err();
    assert!(error.contains("source equation kernel refusal"), "{error}");
}

#[test]
fn ret_only_identity_callee_keeps_the_existing_formal_report_refusal() {
    let (module, target) = forwarding_source_with_leaf(true, false).unwrap();
    fixture::source_validation(&module).unwrap();
    let failure = fixture::qualified_plan(module, target)
        .compile_for_owned_peer_entry("entry")
        .unwrap_err();
    assert!(
        failure
            .reason()
            .to_string()
            .contains("complete nondegenerate Formal report")
    );
}

#[test]
fn original_caller_argument_is_checked_against_its_own_source_equation() {
    // Keep the actual IR call forwarding its live parameter. Change only the
    // independently authored caller source to leaf(0), leaving the leaf genuine.
    let error = forwarding_source(true, true, CallerRoute::WrongSourceArgument).unwrap_err();
    assert!(error.contains("source equation kernel refusal"), "{error}");
    println!("CORE_FORWARDED_WRONG_CALLER_SOURCE_ARGUMENT=REFUSED");
}

#[test]
fn a_source_checked_constant_argument_is_not_a_live_forwarding_peer() {
    // This is a valid different source program, not a malformed certificate:
    // entry(x)=leaf(0). The narrow entry owner must not claim live forwarding.
    let (module, target) = forwarding_source(true, true, CallerRoute::ConstantArgument).unwrap();
    fixture::source_validation(&module).expect("genuine constant-argument source still checks");
    let failure = fixture::qualified_plan(module, target)
        .compile_for_owned_peer_entry("entry")
        .unwrap_err();
    let reason = failure.reason().to_string();
    assert!(
        reason.contains("requires one zero- or one-word forwarding 64-bit call/return")
            || reason.contains("conditional peer requires exactly one actual earlier callee and one final caller/fixup"),
        "{reason}"
    );
    println!("CORE_SOURCE_CHECKED_CONSTANT_ARGUMENT_PEER=REFUSED reason={reason}");
}

#[test]
fn a_source_checked_discarded_callee_result_is_not_the_checked_return_route() {
    // entry(x) calls the real leaf but returns x. Its source equation is valid;
    // it must not borrow the peer owner's return-of-callee-result authority.
    let (module, target) = forwarding_source(true, true, CallerRoute::ReturnInput).unwrap();
    fixture::source_validation(&module).expect("genuine discarded-result source still checks");
    let failure = fixture::qualified_plan(module, target)
        .compile_for_owned_peer_entry("entry")
        .unwrap_err();
    let reason = failure.reason().to_string();
    assert!(
        reason.contains("actual call/result/callee identity differs")
            || reason.contains("LIR argument/result route differs")
            || reason.contains("conditional peer requires exactly one actual earlier callee and one final caller/fixup")
            || reason.contains("actual producer frame is outside the bounded peer domain"),
        "{reason}"
    );
    println!("CORE_SOURCE_CHECKED_DISCARDED_CALLEE_RESULT=REFUSED reason={reason}");
}

// Independent source declarations: these are not recovered from proof metadata.
#[cfg(feature = "source-defined-call")]
fn universal_source_selection(
    increment: u64,
) -> trust_cg_verify::core_defined_call_entry::DefinedCallSourceSelection {
    let nat = Expr::const_str("Nat");
    let definitions = [
        Declaration::Definition {
            name: Name::from_string("ForwardedCalls.leaf"),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
            value: Expr::lam(
                BinderInfo::Default,
                nat.clone(),
                Expr::apps(
                    Expr::const_str("Nat.mod"),
                    [
                        Expr::apps(
                            Expr::const_str("Nat.add"),
                            [Expr::bvar(0), Expr::nat_lit(increment)],
                        ),
                        Expr::nat_lit_u128(1u128 << 64),
                    ],
                ),
            ),
            is_reducible: true,
        },
        Declaration::Definition {
            name: Name::from_string("ForwardedCalls.entry"),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
            value: Expr::lam(
                BinderInfo::Default,
                nat,
                Expr::app(Expr::const_str("ForwardedCalls.leaf"), Expr::bvar(0)),
            ),
            is_reducible: true,
        },
    ];
    let bytes = encode_island_declarations_v1(&definitions).unwrap();
    let digest = ProofDigest::sha256(Sha256::digest(&bytes).into());
    trust_cg_verify::core_defined_call_entry::DefinedCallSourceSelection {
        caller: FuncId::new(1),
        callee: FuncId::new(0),
        island: IslandEnvironment::new(bytes),
        caller_source: SourceDefinitionRef {
            decl: "ForwardedCalls.entry".into(),
            closure_digest: digest,
        },
        callee_source: SourceDefinitionRef {
            decl: "ForwardedCalls.leaf".into(),
            closure_digest: digest,
        },
    }
}

#[cfg(feature = "source-defined-call")]
fn retain_source_word_proof_data(
    entry: &cg::compiler::CoreSourceWordEntry,
    selection: &trust_cg_verify::core_defined_call_entry::DefinedCallSourceSelection,
    samples: &[(u64, u64)],
) {
    use std::collections::{BTreeMap, HashSet};
    let scratch = std::env::temp_dir().join(".ubd");
    std::fs::create_dir_all(&scratch).unwrap();
    let directory = tempfile::Builder::new()
        .prefix("trust-cg-source-word-custody-")
        .tempdir_in(scratch)
        .unwrap()
        .keep();
    let roots = [
        ("source-query", entry.source_judgment()),
        ("source-proof", entry.source_proof()),
        ("argument-codec-query", entry.argument_codec_claim()),
        ("argument-codec-proof", entry.argument_codec_proof()),
    ];
    let mut files = BTreeMap::new();
    let mut write = |name: &str, bytes: &[u8]| {
        std::fs::write(directory.join(name), bytes).unwrap();
        files.insert(
            name.to_owned(),
            serde_json::json!({
                "bytes": bytes.len(), "sha256": format!("{:x}", Sha256::digest(bytes)),
            }),
        );
    };
    write(
        "original-module.tmbc",
        &trust_ir::binary::serialize_module(entry.original_module()).unwrap(),
    );
    write(
        "source-island.declarations-v1",
        &selection.island.declarations,
    );
    let mut pending = Vec::new();
    for (name, expression) in roots {
        let bytes = trust_ir::proof::encode_clean_expr_dag_v2(expression).unwrap();
        assert_eq!(
            trust_ir::proof::decode_clean_expr_dag_v2(&bytes).unwrap(),
            *expression
        );
        write(&format!("{name}.expr-dag-v2"), &bytes);
        pending.extend(expression.collect_constants());
    }
    let environment = entry.source_environment();
    let digest = environment.content_digest();
    write(
        "environment-summary.txt",
        digest.render_summary().as_bytes(),
    );
    write(
        "environment-entries.tsv",
        digest.render_entries().as_bytes(),
    );
    let mut seen = HashSet::new();
    let mut declarations = BTreeMap::new();
    while let Some(name) = pending.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        assert!(
            seen.len() <= 100_000,
            "proof-data closure exceeds diagnostic bound"
        );
        let constant = environment.get_const(&name);
        if let Some(info) = constant {
            pending.extend(info.type_.collect_constants());
            if let Some(value) = &info.value {
                pending.extend(value.collect_constants());
            }
        }
        declarations.insert(
            name.to_string(),
            serde_json::json!({
                "kernel_record_digest": environment.kernel_record_digest(&name)
                    .map(|bytes| bytes.iter().map(|b| format!("{b:02x}")).collect::<String>()),
                "has_constant_info": constant.is_some(),
            }),
        );
    }
    write(
        "syntactic-declaration-closure.json",
        &serde_json::to_vec_pretty(&declarations).unwrap(),
    );
    let manifest = serde_json::json!({
        "schema": "trust-cg.source-word-proof-data.v1",
        "scope": "test-only data from the checked original source/Core owner; no admission or native/provider permission",
        "caller": selection.caller.index(), "callee": selection.callee.index(),
        "caller_source": selection.caller_source, "callee_source": selection.callee_source,
        "environment_content_digest": digest.total,
        "environment_digest_is_diagnostic_only": true,
        "environment_digest_omissions": "mutable counters, lazy constant source, native reducer implementations and documented extension state; immutable kernel/compiler source identities remain required",
        "closure_scope": "syntactic root/type/value dependencies plus per-name kernel record digests, not an observed complete kernel read trace",
        "execution_samples_not_universal_physical_proof": true,
        "runtime_samples": samples.iter().map(|(input, output)| serde_json::json!({
            "input_hex": format!("{input:016x}"), "output_hex": format!("{output:016x}"),
        })).collect::<Vec<_>>(),
        "files": files,
    });
    std::fs::write(
        directory.join("manifest.json"),
        serde_json::to_vec_pretty(&manifest).unwrap(),
    )
    .unwrap();
    println!(
        "CORE_UNIVERSAL_SOURCE_WORD_EVIDENCE_DIR={}",
        directory.display()
    );
}

#[cfg(feature = "source-defined-call")]
#[test]
fn universal_original_source_word_entry_installs_once_and_accepts_runtime_arguments() {
    use cg::jit::entry_stack::OwnedEntryStack;
    let (module, target) = forwarding_source_with_leaf(true, true).unwrap();
    let conditional = fixture::qualified_plan(module, target)
        .compile_for_owned_peer_entry("entry")
        .unwrap();
    let selection = universal_source_selection(7);
    let checked = conditional
        .check_source_word_entry(&selection)
        .expect("original universal source/Core initializer, five steps, halt and argument codec");
    let (mut entry, _) = checked
        .install_owned_stack(
            OwnedEntryStack::allocate(65_536).unwrap(),
            manifest(1),
            cg::compile_service::CompileGeneration::new(1),
        )
        .unwrap();
    let mut checker = trust_ir_build::clean_kernel::TypeChecker::new(entry.source_environment());
    checker.set_allow_unsafe(false);
    checker.set_allow_partial(false);
    checker
        .check_type(entry.source_proof(), entry.source_judgment())
        .unwrap();
    checker
        .check_type(entry.argument_codec_proof(), entry.argument_codec_claim())
        .unwrap();
    assert!(matches!(
        checker.check_type(entry.source_proof(), &Expr::const_str("False")),
        Err(trust_ir_build::clean_kernel::KernelTypeError::TypeMismatch { .. })
    ));
    drop(checker);
    let mut samples = Vec::new();
    for value in [0, 1, 42, 1u64 << 63, u64::MAX, 0xdead_beef_0123_4567] {
        let actual = entry.invoke1_u64(value).unwrap();
        assert_eq!(actual, value.wrapping_add(7));
        samples.push((value, actual));
    }
    retain_source_word_proof_data(&entry, &selection, &samples);
    println!("CORE_UNIVERSAL_SOURCE_WORD_NATIVE=PASS proof_once=true runtime_arguments=6");
}

#[cfg(feature = "source-defined-call")]
#[test]
fn universal_source_word_owner_refuses_an_independent_wrong_source_body() {
    let (module, target) = forwarding_source_with_leaf(true, true).unwrap();
    let conditional = fixture::qualified_plan(module, target)
        .compile_for_owned_peer_entry("entry")
        .unwrap();
    let error = conditional
        .check_source_word_entry(&universal_source_selection(8))
        .unwrap_err();
    assert!(
        error
            .reason()
            .contains("source-call island differs from the replayed original binding"),
        "{error}"
    );
    assert_eq!(error.predecessor().source_function(), FuncId::new(1));
    assert_eq!(
        error
            .predecessor()
            .diagnostic_report()
            .genuinely_verified_count(),
        0
    );
}
