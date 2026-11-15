// rustc_codegen_trust_cg/compile_error_diag_tests.rs - layer codes per CompileError
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Trust-core architecture AD-8 / exit criterion E0.3: `classify_compile_error`
//! has no default arm, and a test per `CompileError` variant asserts the
//! diagnostic code of the layer that produced it.
//!
//! The old default arm filed every untyped error as `TCG-REGALLOC-063`; 80 of the
//! 97 REGALLOC-063 rows in the first valid Checkpoint A were EH-sidecar refusals
//! (`PipelineError::EhSidecarUnsupported`). `CompileError::Pipeline` wraps several
//! layers, so every `PipelineError` variant has its own test as well, and so do
//! the variants of the error types it carries (`LowerError`, `X86PipelineError`)
//! and of `JitError` (no longer `#[non_exhaustive]`).
//!
//! Each test builds the variant and checks its layer code. For arms without
//! typed fields it also checks that the fields are unchanged from the pre-E0.3
//! shape (`error` = the `Display` text): only the classification moved.
//!
//! Classifying by variant is honest only if each variant is raised by one
//! layer, so the `raise_site_*` tests drive REAL refusals through the codegen
//! crate's public API (not hand-built variants) and check the code they get.

use trust_cg_codegen::compiler::CompileError as CE;
use trust_cg_codegen::jit::JitError as JE;
use trust_cg_codegen::lower::LowerError as LE;
use trust_cg_codegen::pipeline::PipelineError as PE;
use trust_cg_codegen::target::{AArch64IsaProfile, Target, TargetSpec};
use trust_cg_codegen::x86_64::X86PipelineError as XE;
use trust_cg_verify::diag::DiagCode;

use super::classify_compile_error;

/// Assert `err`'s layer code, and that an untyped arm still carries exactly the
/// `error` field the old default arm produced.
fn assert_untyped(err: CE, expected: DiagCode) {
    let (code, fields) = classify_compile_error(&err);
    assert_eq!(code, expected, "wrong layer code for `{err}`");
    assert_eq!(
        fields,
        vec![("error", err.to_string())],
        "untyped arm fields changed for `{err}`"
    );
}

fn assert_pipeline(err: PE, expected: DiagCode) {
    assert_untyped(CE::Pipeline(err), expected);
}

fn assert_x86(err: XE, expected: DiagCode) {
    assert_untyped(CE::Pipeline(PE::X86(err)), expected);
}

fn assert_jit(err: JE, expected: DiagCode) {
    assert_untyped(CE::Jit(err), expected);
}

fn budget_error() -> trust_cg_codegen::env_lock::resource_budget::ResourceBudgetError {
    trust_cg_codegen::env_lock::resource_budget::ResourceBudgetError::NonUnicode {
        key: "TCG_TEST_BUDGET",
    }
}

/// A real `rayon::ThreadPoolBuildError` (its fields are private): a pool whose
/// spawn handler refuses to start a thread.
fn worker_pool_error() -> rayon::ThreadPoolBuildError {
    match rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .spawn_handler(|_thread| Err(std::io::Error::other("thread spawn refused")))
        .build()
    {
        Ok(_) => panic!("a refusing spawn handler must fail the pool build"),
        Err(error) => error,
    }
}

fn spec(triple: &str) -> TargetSpec {
    TargetSpec::parse(triple).expect("test target triple parses")
}

fn s(text: &str) -> String {
    text.to_owned()
}

// ---------------------------------------------------------------------------
// The measured default-arm population (first valid Checkpoint A, 97 rows)
// ---------------------------------------------------------------------------

#[test]
fn checkpoint_a_eh_sidecar_refusal_is_unwind_not_regalloc() {
    // The exact shape of the 80 rows: the relocation-inventory mirror refusing an
    // EH function (`module_relocation_inventory_report_with_object_state`).
    let err = CE::Pipeline(PE::EhSidecarUnsupported {
        function: s("_RNvCs0_4core3fmt"),
        api: "module_relocation_inventory_report",
        reason: s(
            "EH object emission adds compact-unwind/eh-frame/personality/LSDA \
             relocations that this inventory does not yet enumerate",
        ),
    });
    let (code, _) = classify_compile_error(&err);
    assert_eq!(code, DiagCode::Unwind);
    assert_eq!(code.as_str(), "TCG-EH-UNWIND");
    assert_ne!(code, DiagCode::Regalloc);
}

#[test]
fn checkpoint_a_adapter_ambiguous_symbol_is_ir_lowering_not_regalloc() {
    // The 6 "ambiguous lowered symbol name" rows: the trust-ir -> LIR adapter
    // refusing a module (`trust_cg_lower::adapter`), before any machine code.
    let err = CE::Adapter(trust_cg_lower::AdapterError::UnsupportedInstruction(s(
        "module contains ambiguous lowered symbol name \"_RNvCs0_4core3fmt\"; only compatible \
         bodyless External declarations may share a function/global symbol",
    )));
    let (code, _) = classify_compile_error(&err);
    assert_eq!(code, DiagCode::IrLowering);
    assert_eq!(code.as_str(), "TCG-IR-LOWER");
    assert_ne!(code, DiagCode::Regalloc);
}

#[test]
fn checkpoint_a_adapter_entry_parameter_type_mismatch_is_ir_lowering_not_regalloc() {
    // The 2 type-mismatch rows (`EntryParamTypeMismatch`, e.g. panic_unwind's
    // `Struct([I64, I64])` entry parameter against an `Array(I64, 2)` signature).
    let err = CE::Adapter(trust_cg_lower::AdapterError::EntryParamTypeMismatch(
        s("_RNvNtCs0_12panic_unwind3imp5panic"),
        0,
        trust_cg_lower::Type::I64,
        trust_cg_lower::Type::I32,
    ));
    let (code, _) = classify_compile_error(&err);
    assert_eq!(code, DiagCode::IrLowering);
    assert_ne!(code, DiagCode::Regalloc);
}

#[test]
fn checkpoint_a_regalloc_translation_validation_stays_regalloc() {
    // The 9 "spill-slot init" rows really are register-allocator refusals.
    let err = CE::Pipeline(PE::RegAlloc(s(
        "register allocation translation validation failed: spill-slot init",
    )));
    let (code, _) = classify_compile_error(&err);
    assert_eq!(code.as_str(), "TCG-REGALLOC-063");
}

// ---------------------------------------------------------------------------
// One test per CompileError variant
// ---------------------------------------------------------------------------

#[test]
fn compile_error_jit_identity_encoding_is_jit() {
    assert_untyped(
        CE::JitIdentityEncoding(
            trust_cg_codegen::jit_cert::JitIdentityEncodingError::FixupOffsetOverflow,
        ),
        DiagCode::Jit,
    );
}

#[test]
fn compile_error_resource_budget_is_driver() {
    assert_untyped(CE::ResourceBudget(budget_error()), DiagCode::Driver);
}

#[test]
fn compile_error_adapter_is_ir_lowering() {
    assert_untyped(
        CE::Adapter(trust_cg_lower::AdapterError::UnsupportedInstruction(s(
            "module contains ambiguous lowered symbol name",
        ))),
        DiagCode::IrLowering,
    );
}

#[test]
fn compile_error_aot_direct_module_function_binding_is_object() {
    assert_untyped(
        CE::AotDirectModuleFunctionBindingUnsupported {
            target: s("x86_64-unknown-linux-gnu"),
            call_count: 2,
        },
        DiagCode::Object,
    );
}

#[test]
fn compile_error_aot_static_function_identity_binding_is_object() {
    assert_untyped(
        CE::AotStaticFunctionIdentityBindingUnsupported {
            target: s("x86_64-unknown-linux-gnu"),
            candidate_count: 1,
        },
        DiagCode::Object,
    );
}

#[test]
fn compile_error_dialect_pipeline_is_ir_lowering() {
    assert_untyped(
        CE::DialectPipeline(
            trust_cg_codegen::dialect_pipeline::DialectPipelineError::Lowering(s(
                "fixpoint not reached",
            )),
        ),
        DiagCode::IrLowering,
    );
}

#[test]
fn compile_error_pipeline_classifies_inside_the_pipeline() {
    // The wrapper has no single layer: the same variant maps to many codes.
    assert_pipeline(PE::ISel(s("unsupported ABI")), DiagCode::Regalloc);
    assert_pipeline(PE::ElfReparse(s("section table")), DiagCode::Object);
    assert_pipeline(PE::DebugProvenance(s("declare var")), DiagCode::DebugInfo);
    assert_pipeline(PE::ModuleIo(s("JSON error")), DiagCode::Driver);
    assert_pipeline(
        PE::EhSidecarUnsupported {
            function: s("f"),
            api: "encode_function",
            reason: s("r"),
        },
        DiagCode::Unwind,
    );
    assert_pipeline(PE::FsymCoverageGap(s("deref")), DiagCode::Proof);
}

#[test]
fn pipeline_stack_limit_machine_refusal_preserves_its_layer_and_reason() {
    assert_pipeline(
        PE::StackLimit {
            function: s("requester"),
            reason: s("the limit parameter does not resolve to one X register"),
        },
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_stack_limit_proof_refusal_preserves_its_layer_and_reason() {
    assert_pipeline(
        PE::StackLimitNotProofQualified {
            function: s("requester"),
        },
        DiagCode::Proof,
    );
}

#[test]
fn compile_error_certified_pass_execution_failed_is_proof_with_typed_fields() {
    let err = CE::CertifiedPassExecutionFailed {
        pass_name: s("dce"),
        function_name: s("f"),
        detail: s("d"),
    };
    let (code, fields) = classify_compile_error(&err);
    assert_eq!(code, DiagCode::Proof);
    assert_eq!(
        fields,
        vec![
            ("pass_name", s("dce")),
            ("function_name", s("f")),
            ("detail", s("d"))
        ]
    );
}

#[test]
fn compile_error_certified_pass_chain_is_proof() {
    assert_untyped(
        CE::CertifiedPassChain(trust_cg_verify::CertifiedPassChainError::Empty),
        DiagCode::Proof,
    );
}

#[test]
fn compile_error_carrier_hygiene_is_carrier_with_typed_fields() {
    use trust_cg_verify::carrier_hygiene::{HighBits, RequiredExtension};
    let err = CE::CarrierHygiene {
        function_name: s("f"),
        block: 3,
        inst_index: 7,
        opcode: trust_cg_ir::x86_64_ops::X86Opcode::Nop,
        operand: trust_cg_ir::regs::VReg::new(9, trust_cg_ir::regs::RegClass::Gpr64),
        required: RequiredExtension::Sign,
        actual: HighBits::Top,
        detail: s("MISCOMPILE #51"),
    };
    let (code, fields) = classify_compile_error(&err);
    assert_eq!(code, DiagCode::Carrier);
    assert_eq!(fields[0], ("function_name", s("f")));
    assert_eq!(fields[1], ("block", s("3")));
    assert_eq!(fields[2], ("inst_index", s("7")));
}

#[test]
fn compile_error_pass_validation_rejected_is_pass_validator_with_typed_fields() {
    let err = CE::PassValidationRejected {
        pass_name: s("overflow"),
        obligation_name: s("o"),
        reason: s("r"),
    };
    let (code, fields) = classify_compile_error(&err);
    assert_eq!(code, DiagCode::PassValidator);
    assert_eq!(
        fields,
        vec![
            ("pass_name", s("overflow")),
            ("obligation_name", s("o")),
            ("reason", s("r"))
        ]
    );
}

#[test]
fn compile_error_compile_artifact_cache_is_driver() {
    assert_untyped(
        CE::CompileArtifactCache(std::io::Error::other("cache directory unwritable")),
        DiagCode::Driver,
    );
}

#[test]
fn compile_error_profile_use_cache_identity_is_driver() {
    assert_untyped(
        CE::ProfileUseCacheIdentity(trust_cg_opt::pgo::ProfDataError::LegacyJsonUnsupported),
        DiagCode::Driver,
    );
}

#[test]
fn compile_error_compile_artifact_cache_identity_json_is_driver() {
    let source = serde_json::from_str::<u8>("not json").expect_err("invalid JSON is rejected");
    assert_untyped(
        CE::CompileArtifactCacheIdentityJson {
            component: "policy",
            source,
        },
        DiagCode::Driver,
    );
}

#[test]
fn compile_error_empty_module_is_driver() {
    assert_untyped(CE::EmptyModule, DiagCode::Driver);
}

#[test]
fn compile_error_dispatcher_empty_module_is_driver() {
    assert_untyped(
        CE::DispatcherEmptyModule {
            dispatcher: "x86_64",
        },
        DiagCode::Driver,
    );
    assert_untyped(
        CE::DispatcherEmptyModule {
            dispatcher: "RISC-V",
        },
        DiagCode::Driver,
    );
}

#[test]
fn compile_error_aarch64_frame_pointers_unsupported_is_driver() {
    assert_untyped(
        CE::Aarch64FramePointersUnsupported {
            target: s("x86_64-unknown-linux-gnu"),
            reason: "the explicit frame policy is modeled only for AArch64 objects",
        },
        DiagCode::Driver,
    );
}

#[test]
fn compile_error_profile_generate_target_unsupported_is_driver() {
    assert_untyped(
        CE::ProfileGenerateTargetUnsupported {
            target: Target::X86_64,
        },
        DiagCode::Driver,
    );
}

#[test]
fn compile_error_proof_lane_lir_incomplete_is_proof() {
    assert_untyped(
        CE::ProofLaneLirIncomplete {
            retained: 1,
            required: 2,
        },
        DiagCode::Proof,
    );
}

#[test]
fn compile_error_ir_inline_is_ir_lowering() {
    assert_untyped(
        CE::IrInline {
            detail: s("opcode multiset diverged"),
        },
        DiagCode::IrLowering,
    );
}

#[test]
fn compile_error_jit_classifies_inside_the_jit_error() {
    // The wrapper has no single layer; see the per-`JitError`-variant tests.
    assert_untyped(CE::Jit(JE::UnresolvedSymbol(s("memcpy"))), DiagCode::Jit);
    assert_untyped(
        CE::Jit(JE::Pipeline(PE::EhSidecarUnsupported {
            function: s("f"),
            api: "jit",
            reason: s("r"),
        })),
        DiagCode::Unwind,
    );
    assert_untyped(
        CE::Jit(JE::ResourceBudget(budget_error())),
        DiagCode::Driver,
    );
}

#[test]
fn compile_error_host_jit_selected_codegen_features_missing_is_jit() {
    assert_untyped(CE::HostJitSelectedCodegenFeaturesMissing, DiagCode::Jit);
}

#[test]
fn compile_error_host_jit_selected_codegen_features_pipeline_mismatch_is_jit() {
    assert_untyped(
        CE::HostJitSelectedCodegenFeaturesPipelineMismatch {
            function_name: s("f"),
            expected: s("sse2"),
            actual: s("avx2"),
        },
        DiagCode::Jit,
    );
}

#[test]
fn compile_error_host_jit_selected_codegen_features_non_uniform_is_jit() {
    assert_untyped(
        CE::HostJitSelectedCodegenFeaturesNonUniform {
            reference_function: s("f"),
            reference_features: s("sse2"),
            function_name: s("g"),
            actual_features: s("avx2"),
        },
        DiagCode::Jit,
    );
}

#[test]
fn compile_error_host_jit_selected_codegen_profile_is_jit() {
    use trust_cg_codegen::jit_contract::HostJitSelectedCodegenProfileError as ProfileError;
    assert_untyped(
        CE::HostJitSelectedCodegenProfile(ProfileError::DetectedSelectionMismatch {
            selected_codegen_features: vec![s("avx2")],
            detected_codegen_features: vec![],
        }),
        DiagCode::Jit,
    );
}

#[test]
fn compile_error_aarch64_machine_code_evidence_missing_is_jit() {
    assert_untyped(
        CE::Aarch64MachineCodeEvidenceMissing {
            function_name: s("<module>"),
        },
        DiagCode::Jit,
    );
}

#[test]
fn compile_error_aarch64_machine_code_evidence_pipeline_mismatch_is_jit() {
    assert_untyped(
        CE::Aarch64MachineCodeEvidencePipelineMismatch {
            function_name: s("f"),
            expected_target: spec("aarch64-apple-darwin"),
            actual_target: spec("aarch64-unknown-linux-gnu"),
            expected_admitted: AArch64IsaProfile::default(),
            actual_admitted: AArch64IsaProfile::default(),
        },
        DiagCode::Jit,
    );
}

#[test]
fn compile_error_aarch64_machine_code_evidence_invalid_is_jit() {
    assert_untyped(
        CE::Aarch64MachineCodeEvidenceInvalid {
            detail: s("nonuniform"),
        },
        DiagCode::Jit,
    );
}

#[test]
fn compile_error_jit_target_mismatch_is_jit() {
    assert_untyped(
        CE::JitTargetMismatch {
            target: Target::Aarch64,
            host: Target::X86_64,
        },
        DiagCode::Jit,
    );
}

#[test]
fn compile_error_jit_target_spec_mismatch_is_jit() {
    assert_untyped(
        CE::JitTargetSpecMismatch {
            requested: spec("aarch64-unknown-linux-gnu"),
            host: spec("aarch64-apple-darwin"),
        },
        DiagCode::Jit,
    );
}

#[test]
fn compile_error_jit_target_unsupported_is_jit() {
    assert_untyped(
        CE::JitTargetUnsupported {
            target: Target::Riscv64,
        },
        DiagCode::Jit,
    );
}

#[test]
fn compile_error_prebuilt_ir_target_unsupported_is_driver() {
    assert_untyped(
        CE::PrebuiltIrTargetUnsupported {
            target: Target::X86_64,
        },
        DiagCode::Driver,
    );
}

#[test]
fn compile_error_proofs_unsupported_for_target_is_proof_with_typed_fields() {
    let err = CE::ProofsUnsupportedForTarget {
        target: Target::Riscv64,
    };
    let (code, fields) = classify_compile_error(&err);
    assert_eq!(code, DiagCode::Proof);
    assert_eq!(fields, vec![("target", format!("{:?}", Target::Riscv64))]);
}

#[test]
fn compile_error_composed_transition_refused_is_proof_with_typed_fields() {
    let refusal = trust_cg_verify::composed_transition::CompositionRefusal::MissingLink {
        function: s("f"),
        stage: trust_cg_verify::composed_transition::LinkStage::PostAllocation,
    };
    let reason = refusal.to_string();
    let err = CE::ComposedTransitionRefused {
        target: Target::Aarch64,
        refusal: Box::new(refusal),
    };
    let (code, fields) = classify_compile_error(&err);
    assert_eq!(code, DiagCode::Proof);
    assert_eq!(
        fields,
        vec![
            ("target", format!("{:?}", Target::Aarch64)),
            ("refusal", s("missing-link")),
            ("reason", reason)
        ]
    );
}

#[test]
fn compile_error_proof_promotion_rejected_is_proof_with_typed_fields() {
    let err = CE::ProofPromotionRejected {
        target: Target::Aarch64,
        reason: s("StpPreIndex"),
    };
    let (code, fields) = classify_compile_error(&err);
    assert_eq!(code, DiagCode::Proof);
    assert_eq!(code.as_str(), "TCG-PROOF-465");
    assert_eq!(
        fields,
        vec![
            ("target", format!("{:?}", Target::Aarch64)),
            ("reason", s("StpPreIndex"))
        ]
    );
}

#[test]
fn compile_error_exception_tables_unproved_is_proof_with_typed_fields() {
    let err = CE::ExceptionTablesUnproved {
        target: Target::X86_64,
        function: s("tp_pass_through"),
        walk_through: true,
    };
    let (code, fields) = classify_compile_error(&err);
    assert_eq!(code, DiagCode::Proof);
    assert_eq!(code.as_str(), "TCG-PROOF-465");
    assert_eq!(
        fields,
        vec![
            ("target", format!("{:?}", Target::X86_64)),
            ("function_name", s("tp_pass_through")),
            ("reason", s("exception_tables_unproved")),
            ("walk_through", s("true"))
        ]
    );
    assert!(
        err.to_string()
            .contains("[TCG-EH-UNPROVED] proof promotion rejected")
            && err.to_string().contains("walk-through exception tables")
    );
}

#[test]
fn compile_error_jit_uncertified_bytes_require_opt_in_is_jit() {
    assert_untyped(
        CE::JitUncertifiedBytesRequireOptIn {
            target: Target::X86_64,
        },
        DiagCode::Jit,
    );
}

#[test]
fn compile_error_x86_aot_object_format_unsupported_is_object() {
    assert_untyped(
        CE::X86AotObjectFormatUnsupported {
            target_os: "windows",
            required_format: "COFF",
            context: "test",
        },
        DiagCode::Object,
    );
}

// ---------------------------------------------------------------------------
// One test per PipelineError variant (the wrapper spans several layers)
// ---------------------------------------------------------------------------

#[test]
fn pipeline_aot_profile_is_regalloc() {
    assert_pipeline(
        PE::AotProfile(trust_cg_codegen::AotProfileError::InstructionIdExhausted {
            function: s("f"),
        }),
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_frame_index_elimination_is_regalloc() {
    assert_pipeline(
        PE::FrameIndexElimination(
            trust_cg_codegen::frame::FrameIndexEliminationError::RuntimeSizedSlot { slot: 1 },
        ),
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_frame_lowering_is_regalloc_unless_it_refuses_an_eh_sidecar() {
    assert_pipeline(
        PE::FrameLowering(LE::FrameLowering(s("overflow"))),
        DiagCode::Regalloc,
    );
    assert_pipeline(
        PE::FrameLowering(LE::UnsupportedInstruction(s("i"))),
        DiagCode::Regalloc,
    );
    assert_pipeline(
        PE::FrameLowering(LE::EncodingFailed(s("e"))),
        DiagCode::Regalloc,
    );
    assert_pipeline(
        PE::FrameLowering(LE::MalformedFunction(s("m"))),
        DiagCode::Regalloc,
    );
    assert_pipeline(
        PE::FrameLowering(LE::RelaxationFailed(
            trust_cg_codegen::relax::RelaxError::MalformedFunction(s("m")),
        )),
        DiagCode::Regalloc,
    );
    assert_pipeline(
        PE::FrameLowering(LE::MissingOperand {
            opcode: trust_cg_lower::isel::AArch64Opcode::Nop,
            index: 0,
        }),
        DiagCode::Regalloc,
    );
    assert_pipeline(
        PE::FrameLowering(LE::UnresolvedPseudo(
            trust_cg_lower::isel::AArch64Opcode::Nop,
        )),
        DiagCode::Regalloc,
    );
    assert_pipeline(
        PE::FrameLowering(LE::EhSidecarUnsupported {
            function: s("f"),
            api: "lower_function",
        }),
        DiagCode::Unwind,
    );
}

#[test]
fn pipeline_resource_budget_is_driver() {
    assert_pipeline(PE::ResourceBudget(budget_error()), DiagCode::Driver);
}

#[test]
fn pipeline_isel_is_regalloc() {
    assert_pipeline(PE::ISel(s("unsupported ABI")), DiagCode::Regalloc);
}

#[test]
fn pipeline_affine_lowering_rejected_is_regalloc() {
    use trust_cg_verify::aarch64_affine_lowering::TrustIrAffineLoweringError;
    assert_pipeline(
        PE::AffineLoweringRejected {
            function: s("f"),
            reason: TrustIrAffineLoweringError::TrustIrLirMismatch,
        },
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_regalloc_is_regalloc() {
    assert_pipeline(PE::RegAlloc(s("spill-slot init")), DiagCode::Regalloc);
}

#[test]
fn pipeline_optimization_invariant_violation_is_regalloc() {
    assert_pipeline(
        PE::OptimizationInvariantViolation {
            function: s("f"),
            detail: s("d"),
        },
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_mach_id_admission_is_regalloc() {
    assert_pipeline(
        PE::MachIdAdmission(trust_cg_ir::MachIdRefusal {
            function: s("f"),
            boundary: s("entry of pass `dce`"),
            error: trust_cg_ir::MachIdAdmissionError::StaleCounter {
                domain: trust_cg_ir::MachIdDomain::VReg,
                counter: 1,
                live_id: 1,
                site: trust_cg_ir::MachIdSite::NoaliasParam { index: 0 },
            },
        }),
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_pass_validation_failed_is_regalloc() {
    assert_pipeline(
        PE::PassValidationFailed {
            function: s("f"),
            pass: s("pressure-aware-scheduler"),
            validator: "dependence-preservation",
            verdict: "refuted",
            reason: s("memory dependence reversed"),
        },
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_cegis_incomplete_is_regalloc() {
    assert_pipeline(
        PE::CegisIncomplete {
            function: s("f"),
            completion: trust_cg_verify::CegisSearchCompletion::DeadlineExceeded,
            ay_refusal: None,
        },
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_encoding_is_regalloc() {
    assert_pipeline(PE::Encoding(s("imm out of range")), DiagCode::Regalloc);
}

#[test]
fn pipeline_object_emission_is_object() {
    assert_pipeline(
        PE::ObjectEmission(s("AArch64 object contains duplicate global symbol `G`")),
        DiagCode::Object,
    );
}

#[test]
fn pipeline_unwind_is_unwind() {
    assert_pipeline(
        PE::Unwind(s(
            "module unwind emission: EH function `f` has no LSDA symbol",
        )),
        DiagCode::Unwind,
    );
}

#[test]
fn pipeline_malformed_aarch64_eh_is_unwind() {
    assert_pipeline(
        PE::MalformedAarch64Eh {
            function: s("f"),
            detail: s("invalid resolved exception table"),
        },
        DiagCode::Unwind,
    );
}

#[test]
fn pipeline_dwarf_emission_is_debug_info() {
    assert_pipeline(
        PE::DwarfEmit(trust_cg_codegen::dwarf_info::DwarfEmitError::DebugLocTooLarge),
        DiagCode::DebugInfo,
    );
}

#[test]
fn pipeline_module_io_is_driver() {
    assert_pipeline(
        PE::ModuleIo(s("unsupported tMBC version: 2")),
        DiagCode::Driver,
    );
}

#[test]
fn pipeline_producer_omitted_body_gate_is_driver() {
    assert_pipeline(
        PE::ProducerOmittedBodyGate {
            function: s("f"),
            wire_version: 41,
        },
        DiagCode::Driver,
    );
}

#[test]
fn pipeline_worker_pool_is_driver() {
    assert_pipeline(PE::WorkerPool(worker_pool_error()), DiagCode::Driver);
}

#[test]
fn pipeline_x86_classifies_inside_the_x86_error() {
    // The wrapper has no single layer; see the per-`X86PipelineError`-variant
    // tests below.
    assert_pipeline(PE::X86(XE::ISel(s("i"))), DiagCode::Regalloc);
    assert_pipeline(PE::X86(XE::Coff(coff_error())), DiagCode::Object);
    assert_pipeline(
        PE::X86(XE::WindowsCoffUnwindMetadataRequired {
            function: s("f"),
            reason: s("r"),
        }),
        DiagCode::Unwind,
    );
}

#[test]
fn pipeline_elf_reparse_is_object() {
    assert_pipeline(PE::ElfReparse(s("section table")), DiagCode::Object);
}

#[test]
fn pipeline_relocation_inventory_digest_is_object() {
    assert_pipeline(PE::RelocationInventoryDigest(s("digest")), DiagCode::Object);
}

#[test]
fn pipeline_unsupported_opcode_is_regalloc() {
    assert_pipeline(
        PE::UnsupportedOpcode(trust_cg_lower::isel::AArch64Opcode::Nop),
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_relaxation_is_regalloc() {
    assert_pipeline(
        PE::Relaxation(trust_cg_codegen::relax::RelaxError::MalformedFunction(s(
            "m",
        ))),
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_invalid_operand_is_regalloc() {
    assert_pipeline(PE::InvalidOperand(s("operand")), DiagCode::Regalloc);
}

#[test]
fn pipeline_aarch64_formal_arg_copy_hazard_is_regalloc() {
    assert_pipeline(PE::Aarch64FormalArgCopyHazard(s("x0")), DiagCode::Regalloc);
}

#[test]
fn pipeline_aarch64_call_arg_repair_is_regalloc() {
    assert_pipeline(PE::Aarch64CallArgRepair(s("x1")), DiagCode::Regalloc);
}

#[test]
fn pipeline_aarch64_lse_not_admitted_is_regalloc() {
    assert_pipeline(
        PE::Aarch64LseNotAdmitted {
            function: s("f"),
            opcode: trust_cg_lower::isel::AArch64Opcode::Nop,
            profile: s("baseline"),
        },
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_aarch64_lse2_not_admitted_is_regalloc() {
    assert_pipeline(
        PE::Aarch64Lse2NotAdmitted {
            function: s("f"),
            opcode: trust_cg_lower::isel::AArch64Opcode::Nop,
            profile: s("baseline"),
        },
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_aarch64_dotprod_not_admitted_is_regalloc() {
    assert_pipeline(
        PE::Aarch64DotProdNotAdmitted {
            function: s("f"),
            opcode: trust_cg_lower::isel::AArch64Opcode::Nop,
            profile: s("baseline"),
        },
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_aarch64_fp16_not_admitted_is_regalloc() {
    assert_pipeline(
        PE::Aarch64Fp16NotAdmitted {
            function: s("f"),
            opcode: trust_cg_lower::isel::AArch64Opcode::Nop,
            profile: s("baseline"),
        },
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_aarch64_feature_not_admitted_is_regalloc() {
    assert_pipeline(
        PE::Aarch64FeatureNotAdmitted {
            function: s("f"),
            opcode: trust_cg_lower::isel::AArch64Opcode::Crc32Cx,
            feature: "crc",
            profile: s("baseline"),
        },
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_aarch64_function_target_feature_is_regalloc() {
    assert_pipeline(
        PE::Aarch64FunctionTargetFeature {
            function: s("f"),
            feature: s("sve"),
            reason: s("not an AArch64 target feature this backend models"),
        },
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_aarch64_target_machine_contract_is_regalloc() {
    assert_pipeline(
        PE::Aarch64TargetMachineContract {
            function: s("f"),
            detail: s("d"),
        },
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_malformed_aarch64_function_is_regalloc() {
    assert_pipeline(
        PE::MalformedAarch64Function {
            function: s("f"),
            detail: s("d"),
        },
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_aarch64_object_field_too_large_is_object() {
    assert_pipeline(
        PE::Aarch64ObjectFieldTooLarge {
            function: s("f"),
            field: "combined code byte length",
            value: u128::from(u32::MAX) + 1,
            max: u128::from(u32::MAX),
        },
        DiagCode::Object,
    );
}

#[test]
fn pipeline_debug_provenance_is_debug_info() {
    assert_pipeline(PE::DebugProvenance(s("declare var")), DiagCode::DebugInfo);
}

#[test]
fn pipeline_guard_kernel_recheck_rejected_is_proof() {
    assert_pipeline(PE::GuardKernelRecheckRejected(s("in `f`")), DiagCode::Proof);
}

#[test]
fn pipeline_isa_guard_kernel_recheck_rejected_is_proof() {
    // The x86-64 and RISC-V dispatchers' guard re-check refusal: the same
    // verifier-backed gate as the AArch64 variant above, carried with its ISA.
    assert_pipeline(
        PE::IsaGuardKernelRecheckRejected {
            isa: "x86",
            function: s("f"),
            reason: s("r"),
        },
        DiagCode::Proof,
    );
}

#[test]
fn pipeline_target_object_unsupported_is_object() {
    assert_pipeline(
        PE::TargetObjectUnsupported {
            target: s("aarch64"),
            format: s("COFF"),
            reason: s("r"),
        },
        DiagCode::Object,
    );
}

#[test]
fn pipeline_eh_sidecar_unsupported_is_unwind() {
    assert_pipeline(
        PE::EhSidecarUnsupported {
            function: s("f"),
            api: "module_relocation_inventory_report",
            reason: s("r"),
        },
        DiagCode::Unwind,
    );
}

#[test]
fn pipeline_object_relocation_inventory_incomplete_is_object() {
    assert_pipeline(
        PE::ObjectRelocationInventoryIncomplete {
            object: s("cgu.o"),
            reason: s("r"),
        },
        DiagCode::Object,
    );
}

#[test]
fn pipeline_dispatch_verification_failed_is_compute_dispatch() {
    let report = trust_cg_lower::VerificationReport {
        cpu_fallback_ok: false,
        missing_cpu_fallback: Vec::new(),
        data_transfers_ok: true,
        data_transfer_errors: Vec::new(),
        synchronization_ok: true,
        synchronization_errors: Vec::new(),
        dependency_order_ok: true,
        dependency_errors: Vec::new(),
        profitability_ok: true,
        profitability_mismatches: Vec::new(),
    };
    assert_pipeline(
        PE::DispatchVerificationFailed {
            violations: 1,
            summary: s("cpu fallback"),
            report,
        },
        DiagCode::ComputeDispatch,
    );
}

#[test]
fn pipeline_coreml_emit_is_compute_dispatch() {
    assert_pipeline(
        PE::CoreMLEmit(trust_cg_codegen::coreml_emitter::CoreMLEmitError::EmptyNodeList),
        DiagCode::ComputeDispatch,
    );
}

#[test]
fn pipeline_metal_emit_is_compute_dispatch() {
    assert_pipeline(
        PE::MetalEmit(
            trust_cg_codegen::metal_emitter::MetalEmitError::InvalidDispatchPlan { reason: s("r") },
        ),
        DiagCode::ComputeDispatch,
    );
}

#[test]
fn pipeline_fixup_is_object() {
    assert_pipeline(
        PE::Fixup(trust_cg_codegen::macho::fixup::FixupError::UnresolvedSymbol { name: s("_f") }),
        DiagCode::Object,
    );
}

#[test]
fn pipeline_macho_relocation_is_object() {
    assert_pipeline(
        PE::MachORelocation(
            trust_cg_codegen::macho::reloc::MachORelocationError::LengthOutOfRange { length: 4 },
        ),
        DiagCode::Object,
    );
}

#[test]
fn pipeline_macho_write_is_object() {
    assert_pipeline(
        PE::MachOWrite(
            trust_cg_codegen::macho::writer::MachOWriteError::FieldOutOfRange {
                field: "ncmds",
                value: 1 << 40,
                max: u128::from(u32::MAX),
            },
        ),
        DiagCode::Object,
    );
}

#[test]
fn pipeline_compact_unwind_is_unwind() {
    assert_pipeline(
        PE::CompactUnwind(
            trust_cg_codegen::unwind::CompactUnwindError::MachORelocation(
                trust_cg_codegen::macho::reloc::MachORelocationError::LengthOutOfRange {
                    length: 4,
                },
            ),
        ),
        DiagCode::Unwind,
    );
}

#[test]
fn pipeline_sampled_verify_unavailable_is_proof() {
    assert_pipeline(
        PE::SampledVerifyUnavailable { function: s("f") },
        DiagCode::Proof,
    );
}

#[test]
fn pipeline_verification_failed_is_proof() {
    assert_pipeline(
        PE::VerificationFailed {
            function: s("f"),
            failures: 1,
            coverage: 50.0,
            report: trust_cg_verify::FunctionVerificationReport {
                function_name: s("f"),
                precondition_failure: None,
                instructions: Vec::new(),
            },
        },
        DiagCode::Proof,
    );
}

#[test]
fn pipeline_fsym_coverage_gap_is_proof() {
    assert_pipeline(
        PE::FsymCoverageGap(s("deref obligation dropped")),
        DiagCode::Proof,
    );
}

fn coff_error() -> trust_cg_codegen::coff::CoffError {
    trust_cg_codegen::coff::CoffError::SectionCountOverflow {
        count: 1 << 17,
        max: 1 << 16,
    }
}

// ---------------------------------------------------------------------------
// One test per X86PipelineError variant (carried typed by PipelineError::X86)
// ---------------------------------------------------------------------------

#[test]
fn x86_resource_budget_is_driver() {
    assert_x86(XE::ResourceBudget(budget_error()), DiagCode::Driver);
}

#[test]
fn x86_isel_is_regalloc() {
    assert_x86(
        XE::ISel(s("Popcnt requires GPR destination")),
        DiagCode::Regalloc,
    );
}

#[test]
fn x86_regalloc_is_regalloc() {
    assert_x86(
        XE::RegAlloc(s("ran out of GPR registers")),
        DiagCode::Regalloc,
    );
}

#[test]
fn x86_regalloc_rematerialization_replay_unsupported_is_regalloc() {
    assert_x86(
        XE::RegAllocRematerializationReplayUnsupported { opcode: 7 },
        DiagCode::Regalloc,
    );
}

#[test]
fn x86_unsupported_target_feature_is_regalloc() {
    assert_x86(
        XE::UnsupportedTargetFeature {
            opcode: trust_cg_ir::x86_64_ops::X86Opcode::Nop,
            feature: trust_cg_codegen::x86_64::X86TargetFeature::Popcnt,
        },
        DiagCode::Regalloc,
    );
}

#[test]
fn x86_constant_pool_is_regalloc() {
    assert_x86(
        XE::ConstantPool(s("entry 3 has unsupported data length 2")),
        DiagCode::Regalloc,
    );
}

#[test]
fn x86_encoding_is_regalloc() {
    assert_x86(
        XE::Encoding(trust_cg_codegen::x86_64::X86EncodeError::InvalidOperands(
            s("r8"),
        )),
        DiagCode::Regalloc,
    );
}

#[test]
fn x86_frame_lowering_is_regalloc() {
    assert_x86(
        XE::FrameLowering(s("x86-64 frame size overflow")),
        DiagCode::Regalloc,
    );
}

#[test]
fn x86_malformed_function_is_regalloc() {
    assert_x86(
        XE::MalformedFunction {
            function: s("f"),
            detail: s("block_order duplicates block"),
        },
        DiagCode::Regalloc,
    );
}

#[test]
fn x86_decode_check_is_regalloc() {
    assert_x86(
        XE::DecodeCheck(s("bytes decode to a different opcode")),
        DiagCode::Regalloc,
    );
}

#[test]
fn x86_windows_coff_unwind_metadata_required_is_unwind() {
    assert_x86(
        XE::WindowsCoffUnwindMetadataRequired {
            function: s("f"),
            reason: s("dynamic stack allocation with XMM saves"),
        },
        DiagCode::Unwind,
    );
}

#[test]
fn x86_coff_undefined_external_call_is_object() {
    assert_x86(
        XE::CoffUndefinedExternalCall {
            caller: s("f"),
            callee: s("g"),
        },
        DiagCode::Object,
    );
}

#[test]
fn x86_symbolic_direct_call_requires_relocation_emission_is_object() {
    assert_x86(
        XE::SymbolicDirectCallRequiresRelocationEmission {
            function: s("f"),
            callee: s("g"),
            format: trust_cg_codegen::x86_64::X86OutputFormat::Elf,
        },
        DiagCode::Object,
    );
}

#[test]
fn x86_eh_output_unsupported_is_unwind() {
    assert_x86(
        XE::EhOutputUnsupported {
            function: s("f"),
            format: trust_cg_codegen::x86_64::X86OutputFormat::Coff,
            reason: s("r"),
        },
        DiagCode::Unwind,
    );
}

#[test]
fn x86_invalid_eh_personality_is_unwind() {
    assert_x86(
        XE::InvalidEhPersonality {
            function: s("f"),
            reason: s("empty"),
        },
        DiagCode::Unwind,
    );
}

#[test]
fn x86_object_field_too_large_is_object() {
    assert_x86(
        XE::ObjectFieldTooLarge {
            function: s("f"),
            field: "COFF unwind-info length",
            value: u128::from(u32::MAX) + 1,
            max: u128::from(u32::MAX),
        },
        DiagCode::Object,
    );
}

#[test]
fn x86_global_ref_unsupported_is_object() {
    assert_x86(
        XE::GlobalRefUnsupported {
            function: s("f"),
            symbol: s("G"),
            reason: s("thread-local globals are not supported"),
        },
        DiagCode::Object,
    );
}

#[test]
fn x86_extern_ref_unsupported_is_object() {
    assert_x86(
        XE::ExternRefUnsupported {
            function: s("f"),
            symbol: s("E"),
            reason: s("r"),
        },
        DiagCode::Object,
    );
}

#[test]
fn x86_coff_is_object() {
    assert_x86(XE::Coff(coff_error()), DiagCode::Object);
}

#[test]
fn x86_macho_relocation_is_object() {
    assert_x86(
        XE::MachORelocation(
            trust_cg_codegen::macho::reloc::MachORelocationError::LengthOutOfRange { length: 4 },
        ),
        DiagCode::Object,
    );
}

#[test]
fn x86_macho_write_is_object() {
    assert_x86(
        XE::MachOWrite(
            trust_cg_codegen::macho::writer::MachOWriteError::FieldOutOfRange {
                field: "ncmds",
                value: 1 << 40,
                max: u128::from(u32::MAX),
            },
        ),
        DiagCode::Object,
    );
}

#[test]
fn x86_elf_reparse_is_object() {
    assert_x86(XE::ElfReparse(s("section table")), DiagCode::Object);
}

#[test]
fn x86_object_emission_is_object() {
    assert_x86(
        XE::ObjectEmission(s("COFF constant-pool relocation offset overflow")),
        DiagCode::Object,
    );
}

#[test]
fn x86_unwind_is_unwind() {
    assert_x86(
        XE::Unwind(s("COFF unwind .xdata size overflow")),
        DiagCode::Unwind,
    );
}

#[test]
fn x86_malformed_eh_is_unwind() {
    assert_x86(
        XE::MalformedEh {
            function: s("f"),
            detail: s("invalid x86 EH metadata/layout"),
        },
        DiagCode::Unwind,
    );
}

#[test]
fn x86_block_profiling_is_jit() {
    assert_x86(
        XE::BlockProfiling(s("x86 block profiling: empty block order")),
        DiagCode::Jit,
    );
    // The two refusals round 2 found still filed elsewhere: a rel32 patch
    // during block-profile branch retargeting (was `ConstantPool`) and the
    // Windows JIT block-counter configuration refusal (was `RegAlloc`).
    assert_x86(
        XE::BlockProfiling(s(
            "x86 block profiling: rel32 patch site 2 outside code length 4",
        )),
        DiagCode::Jit,
    );
    assert_x86(
        XE::BlockProfiling(s(
            "Windows x86_64 JIT block counters require full regalloc: the stack-neutral \
             counter trampoline uses R10, and simplified regalloc may allocate R10",
        )),
        DiagCode::Jit,
    );
}

#[test]
fn x86_worker_pool_is_driver() {
    assert_x86(XE::WorkerPool(worker_pool_error()), DiagCode::Driver);
}

// ---------------------------------------------------------------------------
// One test per JitError variant (no longer `#[non_exhaustive]`)
// ---------------------------------------------------------------------------

#[test]
fn jit_identity_encoding_is_jit() {
    assert_jit(
        JE::IdentityEncoding(
            trust_cg_codegen::jit_cert::JitIdentityEncodingError::FixupOffsetOverflow,
        ),
        DiagCode::Jit,
    );
}

#[test]
fn jit_lir_source_count_mismatch_is_jit() {
    assert_jit(
        JE::LirSourceCountMismatch { machine: 1, lir: 2 },
        DiagCode::Jit,
    );
}

#[test]
fn jit_lir_source_pair_mismatch_is_jit() {
    assert_jit(
        JE::LirSourcePairMismatch {
            ordinal: 0,
            machine: s("f"),
            lir: s("g"),
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_resource_budget_is_driver() {
    assert_jit(JE::ResourceBudget(budget_error()), DiagCode::Driver);
}

#[test]
fn jit_pipeline_keeps_the_pipeline_layer() {
    assert_jit(JE::Pipeline(PE::RegAlloc(s("r"))), DiagCode::Regalloc);
    assert_jit(JE::Pipeline(PE::Unwind(s("u"))), DiagCode::Unwind);
    assert_jit(JE::Pipeline(PE::ObjectEmission(s("o"))), DiagCode::Object);
    assert_jit(
        JE::Pipeline(PE::X86(XE::BlockProfiling(s("b")))),
        DiagCode::Jit,
    );
}

#[test]
fn jit_block_profile_splice_is_jit() {
    assert_jit(
        JE::BlockProfileSplice(s("block-splice: empty block_order")),
        DiagCode::Jit,
    );
}

#[test]
fn jit_unresolved_symbol_is_jit() {
    assert_jit(JE::UnresolvedSymbol(s("memcpy")), DiagCode::Jit);
}

#[test]
fn jit_unsupported_host_is_jit() {
    assert_jit(
        JE::UnsupportedHost {
            arch: "riscv64",
            os: "linux",
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_memory_alloc_is_jit() {
    assert_jit(
        JE::MemoryAlloc(std::io::Error::other("mmap")),
        DiagCode::Jit,
    );
}

#[test]
fn jit_memory_protect_is_jit() {
    assert_jit(
        JE::MemoryProtect(std::io::Error::other("mprotect")),
        DiagCode::Jit,
    );
}

#[test]
fn jit_raw_jit_eh_unsupported_is_unwind() {
    assert_jit(
        JE::RawJitEhUnsupported { function: s("f") },
        DiagCode::Unwind,
    );
}

#[test]
fn jit_raw_jit_target_mismatch_is_jit() {
    assert_jit(
        JE::RawJitTargetMismatch {
            function: s("f"),
            host_arch: "x86_64",
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_raw_jit_isa_extension_not_admitted_is_jit() {
    assert_jit(
        JE::RawJitIsaExtensionNotAdmitted {
            function: s("f"),
            opcode: trust_cg_ir::inst::AArch64Opcode::Nop,
            required_feature: "lse",
            host_profile: s("baseline"),
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_raw_jit_function_feature_unsupported_by_host_is_jit() {
    assert_jit(
        JE::RawJitFunctionFeatureUnsupportedByHost {
            function: s("f"),
            feature: "crc",
            host_features: vec!["lse"],
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_serialized_buffer_feature_unsupported_by_host_is_jit() {
    assert_jit(
        JE::SerializedBufferFeatureUnsupportedByHost {
            feature: "crc",
            host_features: vec!["lse"],
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_serialized_buffer_target_mismatch_is_jit() {
    assert_jit(
        JE::SerializedBufferTargetMismatch {
            serialized_target: s("a"),
            host_target: s("b"),
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_windows_unwind_unsupported_is_unwind() {
    assert_jit(
        JE::WindowsUnwindUnsupported {
            function: s("f"),
            reason: s("r"),
        },
        DiagCode::Unwind,
    );
}

#[test]
fn jit_windows_unwind_range_invalid_is_unwind() {
    assert_jit(
        JE::WindowsUnwindRangeInvalid {
            function: s("f"),
            begin_offset: 0,
            end_offset: 8,
            code_len: 4,
        },
        DiagCode::Unwind,
    );
}

#[test]
fn jit_windows_unwind_registration_failed_is_unwind() {
    assert_jit(
        JE::WindowsUnwindRegistrationFailed { function_count: 1 },
        DiagCode::Unwind,
    );
}

#[test]
fn jit_empty_executable_buffer_is_jit() {
    assert_jit(
        JE::EmptyExecutableBuffer { function_count: 1 },
        DiagCode::Jit,
    );
}

#[test]
fn jit_invalid_function_range_is_jit() {
    assert_jit(
        JE::InvalidFunctionRange {
            function: s("f"),
            start: 8,
            end: 4,
            code_len: 16,
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_validation_range_count_mismatch_is_jit() {
    assert_jit(
        JE::ValidationRangeCountMismatch {
            validation_count: 1,
            range_count: 2,
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_validation_function_name_mismatch_is_jit() {
    assert_jit(
        JE::ValidationFunctionNameMismatch {
            validation_function: s("f"),
            range_function: s("g"),
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_certification_input_count_mismatch_is_proof() {
    assert_jit(
        JE::CertificationInputCountMismatch {
            functions: 1,
            lir_functions: 2,
            ranges: 1,
            fixup_manifests: 1,
        },
        DiagCode::Proof,
    );
}

#[test]
fn jit_unpublished_executable_buffer_is_jit() {
    assert_jit(
        JE::UnpublishedExecutableBuffer {
            buffer_base: 0x1000,
            buffer_end: 0x2000,
            code_len: 16,
            allocation_len: 4096,
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_invalid_executable_buffer_extent_is_jit() {
    assert_jit(
        JE::InvalidExecutableBufferExtent {
            buffer_base: 0x1000,
            code_end: 0x3000,
            allocation_end: 0x2000,
            code_len: 8192,
            allocation_len: 4096,
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_null_function_pointer_is_jit() {
    assert_jit(JE::NullFunctionPointer { symbol: s("f") }, DiagCode::Jit);
}

#[test]
fn jit_pointer_ownership_mismatch_is_jit() {
    assert_jit(
        JE::JitPointerOwnershipMismatch {
            context: s("entry"),
            pointer: 0x9000,
            buffer_base: 0x1000,
            buffer_end: 0x2000,
            code_len: 16,
            allocation_len: 4096,
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_function_pointer_symbol_mismatch_is_jit() {
    assert_jit(
        JE::FunctionPointerSymbolMismatch {
            symbol: s("f"),
            pointer: 0x1004,
            buffer_base: 0x1000,
            actual_offset: 4,
            expected_offset: 0,
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_branch_out_of_range_is_jit() {
    assert_jit(
        JE::BranchOutOfRange {
            offset: 0,
            target: 1 << 40,
            distance: 1 << 40,
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_veneer_out_of_range_is_jit() {
    assert_jit(
        JE::VeneerOutOfRange {
            symbol: s("memcpy"),
            offset: 0,
            veneer_offset: 1 << 40,
            distance: 1 << 40,
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_fixup_out_of_bounds_is_jit() {
    assert_jit(
        JE::FixupOutOfBounds {
            offset: 64,
            code_len: 16,
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_fixup_rebase_out_of_range_is_jit() {
    assert_jit(
        JE::FixupRebaseOutOfRange {
            offset: u32::MAX,
            base: 1,
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_empty_local_function_address_body_is_jit() {
    assert_jit(
        JE::EmptyLocalFunctionAddressBody { function: s("f") },
        DiagCode::Jit,
    );
}

#[test]
fn jit_local_function_address_replay_unavailable_is_proof() {
    assert_jit(
        JE::LocalFunctionAddressReplayUnavailable { offset: 8 },
        DiagCode::Proof,
    );
}

#[test]
fn jit_local_function_address_replay_rejected_is_jit() {
    assert_jit(
        JE::LocalFunctionAddressReplayRejected {
            offset: 8,
            detail: s("word does not decode to ADRP"),
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_raw_jit_named_symbol_address_fixup_unsupported_is_jit() {
    assert_jit(
        JE::RawJitNamedSymbolAddressFixupUnsupported {
            symbol: s("G"),
            kind: trust_cg_codegen::macho::reloc::AArch64RelocKind::Page21,
            offset: 0,
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_invalid_local_function_address_fixup_is_jit() {
    assert_jit(
        JE::InvalidLocalFunctionAddressFixup {
            offset: 4,
            detail: s("d"),
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_unaligned_local_function_address_image_is_jit() {
    assert_jit(
        JE::UnalignedLocalFunctionAddressImage { base: 0x1001 },
        DiagCode::Jit,
    );
}

#[test]
fn jit_duplicate_symbol_is_jit() {
    assert_jit(JE::DuplicateSymbol(s("f")), DiagCode::Jit);
}

#[test]
fn jit_profile_hooks_unsupported_is_jit() {
    assert_jit(JE::ProfileHooksUnsupported, DiagCode::Jit);
}

#[test]
fn jit_missing_block_profile_counter_is_jit() {
    assert_jit(
        JE::MissingBlockProfileCounter {
            function: s("f"),
            block_id: 3,
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_missing_block_timing_cell_is_jit() {
    assert_jit(
        JE::MissingBlockTimingCell {
            function: s("f"),
            block_id: 3,
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_profile_hook_mode_unimplemented_is_jit() {
    assert_jit(
        JE::ProfileHookModeUnimplemented {
            mode: trust_cg_codegen::jit::ProfileHookMode::BlockCounts,
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_published_bytes_hash_mismatch_is_jit() {
    assert_jit(
        JE::PublishedBytesHashMismatch {
            expected_sha256: s("a"),
            actual_sha256: s("b"),
            published_len: 16,
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_installed_artifact_replay_rejected_is_jit() {
    assert_jit(
        JE::InstalledArtifactReplayRejected {
            function: s("f"),
            offset: 8,
            detail: s("the installed word differs from the certified word"),
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_profile_patch_out_of_bounds_is_jit() {
    assert_jit(
        JE::ProfilePatchOutOfBounds {
            patch_offset: 64,
            code_len: 16,
        },
        DiagCode::Jit,
    );
}

#[test]
fn jit_host_jit_selected_codegen_profile_conflict_is_jit() {
    assert_jit(
        JE::HostJitSelectedCodegenProfileConflict {
            existing_profile_sha256: s("a"),
            incoming_profile_sha256: s("b"),
        },
        DiagCode::Jit,
    );
}

// ---------------------------------------------------------------------------
// Real raise sites: refusals produced by the codegen crate, not hand-built
// ---------------------------------------------------------------------------

#[test]
fn raise_site_tmbc_decode_refusal_is_module_io_driver() {
    // Formerly `PipelineError::ISel("invalid tMBC data: ...")`, which read as an
    // instruction-selection failure before any compilation layer ran.
    let err = trust_cg_codegen::pipeline::decode_tmbc(&[0u8; 3])
        .expect_err("a 3-byte buffer cannot carry the tMBC envelope");
    assert!(matches!(err, PE::ModuleIo(_)), "{err:?}");
    let (code, _) = classify_compile_error(&CE::Pipeline(err));
    assert_eq!(code, DiagCode::Driver);
}

/// A tMBC envelope around `payload`, as `encode_tmbc` writes one.
fn tmbc_envelope(payload: &[u8]) -> Vec<u8> {
    let mut bytes = trust_cg_codegen::pipeline::TMBC_MAGIC.to_vec();
    bytes.extend_from_slice(&trust_cg_codegen::pipeline::TMBC_VERSION.to_le_bytes());
    bytes.extend_from_slice(payload);
    bytes
}

#[test]
fn raise_site_tmbc_payload_deserialize_refusal_is_module_io_driver() {
    // The reader's payload refusal landed on main as
    // `PipelineError::ISel("failed to deserialize tMBC payload: ...")`.
    let err = trust_cg_codegen::pipeline::decode_tmbc(&tmbc_envelope(b"NOT_TRUST_IR"))
        .expect_err("a payload without the TRUST_IR header cannot decode");
    match &err {
        PE::ModuleIo(message) => assert!(
            message.starts_with("failed to deserialize tMBC payload: "),
            "{message}"
        ),
        other => panic!("expected PipelineError::ModuleIo, got {other:?}"),
    }
    let (code, _) = classify_compile_error(&CE::Pipeline(err));
    assert_eq!(code, DiagCode::Driver);
}

#[test]
fn raise_site_producer_omitted_body_gate_is_driver() {
    // trust-ir's own conformance golden `body_gate`: a v41+ header and a
    // bodied function with no codegen license, which the reader refuses as a
    // producer omission (the fixture list is pinned by trust-cg-codegen's
    // `tests/trust_ir_binary_container.rs`).
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/trust_ir_binary_container/conformance/body_gate.tmbc");
    let payload =
        std::fs::read(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    let err = trust_cg_codegen::pipeline::decode_tmbc(&tmbc_envelope(&payload))
        .expect_err("the reader refuses a v41+ bodied function without a codegen license");
    assert!(
        matches!(&err, PE::ProducerOmittedBodyGate { wire_version, .. } if *wire_version >= 41),
        "{err:?}"
    );
    let (code, _) = classify_compile_error(&CE::Pipeline(err));
    assert_eq!(code, DiagCode::Driver);
}

#[test]
fn raise_site_forced_frame_pointers_off_aarch64_is_driver() {
    // An explicit AArch64 frame-pointer policy on an x86-64 compile: the
    // compile driver refuses the route before it reads the module.
    use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            aarch64_force_frame_pointers: true,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("x86_64-unknown-linux-gnu").expect("an x86-64 ELF triple"),
    );
    let err = match compiler.compile(&trust_ir::Module::new("frame_policy")) {
        Ok(_) => panic!("x86-64 cannot honor an AArch64 frame-pointer policy"),
        Err(err) => err,
    };
    assert!(
        matches!(err, CE::Aarch64FramePointersUnsupported { .. }),
        "{err:?}"
    );
    let (code, _) = classify_compile_error(&err);
    assert_eq!(code, DiagCode::Driver);
}

#[test]
fn raise_site_module_bytes_utf8_refusal_is_module_io_driver() {
    let err = trust_cg_codegen::pipeline::load_module_from_bytes(&[0xff, 0xfe, 0xfd])
        .expect_err("non-UTF-8, non-tMBC bytes cannot be a module");
    assert!(matches!(err, PE::ModuleIo(_)), "{err:?}");
    let (code, _) = classify_compile_error(&CE::Pipeline(err));
    assert_eq!(code, DiagCode::Driver);
}

#[test]
fn raise_site_lsda_typed_catch_refusal_is_unwind() {
    // Formerly `PipelineError::MalformedAarch64Function`, a machine-code variant.
    use trust_cg_ir::types::BlockId;
    use trust_cg_ir::{EhCallSiteEntry, LandingPadEntry, MachFunction, Signature, Type};
    let mut func = MachFunction::new(
        s("with_catch"),
        Signature::new(vec![Type::I64], vec![Type::I64]),
    );
    func.eh_metadata.personality = Some(s("__gxx_personality_v0"));
    func.eh_metadata.add_landing_pad(LandingPadEntry {
        block: BlockId(2),
        offset: 0x80,
        catch_type_indices: vec![1],
        is_cleanup: false,
    });
    func.eh_metadata.add_call_site(EhCallSiteEntry {
        call_block: BlockId(0),
        start_offset: 0x10,
        length: 0x08,
        landing_pad_block: Some(BlockId(2)),
    });
    let err = trust_cg_codegen::pipeline::generate_lsda_for_function(&func)
        .expect_err("a typed catch has no typeinfo relocation authority");
    assert!(matches!(err, PE::MalformedAarch64Eh { .. }), "{err:?}");
    let (code, _) = classify_compile_error(&CE::Pipeline(err));
    assert_eq!(code, DiagCode::Unwind);
}

#[test]
fn raise_site_object_global_refusal_is_object() {
    // Formerly `PipelineError::Encoding("AArch64 object global ...")`.
    use trust_cg_codegen::pipeline::{GlobalSymbolRef, ObjectGlobal, Pipeline, PipelineConfig};
    use trust_cg_ir::inst::{AArch64Opcode, MachInst};
    use trust_cg_ir::{MachFunction, Signature};
    let mut func = MachFunction::new(s("main"), Signature::new(vec![], vec![]));
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(func.entry, ret);
    let globals = vec![ObjectGlobal {
        name: s("BROKEN_SLOT"),
        data: vec![0; 4],
        mutable: true,
        is_external: true,
        symbol_refs: vec![GlobalSymbolRef {
            offset: 0,
            symbol: s("main"),
            addend: 0,
        }],
        is_thread_local: false,
        is_import: false,
        is_weak: false,
        align: 4,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        comdat: false,
        section: None,
    }];
    let pipeline = Pipeline::new(PipelineConfig {
        target_triple: s("aarch64-apple-darwin"),
        ..Default::default()
    });
    let err = pipeline
        .compile_module_with_globals(&[func], &globals)
        .expect_err("a pointer slot past the initializer bytes must be refused");
    assert!(matches!(err, PE::ObjectEmission(_)), "{err:?}");
    let (code, _) = classify_compile_error(&CE::Pipeline(err));
    assert_eq!(code, DiagCode::Object);
}

// ---------------------------------------------------------------------------
// [TCG-LINK-UNDEF]: filed under the layer that produces the undefined symbol
// ---------------------------------------------------------------------------

const TAG: &str = "Cs1a2b3c_4demo";

fn refs(symbols: &[&str]) -> std::collections::BTreeSet<String> {
    symbols.iter().map(|symbol| symbol.to_string()).collect()
}

#[test]
fn link_undef_is_filed_under_the_mir_lowering_bridge_not_the_object_writer() {
    let refusal = super::LinkUndefinedLocalSymbolsRefusal::new(&[s("_RNvCs1a2b3c_4demo1f: x")]);
    assert_eq!(refusal.code, DiagCode::MirUnsupported);
    assert_eq!(refusal.code.as_str(), "TCG-MIR-UNSUPPORTED");
    assert_ne!(refusal.code, DiagCode::Object);
    assert_eq!(refusal.count, "1");
    // The wrapper header and trailer are unchanged (the census parses them).
    assert!(refusal.why.starts_with(
        "rustc_codegen_trust_cg: this crate's emitted objects reference symbol(s) only this \
         crate could define, and it did not define them — refusing rather than shipping an \
         object that cannot link:\n  - _RNvCs1a2b3c_4demo1f: x\noptions: (1) compile this \
         crate with the LLVM backend;"
    ));
}

#[test]
fn link_undef_entries_name_the_drop_record_and_the_uncollected_call() {
    // A v0 symbol ends in its INSTANTIATING crate's token; these three were
    // instantiated by this crate, the fourth by another.
    let dropped = format!("_RINvCs0_4core7droppedB{TAG}");
    let uncollected = format!("_RINvCs0_4core11uncollectedB{TAG}");
    let defined = format!("_RINvCs0_4core7definedB{TAG}");
    let foreign = "_RINvCs0_4core3fooBCs9zzz_5other".to_string();
    let reachable = refs(&[&dropped, &uncollected, &defined, &foreign, "_abort"]);
    let drop_records: std::collections::BTreeMap<&str, &str> = [(
        dropped.as_str(),
        "[TCG-EH-UNWIND] exception-handling sidecar unsupported at code-only API `x`",
    )]
    .into_iter()
    .collect();
    let mono = refs(&[&dropped, &defined]);
    let entries = super::link_undefined_local_symbol_entries(&reachable, TAG, &drop_records, &mono);
    // `reachable_refs` is ordered, so `..11uncollected..` sorts before `..7dropped..`.
    assert_eq!(
        entries,
        vec![
            format!(
                "{uncollected}: called by an emitted object, but rustc's monomorphization \
                 collector never placed it in this crate — no crate can define it, so the \
                 bridge lowered a call rustc did not plan"
            ),
            format!(
                "{dropped}: DROPPED by this compile ([TCG-EH-UNWIND] exception-handling sidecar \
                 unsupported at code-only API `x`) yet called by an emitted object — the drop \
                 verdict does not hold for this crate type"
            ),
        ]
    );
}

#[test]
fn link_undef_entries_cover_local_rooted_symbols_but_not_bridge_globals() {
    // A LOCAL item's v0 path is rooted at this crate's token, which then sits at
    // the FRONT of the symbol; an instance over a local type names it inside.
    let local_item = format!("_RNv{TAG}4slow");
    let over_local_type = format!("_RINvCs0_4core1fNtB2_{TAG}1AE");
    // The bridge's own synthesized globals carry a `.` and are not v0 manglings.
    let vtable = format!("_RNv{TAG}4main.vtable.0123456789abcdef");
    let foreign = "_RNvCs9zzz_5other4slow".to_string();
    assert!(super::symbol_only_local_crate_defines(&local_item, TAG));
    assert!(super::symbol_only_local_crate_defines(
        &over_local_type,
        TAG
    ));
    assert!(!super::symbol_only_local_crate_defines(&vtable, TAG));
    assert!(!super::symbol_only_local_crate_defines(&foreign, TAG));
    let reachable = refs(&[&local_item, &over_local_type, &vtable, &foreign]);
    let mono = refs(&[&over_local_type]);
    let entries = super::link_undefined_local_symbol_entries(
        &reachable,
        TAG,
        &std::collections::BTreeMap::new(),
        &mono,
    );
    assert_eq!(entries.len(), 1, "{entries:?}");
    assert!(entries[0].starts_with(&format!("{local_item}: called by an emitted object")));
}

/// `[TCG-ITER-STUB-REACHABLE]`'s reach: a trap stub named only by a dead std
/// body (whose every caller was intercepted, so no local body references it)
/// is unreached; one a local function names through a lowered std body is
/// reached, and a cycle terminates.
#[test]
fn a_trap_stub_is_reached_only_through_emitted_references_from_local_code() {
    let mut edges: std::collections::HashMap<&str, Vec<&str>> = std::collections::HashMap::new();
    edges.insert(
        "local_fold",
        vec!["std_rev_fold_intercepted_away", "std_by_ref_rfold"],
    );
    edges.insert(
        "std_by_ref_rfold",
        vec!["std_spec_try_rfold_stub", "std_by_ref_rfold"],
    );
    edges.insert("std_rfold_dead", vec!["std_other_stub"]);
    edges.insert("local_static", vec!["local_fold"]);
    let reach = super::symbols_reachable_from(["local_fold", "local_static"], &edges);
    assert!(reach.contains("std_spec_try_rfold_stub"), "{reach:?}");
    assert!(reach.contains("local_static"), "{reach:?}");
    assert!(!reach.contains("std_other_stub"), "{reach:?}");
    assert!(!reach.contains("std_rfold_dead"), "{reach:?}");
    assert!(super::symbols_reachable_from(std::iter::empty(), &edges).is_empty());
}

#[test]
fn local_crate_tag_comes_from_a_local_item_or_an_instantiating_crate_suffix() {
    let ident = "_4demo";
    let tag = "Cs5hAsh_4demo";
    // A local item's own v0 symbol: the path root is the tag.
    assert_eq!(
        super::local_crate_v0_tag(["_RNvCs5hAsh_4demo4slow"], [], ident).as_deref(),
        Some(tag)
    );
    // Every local item `#[no_mangle]`: an upstream generic instantiated here
    // ends in this crate's tag. A symbol that only mentions the crate name
    // elsewhere, or a non-v0 symbol, is not read.
    let upstream_generic =
        "_RNvXs2J_NtNtCs0core_4core5slice4iterINtB6_4ItermENtB8_4Iter4nextCs5hAsh_4demo";
    let mono = [
        "_RNvCs9zzz_5other4slow",
        "_RINvCs0core_4core4demoCs5hAsh_4demoE",
        "demo_no_mangle_4demo",
        upstream_generic,
    ];
    assert_eq!(
        super::local_crate_v0_tag(std::iter::empty(), mono, ident).as_deref(),
        Some(tag)
    );
    // No local v0 item and no instantiating-crate suffix: no tag, so the gate
    // has nothing only-ours to check.
    assert_eq!(
        super::local_crate_v0_tag(
            std::iter::empty(),
            ["_RNvCs9zzz_5other4slow", "demo_4demo"],
            ident
        ),
        None
    );
}

#[test]
fn native_copy_names_no_crate_reads_real_v0_symbols() {
    // Symbols a native `-Copt-level=0` / `1` compile of crate `xlib` placed in
    // its codegen units (read off its object; Mach-O's leading `_` dropped).
    let ident = "_4xlib";
    let local_item = "_RNvCs4eJvtz1GcQV_4xlib7lib_ptr";
    let local_generic = "_RINvNtCsiHPWGBzRfGA_4core3mem4swapmECs4eJvtz1GcQV_4xlib";
    let local_copy_named_here = "_RNvMs6_NtCsiHPWGBzRfGA_4core3numm3powCs4eJvtz1GcQV_4xlib";
    // `#[inline]` core fns rustc copies into every crate under the SAME name.
    let as_ptr = "_RNvMNtCsiHPWGBzRfGA_4core3stre6as_ptr";
    let pow = "_RNvMs6_NtCsiHPWGBzRfGA_4core3numm3pow";
    let tag = super::local_crate_v0_tag(
        [local_item],
        [local_item, local_generic, as_ptr, pow],
        ident,
    );
    assert_eq!(tag.as_deref(), Some("Cs4eJvtz1GcQV_4xlib"));
    let names_no_crate = |symbol: &str| {
        super::native_copy_names_no_crate(symbol, tag.as_deref(), || {
            panic!("a v0 token decides without the instance")
        })
    };
    assert!(names_no_crate(as_ptr));
    assert!(names_no_crate(pow));
    assert!(!names_no_crate(local_item));
    assert!(!names_no_crate(local_generic));
    assert!(!names_no_crate(local_copy_named_here));
    // Legacy mangling has no v0 token: the instance decides.
    assert!(super::native_copy_names_no_crate(
        "_ZN4core3str21_$LT$impl$u20$str$GT$6as_ptr17h0123456789abcdefE",
        None,
        || true
    ));
    assert!(!super::native_copy_names_no_crate(
        "_ZN4xlib7lib_ptr17h0123456789abcdefE",
        None,
        || false
    ));
}

// ---------------------------------------------------------------------------
// Variants main added while E0.3 was parked: each is classified by the layer
// that raises it (the merge failed E0004 on every one until it was named).
// ---------------------------------------------------------------------------

fn layout_crosscheck_error() -> trust_cg_codegen::aarch64::layout_crosscheck::LayoutCrossCheckError
{
    trust_cg_codegen::aarch64::layout_crosscheck::LayoutCrossCheckError::BlockMapSize {
        encoder: 2,
        layout: 3,
    }
}

fn switch_binding_error() -> trust_cg_verify::aarch64_switch_binding::SwitchBindingError {
    trust_cg_verify::aarch64_switch_binding::SwitchBindingError::ImageTooShort {
        layout: 8,
        image: 4,
    }
}

#[test]
fn compile_volatile_trace_changed_is_regalloc() {
    // Raised by `check_volatile_trace_preserved`, the translation validator
    // that compares the x86-64 machine-IR optimizer's volatile access trace.
    assert_untyped(
        CE::VolatileTraceChanged {
            function: s("f"),
            violation: s("a volatile load was elided"),
        },
        DiagCode::Regalloc,
    );
}

#[test]
fn compile_symbol_shadowing_and_object_binding_are_object() {
    assert_untyped(
        CE::ModuleLocalFunctionShadowsRuntimeSymbol {
            target: s("aarch64-unknown-linux-gnu"),
            function: s("memcpy"),
        },
        DiagCode::Object,
    );
    assert_untyped(
        CE::DataShadowsBackendSymbol {
            target: s("aarch64-unknown-linux-gnu"),
            global: s("rust_eh_personality"),
        },
        DiagCode::Object,
    );
    assert_untyped(
        CE::AotCodeReferenceReachesData {
            target: s("aarch64-unknown-linux-gnu"),
            detail: s("CALL26 to `memcpy` resolves into .data"),
        },
        DiagCode::Object,
    );
    assert_untyped(
        CE::AotModuleLocalFunctionBindingViolated {
            target: s("aarch64-unknown-linux-gnu"),
            function: s("helper"),
            detail: s("symbol is STB_GLOBAL"),
        },
        DiagCode::Object,
    );
    assert_untyped(
        CE::AotObjectSymbolDisciplineViolated {
            target: s("aarch64-apple-darwin"),
            detail: s("emitted function `helper` has no symbol"),
        },
        DiagCode::Object,
    );
}

#[test]
fn compile_route_configuration_refusals_are_driver() {
    assert_untyped(
        CE::RelocationModelUnsupported {
            target: s("x86_64-apple-darwin"),
            model: trust_cg_codegen::compiler::RelocationModel::Pic,
            reason: "only AArch64 ELF implements pie/pic",
        },
        DiagCode::Driver,
    );
    assert_untyped(
        CE::Aarch64IsaProfileUnsupported {
            target: s("x86_64-unknown-linux-gnu"),
            profile: AArch64IsaProfile::default(),
            reason: "not an AArch64 target",
        },
        DiagCode::Driver,
    );
    assert_untyped(
        CE::EhFramesCannotUnwindUnsupported {
            target: s("x86_64-unknown-linux-gnu"),
            reason: "only the AArch64 LSDA emitter models non-unwinding exception frames",
        },
        DiagCode::Driver,
    );
}

#[test]
fn pipeline_machine_code_validators_are_regalloc() {
    assert_pipeline(
        PE::VolatileAccessNotPreserved {
            function: s("f"),
            detail: s("a path skips the volatile store"),
        },
        DiagCode::Regalloc,
    );
    assert_pipeline(
        PE::Aarch64LayoutCrossCheck {
            function: s("f"),
            error: layout_crosscheck_error(),
        },
        DiagCode::Regalloc,
    );
    assert_pipeline(
        PE::FrameLowering(LE::LayoutCrossCheck {
            function: s("f"),
            error: layout_crosscheck_error(),
        }),
        DiagCode::Regalloc,
    );
    assert_pipeline(
        PE::Aarch64SwitchBinding {
            function: s("f"),
            error: switch_binding_error(),
        },
        DiagCode::Regalloc,
    );
    assert_pipeline(
        PE::FrameLowering(LE::SwitchBinding {
            function: s("f"),
            error: switch_binding_error(),
        }),
        DiagCode::Regalloc,
    );
}

#[test]
fn pipeline_new_object_refusals_are_object() {
    use trust_cg_codegen::object_sections::SectionRefusal;
    assert_pipeline(
        PE::ElfSymbol(trust_cg_codegen::elf::ElfSymbolError::SymbolTableFrozen {
            symbol: s("late"),
        }),
        DiagCode::Object,
    );
    assert_pipeline(
        PE::ElfSection(
            trust_cg_codegen::elf::ElfSectionError::AlignmentNotPowerOfTwo {
                name: s(".data"),
                align: 3,
            },
        ),
        DiagCode::Object,
    );
    assert_pipeline(
        PE::MachODeploymentTarget(
            trust_cg_codegen::apple_deployment::AppleDeploymentTargetError::NotAnAppleTarget {
                triple: s("aarch64-unknown-linux-gnu"),
            },
        ),
        DiagCode::Object,
    );
    assert_pipeline(
        PE::ExplicitSectionUnsupported {
            global: s("g"),
            section: s("__TEXT,__text"),
            format: "Mach-O",
            code: SectionRefusal::ExecutableSection,
            reason: s("data in an executable section"),
        },
        DiagCode::Object,
    );
    assert_pipeline(
        PE::ExplicitFunctionSectionUnsupported {
            function: s("f"),
            section: s(".data.f"),
            format: "ELF",
            code: SectionRefusal::DataSection,
            reason: s("code in a data section"),
        },
        DiagCode::Object,
    );
    assert_pipeline(
        PE::RelocationWindowExceeded {
            relocation: "R_AARCH64_CALL26",
            symbol: s("far"),
            site: 0,
            displacement: 1 << 28,
            min: -(1 << 27),
            max: (1 << 27) - 4,
        },
        DiagCode::Object,
    );
    assert_pipeline(
        PE::LocalExecTlsWindowExceeded {
            symbol: s("tls"),
            site: 0,
            offset: 1 << 24,
            addend: 0,
            minimum: (1 << 24) + 16,
            max: (1 << 24) - 1,
        },
        DiagCode::Object,
    );
    assert_x86(
        XE::WeakUndefinedReferenceUnsupported {
            symbol: s("weak_ref"),
            format: trust_cg_codegen::x86_64::X86OutputFormat::Elf,
        },
        DiagCode::Object,
    );
    assert_x86(
        XE::ImportVisibilityUnsupported {
            symbol: s("hidden_import"),
            visibility: trust_ir::Visibility::Hidden,
            format: trust_cg_codegen::x86_64::X86OutputFormat::MachO,
        },
        DiagCode::Object,
    );
    assert_x86(
        XE::FunctionVisibilityUnsupported {
            function: s("hidden_fn"),
            visibility: trust_ir::Visibility::Hidden,
            format: trust_cg_codegen::x86_64::X86OutputFormat::Elf,
            reason: "only the x86-64 Mach-O module emitter spells a hidden function definition",
        },
        DiagCode::Object,
    );
    assert_x86(
        XE::MachOSymbolNameCollision {
            symbol: s("GCC_except_table_f"),
            nlist: s("_GCC_except_table_f"),
            kind: "function definition",
            existing: "LSDA label",
        },
        DiagCode::Object,
    );
    assert_x86(
        XE::FunctionLinkageUnsupported {
            function: s("local_fn"),
            linkage: trust_cg_codegen::pipeline::FunctionSymbolLinkage::Local,
            format: trust_cg_codegen::x86_64::X86OutputFormat::MachO,
            reason: "only the x86-64 ELF module emitter binds a module-local function definition",
        },
        DiagCode::Object,
    );
}

#[test]
fn pipeline_eh_frame_decode_check_is_unwind() {
    assert_pipeline(
        PE::EhFrameDecodeCheck(
            trust_cg_codegen::dwarf_cfi_decode_check::EhFrameDecodeError {
                message: s("FDE pc-begin disagrees"),
            },
        ),
        DiagCode::Unwind,
    );
}

#[test]
fn pipeline_module_encoding_target_and_policy_refusals_are_driver() {
    assert_pipeline(
        PE::NoTmbcWireImage(s("inlining-chain scope link")),
        DiagCode::Driver,
    );
    assert_pipeline(
        PE::TargetAbiUnresolved(trust_cg_lower::abi::AArch64AbiTargetError::Empty),
        DiagCode::Driver,
    );
    assert_pipeline(
        PE::AmbientLateLayoutControl {
            function: s("f"),
            control: "TCG_A64_LATE_LAYOUT",
        },
        DiagCode::Driver,
    );
}

#[test]
fn jit_executable_memory_and_data_image_refusals_are_jit() {
    use trust_cg_codegen::jit::JitPageProtection;
    for err in [
        JE::MapJitRefused {
            len: 4096,
            code_signing: None,
            source: std::io::Error::other("EPERM"),
        },
        JE::WritableExecutableProtectionRefused {
            requested: JitPageProtection::ReadWriteExecute,
            buffer_base: 0x1000,
            allocation_len: 4096,
        },
        JE::PublishedProtectionDowngradeRefused {
            requested: JitPageProtection::ReadWrite,
            buffer_base: 0x1000,
            allocation_len: 4096,
        },
        JE::ExecutableBufferInFlight {
            buffer_base: 0x1000,
            in_flight: 1,
        },
        JE::ProcessLifetimeReleaseRefused {
            buffer_base: 0x1000,
        },
        JE::UnenforceableTeardownPolicy {
            policy: s("manual"),
        },
        JE::TeardownPolicyDowngradeRefused {
            current: s("process_lifetime"),
            requested: s("ref_counted"),
        },
        JE::JitDataImageUnsupported {
            global: s("g"),
            reason: s("thread-local"),
        },
        JE::JitDataGlobalUnplaceable {
            offset: 8,
            global: s("g"),
            reason: s("not placed"),
        },
        JE::JitDataRelocationOutOfRange {
            symbol: s("g"),
            site: 0,
            target: 1 << 40,
            detail: s("beyond ADRP reach"),
        },
        JE::DataImageMap {
            len: 4096,
            source: std::io::Error::other("ENOMEM"),
        },
        JE::InvalidDataRelocation {
            offset: 8,
            detail: s("misaligned"),
        },
    ] {
        assert_jit(err, DiagCode::Jit);
    }
}

#[test]
fn jit_unwind_table_refusals_are_unwind() {
    for err in [
        JE::JitUnwindProfileHooksUnsupported {
            function: s("f"),
            mode: trust_cg_codegen::jit::ProfileHookMode::CallCounts,
        },
        JE::JitUnwindFrameLayoutMissing { function: s("f") },
        JE::JitUnwindFrameShapeUnsupported {
            function: s("f"),
            detail: s("dynamic stack"),
        },
        JE::JitUnwindPrologueMismatch {
            function: s("f"),
            detail: s("stp offset"),
        },
        JE::JitUnwindMultiplePersonalities {
            personalities: vec![s("a"), s("b")],
        },
        JE::JitUnwindTypedCatchUnsupported {
            function: s("f"),
            typeinfo_symbols: vec![s("_ZTIi")],
        },
        JE::JitUnwindPersonalityUnresolved {
            personality: s("rust_eh_personality"),
        },
        JE::JitUnwindTableRejected {
            detail: s("bad CIE"),
        },
        JE::JitUnwindRelocationOutOfRange {
            field_offset: 0,
            target_offset: 1 << 33,
        },
        JE::JitUnwindRegistrationUnavailable {
            detail: s("no __register_frame"),
        },
        JE::JitUnwindRegistrationNotObserved {
            function: s("f"),
            expected_fde: 0x10,
            observed_fde: 0x20,
            observed_function: 0x30,
        },
    ] {
        assert_jit(err, DiagCode::Unwind);
    }
}

#[test]
fn jit_missing_proof_evidence_is_proof() {
    for err in [
        JE::SourceModuleHasNoWireImage(s("inlining-chain scope link")),
        JE::JitUnwindProofEvidenceUnavailable { function: s("f") },
        JE::JitDataRelocationProofUnavailable {
            offset: 8,
            symbol: s("g"),
        },
    ] {
        assert_jit(err, DiagCode::Proof);
    }
}

#[test]
fn pipeline_debug_info_input_is_debug_info() {
    assert_pipeline(
        PE::DebugInfoInput(s(
            "module DWARF emission received 2 function(s), 1 text offset(s)",
        )),
        DiagCode::DebugInfo,
    );
}

#[test]
fn pipeline_adapter_refusal_is_ir_lowering() {
    assert_pipeline(
        PE::IrLowering(trust_cg_lower::AdapterError::UnsupportedInstruction(s(
            "byval parameter",
        ))),
        DiagCode::IrLowering,
    );
}
