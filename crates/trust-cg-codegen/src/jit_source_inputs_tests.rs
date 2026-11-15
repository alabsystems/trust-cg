//! Custody/policy controls only. No unavailable tool is treated as proof success.

use super::*;
use crate::jit::{JitCompiler, JitConfig};
use crate::jit_cert::{
    JitCertCacheKey, aarch64_verifier_input_digest, aarch64_verifier_input_digest_with_lir,
};
use std::collections::HashMap;
use trust_cg_ir::regs::{SpecialReg, X0, X29, X30};
use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, Signature, Type};
use trust_cg_lower::function::{BasicBlock, Signature as LirSignature};
use trust_cg_lower::instructions::{Instruction, Opcode, Value};
use trust_cg_lower::{Function, ProofContext};
use trust_cg_verify::function_verifier::{
    FunctionVerificationPreconditionFailure, InstructionVerificationResult,
};
use trust_cg_verify::{FunctionVerifier, VerificationConfig};

fn fixture(name: &str) -> (MachFunction, (Function, ProofContext)) {
    let mut source = Function::new(
        name,
        LirSignature {
            params: vec![],
            returns: vec![trust_cg_lower::Type::I64],
        },
    );
    source.blocks.insert(
        source.entry_block,
        BasicBlock {
            instructions: vec![
                Instruction {
                    opcode: Opcode::Iconst {
                        imm: 42,
                        ty: trust_cg_lower::Type::I64,
                    },
                    args: vec![],
                    results: vec![Value(0)],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(0)],
                    results: vec![],
                },
            ],
            ..Default::default()
        },
    );
    let mut machine = MachFunction::new(name.into(), Signature::new(vec![], vec![Type::I64]));
    for (opcode, operands) in [
        (
            AArch64Opcode::StpPreIndex,
            vec![
                MachOperand::PReg(X29),
                MachOperand::PReg(X30),
                MachOperand::Special(SpecialReg::SP),
                MachOperand::Imm(-16),
            ],
        ),
        (
            AArch64Opcode::AddRI,
            vec![
                MachOperand::PReg(X29),
                MachOperand::Special(SpecialReg::SP),
                MachOperand::Imm(0),
            ],
        ),
        (
            AArch64Opcode::Movz,
            vec![
                MachOperand::PReg(X0),
                MachOperand::Imm(42),
                MachOperand::Imm(0),
            ],
        ),
        (
            AArch64Opcode::LdpPostIndex,
            vec![
                MachOperand::PReg(X29),
                MachOperand::PReg(X30),
                MachOperand::Special(SpecialReg::SP),
                MachOperand::Imm(16),
            ],
        ),
        (AArch64Opcode::Ret, vec![MachOperand::PReg(X30)]),
    ] {
        let id = machine.push_inst(MachInst::new(opcode, operands));
        machine.append_inst(machine.entry, id);
    }
    (machine, (source, ProofContext::default()))
}

fn without_tools<T>(run: impl FnOnce() -> T) -> T {
    trust_cg_process_env::with_env_edits(|env| {
        env.set("AY_SOLVER_PATH", "/nonexistent/jit-source-custody-ay");
        env.set(
            "TCG_EXTERNAL_CLEAN_CHECKER",
            "/nonexistent/jit-source-custody-clean",
        );
        env.set("TCG_CANARY_NO_CACHE", "1");
        env.set("TCG_NO_VERDICT_DB", "1");
        env.set("TCG_REFINE_SOLVER", "0");
        run()
    })
}

#[test]
fn source_inputs_borrow_exact_ordinal_owners_without_cloning() {
    let (a, source_a) = fixture("first");
    let (b, source_b) = fixture("second");
    let machines = [a, b];
    let sources = [source_a, source_b];
    let inputs = Aarch64JitInputs::with_replayed_lir(&machines, &sources).unwrap();
    assert_eq!(inputs.functions().as_ptr(), machines.as_ptr());
    for (ordinal, source) in sources.iter().enumerate() {
        assert!(std::ptr::eq(inputs.source(ordinal).unwrap(), &source.0));
    }
    assert!(std::ptr::eq(
        inputs.source_verifier().unwrap(),
        crate::compiler::shared_aarch64_function_verifier(),
    ));
}

#[test]
fn source_inputs_reject_missing_extra_and_reordered_sources_before_encoding() {
    let (a, source_a) = fixture("first");
    let (b, source_b) = fixture("second");
    let machines = [a, b];
    let sources = [source_a, source_b];
    let jit = JitCompiler::new(JitConfig {
        verify: true,
        ..Default::default()
    });
    let module = trust_ir::Module::new("pairing-control");
    let compile = |machines: &[MachFunction], sources: &[(Function, ProofContext)]| {
        jit.compile_with_lir_and_encoding_metrics(
            machines,
            sources,
            &module,
            &module,
            &HashMap::new(),
            true,
            None,
        )
        .expect_err("source pairing must refuse before encoding or mapping")
    };
    for missing in [&sources[..0], &sources[..1]] {
        assert!(
            matches!(compile(&machines, missing), JitError::LirSourceCountMismatch {
            machine: 2, lir,
        } if lir == missing.len())
        );
    }
    assert!(matches!(
        compile(&machines[..1], &sources),
        JitError::LirSourceCountMismatch { machine: 1, lir: 2 }
    ));
    let reversed = [sources[1].clone(), sources[0].clone()];
    assert!(
        matches!(compile(&machines, &reversed), JitError::LirSourcePairMismatch {
        ordinal: 0, machine, lir,
    } if machine == "first" && lir == "second")
    );
    let mut renamed = sources.clone();
    renamed[1].0.name = "replacement".into();
    assert!(
        matches!(compile(&machines, &renamed), JitError::LirSourcePairMismatch {
        ordinal: 1, machine, lir,
    } if machine == "second" && lir == "replacement")
    );
}

#[test]
fn source_inputs_require_enforce_and_formal_on_miss_despite_ambient_mode() {
    without_tools(|| {
        let (machine, source) = fixture("policy");
        let machines = [machine];
        let sources = [source];
        let inputs = Aarch64JitInputs::with_replayed_lir(&machines, &sources).unwrap();
        let verifier = inputs.source_verifier().unwrap();
        for ambient in ["off", "warn", "enforce"] {
            trust_cg_process_env::with_env_overrides(&[("TCG_PROVENANCE_XCHECK", ambient)], || {
                let request = inputs.capture_request(verifier);
                // Enforce is observed through the real precondition, not a
                // diagnostic string or an ambient policy assumption.
                let missing = verifier.verify_with_request(&machines[0], None, &request);
                assert!(matches!(
                    missing.report().precondition_failure,
                    Some(FunctionVerificationPreconditionFailure::MissingLirSource)
                ));
                let default_policy = FunctionVerifier::new().verify_with_request(
                    &machines[0],
                    inputs.source(0),
                    &request,
                );
                assert!(matches!(
                    default_policy.report().precondition_failure,
                    Some(
                        FunctionVerificationPreconditionFailure::VerificationRequestConfigMismatch
                    )
                ));
                let expected_policy =
                    FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
                let accepted_config =
                    expected_policy.verify_with_request(&machines[0], None, &request);
                assert!(matches!(
                    accepted_config.report().precondition_failure,
                    Some(FunctionVerificationPreconditionFailure::MissingLirSource)
                ));
            });
        }
    });
}

#[test]
fn source_inputs_reach_frame_obligation_but_never_accept_missing_replay() {
    without_tools(|| {
        let (machine, source) = fixture("frame");
        let machines = [machine];
        let sources = [source];
        let inputs = Aarch64JitInputs::with_replayed_lir(&machines, &sources).unwrap();
        assert!(
            trust_cg_verify::source_bound_frame::source_bound_frame(&sources[0].0, &machines[0])
                .is_ok()
        );
        let verifier = inputs.source_verifier().unwrap();
        let request = inputs.capture_request(verifier);
        let report = verifier.verify_with_request(&machines[0], inputs.source(0), &request);
        assert!(report.report().precondition_failure.is_none());
        for ordinal in [0, 1, 3] {
            assert!(matches!(&report.report().instructions[ordinal].result,
                InstructionVerificationResult::Unverified { reason }
                    if reason == "source-bound frame needs independently replayed proof"));
        }
        assert!(!report.report().emitted_opcode_inventory().is_promotable());
        assert!(!report.reusable_for(&request));
        assert!(report.matches_aarch64_input(&machines[0], inputs.source(0)));
        assert!(!report.matches_aarch64_input(&machines[0], None));
        let mut changed = sources[0].0.clone();
        changed
            .blocks
            .get_mut(&changed.entry_block)
            .unwrap()
            .instructions[0]
            .opcode = Opcode::Iconst {
            imm: 43,
            ty: trust_cg_lower::Type::I64,
        };
        assert!(!report.matches_aarch64_input(&machines[0], Some(&changed)));
    });
}

#[test]
fn same_name_different_source_body_cannot_supply_frame_authority() {
    without_tools(|| {
        let (machine, mut source) = fixture("same_name");
        source
            .0
            .blocks
            .get_mut(&source.0.entry_block)
            .unwrap()
            .instructions[0]
            .opcode = Opcode::Iconst {
            imm: 43,
            ty: trust_cg_lower::Type::I64,
        };
        let machines = [machine];
        let sources = [source];
        let inputs = Aarch64JitInputs::with_replayed_lir(&machines, &sources).unwrap();
        let mismatch = trust_cg_verify::source_bound_frame::FrameBindingMismatch::Body(
            trust_cg_verify::aarch64_affine_lowering::AffineLoweringError::ReturnMismatch,
        );
        assert_eq!(
            trust_cg_verify::source_bound_frame::source_bound_frame(&sources[0].0, &machines[0])
                .err()
                .and_then(|refusal| refusal.mismatch().cloned()),
            Some(mismatch.clone())
        );
        let verifier = inputs.source_verifier().unwrap();
        let request = inputs.capture_request(verifier);
        let report = verifier.verify_with_request(&machines[0], inputs.source(0), &request);
        // The verifying JIT's enforced source check rejects the erroneous
        // supported target by name; it is not an uncovered-envelope gap.
        assert_eq!(
            report.report().precondition_failure,
            Some(FunctionVerificationPreconditionFailure::SourceBoundFrameMismatch(mismatch))
        );
        assert!(report.report().has_failures());
        assert!(report.report().instructions.is_empty());
        assert!(!report.reusable_for(&request));
        let inventory = report.report().emitted_opcode_inventory();
        assert!(!inventory.is_promotable());
        assert!(
            inventory
                .promotion_rejection_reason()
                .unwrap()
                .contains("[TCG-SOURCE-BOUND-FRAME-MISMATCH]")
        );
        let certificate = crate::jit_cert::JitCertificate::from_report(
            &machines[0],
            report.report(),
            0..4,
            "aarch64",
            aarch64_verifier_input_digest_with_lir(&machines[0], inputs.source(0)).unwrap(),
            [0; 32],
        );
        assert!(!certificate.is_verified());
    });
}

/// The frame prologue/epilogue in these fixtures must never carry the
/// SOURCE-BOUND FRAME theorem when no matching source is present.
///
/// They do reach the operand-bound pair-memory obligation
/// (`aarch64_pair_memory_proofs`), which is a different and weaker claim: it
/// says the emitted `STP …, [SP,#-16]!` / `LDP …, [SP],#16` denote what their
/// operands say, not that a matching save preceded the restore. That
/// obligation discharges only by sampling, and a sampled discharge is reported,
/// never credited (E0.2): both rows stay `Unverified`, name the pair
/// obligation rather than the frame theorem, and keep the function
/// unpromotable.
fn assert_no_frame_authority(
    report: &trust_cg_verify::function_verifier::FunctionVerificationReport,
) {
    let sampled_pair = format!(
        "{}: `RECONSTRUCTED PairMemory_",
        trust_cg_verify::function_verifier::STATISTICAL_EVIDENCE_IS_NOT_CREDIT
    );
    for ordinal in [0usize, 3] {
        match &report.instructions[ordinal].result {
            InstructionVerificationResult::Unverified { reason } => {
                assert!(
                    reason.starts_with(&sampled_pair),
                    "instruction {ordinal} must be the uncredited sampled pair row: {reason}"
                );
                assert!(
                    !reason.contains(trust_cg_verify::source_bound_frame::FRAME_OBLIGATION_NAME),
                    "instruction {ordinal} names the frame theorem without the frame: {reason}"
                );
            }
            other => panic!("instruction {ordinal} took credit without the frame: {other:?}"),
        }
    }
    assert!(!report.emitted_opcode_inventory().is_promotable());
}

#[test]
fn complete_input_digest_and_cache_key_separate_source_presence_and_mutations() {
    let (machine, (source, _)) = fixture("identity");
    let raw = aarch64_verifier_input_digest(&machine).unwrap();
    assert_eq!(
        raw,
        aarch64_verifier_input_digest_with_lir(&machine, None).unwrap()
    );
    let bound = aarch64_verifier_input_digest_with_lir(&machine, Some(&source)).unwrap();
    assert_ne!(raw, bound);
    assert_eq!(
        bound,
        aarch64_verifier_input_digest_with_lir(&machine, Some(&source.clone())).unwrap()
    );
    let key = |digest| {
        JitCertCacheKey::new_for_verified_function_digests(
            &[1; 32],
            &digest,
            b"same fixups",
            b"same compiler policy",
            &[2; 32],
        )
    };
    assert_ne!(key(raw), key(bound));
    let mut changed = source.clone();
    changed
        .blocks
        .get_mut(&changed.entry_block)
        .unwrap()
        .instructions[0]
        .opcode = Opcode::Iconst {
        imm: 43,
        ty: trust_cg_lower::Type::I64,
    };
    let mut signature = source.clone();
    signature.signature.returns = vec![trust_cg_lower::Type::I32];
    let mut metadata = source.clone();
    metadata
        .value_types
        .insert(Value(0), trust_cg_lower::Type::I32);
    for mutant in [changed, signature, metadata] {
        let digest = aarch64_verifier_input_digest_with_lir(&machine, Some(&mutant)).unwrap();
        assert_ne!(bound, digest);
        assert_ne!(key(bound), key(digest));
    }
}

#[test]
fn raw_source_absence_preserves_default_policy_and_cannot_gain_frame_authority() {
    without_tools(|| {
        let (machine, _) = fixture("raw");
        let machines = [machine];
        let inputs = Aarch64JitInputs::raw(&machines);
        assert!(inputs.source(0).is_none());
        assert!(inputs.source_verifier().is_none());
        for ambient in ["off", "warn"] {
            trust_cg_process_env::with_env_overrides(&[("TCG_PROVENANCE_XCHECK", ambient)], || {
                let verifier = FunctionVerifier::new();
                let request = inputs.capture_request(&verifier);
                let report = verifier.verify_with_request(&machines[0], None, &request);
                assert!(report.report().precondition_failure.is_none());
                assert!(report.matches_aarch64_input(&machines[0], None));
                assert_no_frame_authority(report.report());
            });
        }
    });
}

#[test]
fn unchecked_entry_preserves_raw_empty_input_refusal_without_source_walk() {
    let (_, source) = fixture("unused");
    let jit = JitCompiler::new(JitConfig {
        verify: false,
        ..Default::default()
    });
    let raw = jit
        .compile_raw(&[], &HashMap::new())
        .expect_err("empty input refuses");
    let module = trust_ir::Module::new("unchecked-source");
    let paired = jit
        .compile_with_lir_and_encoding_metrics(
            &[],
            &[source],
            &module,
            &module,
            &HashMap::new(),
            false,
            None,
        )
        .expect_err("empty input still refuses");
    assert_eq!(raw.to_string(), paired.to_string());
    assert!(!matches!(paired, JitError::LirSourceCountMismatch { .. }));
}

#[test]
fn original_module_changes_cannot_reuse_a_lir_only_cache_key_or_receipt() {
    without_tools(|| {
        let (machine, source) = fixture("unchanged_machine_and_lir");
        let machines = [machine];
        let sources = [source];
        let module = trust_ir::Module::new("original");
        let mut changed = module.clone();
        changed.func_types.push(trust_ir::FuncTy {
            params: vec![trust_ir::Ty::PtrMut(Box::new(trust_ir::Ty::F64))],
            returns: vec![],
            abi: None,
            is_vararg: false,
        });
        let old = Aarch64JitInputs::with_replayed_lir(&machines, &sources).unwrap();
        let bound =
            Aarch64JitInputs::with_replayed_source_modules(&machines, &sources, &module, &module)
                .unwrap();
        let mutated =
            Aarch64JitInputs::with_replayed_source_modules(&machines, &sources, &changed, &module)
                .unwrap();
        assert_ne!(
            old.verifier_input_digest(0).unwrap(),
            bound.verifier_input_digest(0).unwrap()
        );
        assert_ne!(
            bound.verifier_input_digest(0).unwrap(),
            mutated.verifier_input_digest(0).unwrap()
        );
        let verifier = bound.source_verifier().unwrap();
        let request = bound.capture_request(verifier);
        let report = bound.verify(0, verifier, &request);
        assert!(bound.matches_report(0, &report));
        assert!(!old.matches_report(0, &report));
        assert!(!mutated.matches_report(0, &report));
        assert!(
            !report.reusable_for(&request),
            "input custody supplies no missing proof"
        );
    });
}
