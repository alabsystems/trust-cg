// Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use crate::aarch64_affine_lowering::check_aarch64_trust_ir_affine_bytes;
use crate::aarch64_conditional_frame::{
    ConditionalFramePremise, conditional_static_frame_with_body,
};
use crate::aarch64_static_frame::{
    SavedFrameRegister, StaticFrameEnvelopeCandidates, StaticFrameLayoutClaim,
    check_static_frame_envelopes,
};
use trust_cg_ir::regs::{PReg, X0};
use trust_cg_ir::{AArch64Opcode as Op, MachFunction, MachInst, MachOperand as O, SpecialReg};
use trust_ir_build::ModuleBuilder;

struct Ordinary {
    module: trust_ir::Module,
    lir: Vec<trust_cg_lower::Function>,
    machine: MachFunction,
    image: Vec<u8>,
    claim: StaticFrameLayoutClaim,
    candidates: StaticFrameEnvelopeCandidates,
}

impl Ordinary {
    fn new() -> Self {
        Self::with_extra_original_call(false)
    }
    fn with_extra_original_call(extra: bool) -> Self {
        let host = trust_cg_codegen::CoreHostJitTarget::detect().unwrap();
        let mut m = ModuleBuilder::new_with_target_info(
            "two_call_frame",
            host.trust_ir_target_info().clone(),
        );
        let sig = m.add_func_type(vec![trust_ir::Ty::U64], vec![trust_ir::Ty::U64]);
        let mut f = m.function("identity_leaf", sig);
        f.set_linkage(trust_ir::Linkage::Internal);
        let b = f.create_block();
        let arg = f.add_block_param(b, trust_ir::Ty::U64);
        f.switch_to_block(b);
        f.ret(vec![arg]);
        let leaf = f.build();
        let mut f = m.function("two_call_frame", sig);
        let b = f.create_block();
        let arg = f.add_block_param(b, trust_ir::Ty::U64);
        f.switch_to_block(b);
        let first = f.call(leaf, vec![arg]);
        let second = f.call(leaf, vec![first]);
        if extra {
            let _ = f.call(leaf, vec![arg]);
        }
        f.ret(vec![second]);
        f.build();
        let module = m.build().unwrap();
        let (lir, _) =
            trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
                &module,
                trust_cg_lower::GuardCarrierArch::AArch64,
                trust_cg_lower::TlsDialect::MachOTlv,
                &crate::license_test_support::permit_unlicensed(),
            )
            .unwrap();
        let lir = lir.into_iter().map(|(f, _)| f).collect();
        let signature = trust_cg_ir::function::Signature::new(
            vec![trust_cg_ir::function::Type::I64],
            vec![trust_cg_ir::function::Type::I64],
        );
        let mut machine = MachFunction::new("two_call_frame".into(), signature);
        let block = machine.entry;
        let pair = |opcode, a, b, offset| {
            MachInst::new(
                opcode,
                vec![
                    O::PReg(PReg::new(a)),
                    O::PReg(PReg::new(b)),
                    O::Special(SpecialReg::SP),
                    O::Imm(offset),
                ],
            )
        };
        machine.insts = vec![
            pair(Op::StpPreIndex, 26, 25, -80),
            pair(Op::StpRI, 24, 23, 16),
            pair(Op::StpRI, 22, 21, 32),
            pair(Op::StpRI, 20, 19, 48),
            pair(Op::StpRI, 29, 30, 64),
            MachInst::new(
                Op::AddRI,
                vec![
                    O::PReg(PReg::new(29)),
                    O::Special(SpecialReg::SP),
                    O::Imm(64),
                ],
            ),
            MachInst::with_flags(
                Op::Bl,
                vec![O::Symbol("identity_leaf".into())],
                Op::Bl
                    .default_flags()
                    .union(trust_cg_ir::InstFlags::EXACT_MODULE_CALL),
            ),
            MachInst::with_flags(
                Op::Bl,
                vec![O::Symbol("identity_leaf".into())],
                Op::Bl
                    .default_flags()
                    .union(trust_cg_ir::InstFlags::EXACT_MODULE_CALL),
            ),
            pair(Op::LdpRI, 29, 30, 64),
            pair(Op::LdpRI, 20, 19, 48),
            pair(Op::LdpRI, 22, 21, 32),
            pair(Op::LdpRI, 24, 23, 16),
            pair(Op::LdpPostIndex, 26, 25, 80),
            MachInst::new(Op::Ret, vec![O::PReg(PReg::new(30))]).with_implicit_uses(&[X0]),
        ];
        machine.blocks[block.0 as usize].insts = (0..14).map(InstId).collect();
        let mut image = Vec::new();
        for (i, inst) in machine.insts.iter().enumerate() {
            let word = match i {
                6 => 0x94000008u32,
                7 => 0x94000007u32,
                13 => 0xd65f03c0u32,
                _ => crate::aarch64_memory_effect::memory_effect_word(inst)
                    .or_else(|| {
                        crate::aarch64_instruction_word_proofs::instruction_word(inst)
                            .map(|w| w.word)
                    })
                    .unwrap(),
            };
            image.extend_from_slice(&word.to_le_bytes());
        }
        // An actual checked sixteen-byte leaf frame, not an assumed ABI
        // or arbitrary externally supplied effect summary.
        for word in [0xa9bf7bfdu32, 0x910003fd, 0xa8c17bfd, 0xd65f03c0] {
            image.extend_from_slice(&word.to_le_bytes());
        }
        let claim = StaticFrameLayoutClaim {
            saved_pairs: [[29, 30], [19, 20], [21, 22], [23, 24], [25, 26]]
                .map(|p| p.map(SavedFrameRegister::X))
                .to_vec(),
            callee_saved_bytes: 80,
            stack_slot_bytes: 0,
            outgoing_argument_bytes: 0,
            total_bytes: 80,
            uses_frame_pointer: true,
            dynamic_allocation: false,
            red_zone: false,
            slot_fp_offsets: vec![],
        };
        let candidates = StaticFrameEnvelopeCandidates {
            prologue: (0..6).map(InstId).collect(),
            epilogues: vec![(8..14).map(InstId).collect()],
        };
        Self {
            module,
            lir,
            machine,
            image,
            claim,
            candidates,
        }
    }
    fn geometry(&self) -> CheckedStaticFrameEnvelopes<'_> {
        check_static_frame_envelopes(
            &self.lir[1],
            &self.machine,
            &self.image[..56],
            &self.claim,
            &self.candidates,
            &[],
        )
        .unwrap()
    }
    #[cfg(target_arch = "aarch64")]
    fn certify_original_leaf(&mut self) {
        use sha2::{Digest, Sha256};
        use trust_ir::proof::{
            IslandEnvironment, ProofDigest, ProofLineageId, ProofTransform, ProofTransformStage,
            SourceDefinitionRef, encode_island_declarations_v1,
        };
        use trust_ir_build::clean_kernel::{BinderInfo, Declaration, Expr, Name};
        // Independent source, not a denotation recovered from machine words.
        let bytes = encode_island_declarations_v1(&[Declaration::Definition {
            name: Name::from_string("Source.frame_identity"),
            level_params: vec![],
            type_: Expr::arrow(Expr::const_str("Nat"), Expr::const_str("Nat")),
            value: Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), Expr::bvar(0)),
            is_reducible: true,
        }])
        .unwrap();
        let id = self.module.functions[0].id;
        let (_, obligation, certificate) =
            trust_ir_build::certify_identity_lineage_rung_island_bound(
                &self.module,
                ProofLineageId::new(0),
                trust_ir::value::ProofId::new(0),
                ProofTransform::new(
                    ProofTransformStage::Frontend,
                    "defined-frame-call",
                    "original-identity",
                    "1",
                ),
                id,
                &IslandEnvironment::new(bytes.clone()),
                SourceDefinitionRef {
                    decl: "Source.frame_identity".into(),
                    closure_digest: ProofDigest::sha256(Sha256::digest(&bytes).into()),
                },
            )
            .expect("independent original identity equals actual leaf IR");
        self.module.functions[0].body_gate = Some(trust_ir::BodyGate::Gated {
            authority: "clean-kernel-tv".into(),
            evidence: Some(trust_ir::GateEvidence {
                obligation: obligation.id,
                body_digest: self.module.function_body_digest(id).unwrap(),
            }),
        });
        self.module.proof_obligations.push(obligation);
        self.module.proof_certificates.push(certificate);
        let report = trust_ir_build::validate_module_with_config(
            &self.module,
            &trust_ir_build::ValidationConfig::pinned()
                .with_bound_certificates(true)
                .with_source_bound_certificates(true)
                .with_gate_evidence(true),
        );
        assert!(
            report.is_ok(),
            "ordinary validator must replay the actual bound original-source certificate: {:?}",
            report.errors()
        );
    }
}

#[test]
fn checked_two_call_eighty_byte_frame_composes_real_leaf_footprints() {
    let fixture = Ordinary::new();
    let geometry = fixture.geometry();
    let leaf = check_aarch64_trust_ir_affine_bytes(
        &fixture.module,
        0,
        &fixture.lir[0],
        &fixture.image[56..],
    )
    .unwrap();
    let sites: Vec<_> = fixture.lir[1].blocks[&fixture.lir[1].entry_block]
        .instructions
        .iter()
        .enumerate()
        .filter_map(|(i, n)| matches!(n.opcode, Opcode::Call { .. }).then_some(i))
        .collect();
    assert_eq!(sites.len(), 2);
    let calls = [
        FrameBodyCall {
            instruction: InstId(6),
            lir_instruction: sites[0],
            callee_offset: 56,
            callee: &leaf,
        },
        FrameBodyCall {
            instruction: InstId(7),
            lir_instruction: sites[1],
            callee_offset: 56,
            callee: &leaf,
        },
    ];
    let body = check_frame_body(&geometry, &fixture.module, 1, &fixture.image, 0, &calls).unwrap();
    assert_eq!(body.required_entry_stack_bytes(), 96);
    let composed = conditional_static_frame_with_body(&body).unwrap();
    let exit = &composed.exits()[0];
    assert_eq!(
        exit.premises(),
        &[
            ConditionalFramePremise::EntrySpNonwrapping { frame_bytes: 96 },
            ConditionalFramePremise::EntrySpAlignment { bytes: 16 }
        ]
    );
    assert_eq!(exit.obligation().preconditions.len(), 2);
    assert!(!exit.obligation().is_reconstructed());
    assert!(
        !exit
            .obligation()
            .aarch64_expr
            .to_string()
            .contains("resume_memory")
    );
    let mut env = crate::smt::EvalEnv::default();
    env.insert("frame_entry_sp".into(), 80);
    assert_eq!(
        exit.obligation().preconditions[0].eval(&env),
        crate::smt::EvalResult::Bool(false)
    );
    env.insert("frame_entry_sp".into(), 96);
    assert_eq!(
        exit.obligation().preconditions[0].eval(&env),
        crate::smt::EvalResult::Bool(true)
    );
}

fn challenge(fixture: &Ordinary, edit: impl FnOnce(&mut Vec<FrameBodyCall<'_, '_>>)) -> Result<()> {
    let geometry = fixture.geometry();
    let leaf = check_aarch64_trust_ir_affine_bytes(
        &fixture.module,
        0,
        &fixture.lir[0],
        &fixture.image[56..],
    )
    .map_err(|e| inconsistent(format!("callee endpoint: {e}")))?;
    let sites: Vec<_> = fixture.lir[1].blocks[&fixture.lir[1].entry_block]
        .instructions
        .iter()
        .enumerate()
        .filter_map(|(i, n)| matches!(n.opcode, Opcode::Call { .. }).then_some(i))
        .collect();
    let mut calls = vec![
        FrameBodyCall {
            instruction: InstId(6),
            lir_instruction: sites[0],
            callee_offset: 56,
            callee: &leaf,
        },
        FrameBodyCall {
            instruction: InstId(7),
            lir_instruction: sites[1],
            callee_offset: 56,
            callee: &leaf,
        },
    ];
    edit(&mut calls);
    check_frame_body(&geometry, &fixture.module, 1, &fixture.image, 0, &calls).map(|_| ())
}

#[test]
fn frame_body_refuses_wrong_call_binding_target_origin_and_callee_bytes() {
    let fixture = Ordinary::new();
    challenge(&fixture, |_| {}).unwrap();
    assert!(
        challenge(&fixture, |calls| {
            calls.pop();
        })
        .is_err()
    );
    assert!(challenge(&fixture, |calls| calls[1].instruction = InstId(6)).is_err());
    assert!(
        challenge(&fixture, |calls| calls[1].lir_instruction =
            calls[0].lir_instruction)
        .is_err()
    );
    assert!(challenge(&fixture, |calls| calls[0].lir_instruction = usize::MAX).is_err());
    assert!(challenge(&fixture, |calls| calls[0].callee_offset = 60).is_err());
    let mut fixture = Ordinary::new();
    fixture.image[24..28].copy_from_slice(&0x94000007u32.to_le_bytes());
    assert!(
        challenge(&fixture, |_| {})
            .unwrap_err()
            .to_string()
            .contains("BL target")
    );
    let mut fixture = Ordinary::new();
    fixture.image[56] ^= 1;
    assert!(
        challenge(&fixture, |_| {})
            .unwrap_err()
            .to_string()
            .contains("callee endpoint")
    );
    let mut fixture = Ordinary::new();
    let entry = fixture.lir[1].entry_block;
    fixture.lir[1]
        .trust_ir_origins
        .get_mut(&entry)
        .unwrap()
        .iter_mut()
        .for_each(|o| *o = None);
    assert!(
        challenge(&fixture, |_| {})
            .unwrap_err()
            .to_string()
            .contains("original call origin")
    );
    let mut fixture = Ordinary::new();
    let entry = fixture.lir[1].entry_block;
    let last = fixture.module.functions[1].blocks[0].body.len() - 1;
    fixture.lir[1]
        .trust_ir_origins
        .get_mut(&entry)
        .unwrap()
        .iter_mut()
        .for_each(|o| *o = Some(trust_cg_ir::TrustIrInstId(last as u32)));
    assert!(
        challenge(&fixture, |_| {})
            .unwrap_err()
            .to_string()
            .contains("stale original call")
    );
    let mut fixture = Ordinary::new();
    let entry = fixture.lir[1].entry_block;
    let calls: Vec<_> = fixture.lir[1].blocks[&entry]
        .instructions
        .iter()
        .enumerate()
        .filter_map(|(i, n)| matches!(n.opcode, Opcode::Call { .. }).then_some(i))
        .collect();
    let origins = fixture.lir[1].trust_ir_origins.get_mut(&entry).unwrap();
    origins[calls[1]] = origins[calls[0]];
    assert!(
        challenge(&fixture, |_| {})
            .unwrap_err()
            .to_string()
            .contains("duplicate original call origin")
    );
    let mut fixture = Ordinary::with_extra_original_call(true);
    assert!(trust_ir_build::validate_module(&fixture.module).is_empty());
    let entry = fixture.lir[1].entry_block;
    let third = fixture.lir[1].blocks[&entry]
        .instructions
        .iter()
        .enumerate()
        .filter_map(|(i, n)| matches!(n.opcode, Opcode::Call { .. }).then_some(i))
        .nth(2)
        .unwrap();
    fixture.lir[1]
        .blocks
        .get_mut(&entry)
        .unwrap()
        .instructions
        .remove(third);
    fixture.lir[1]
        .trust_ir_origins
        .get_mut(&entry)
        .unwrap()
        .remove(third);
    assert!(
        challenge(&fixture, |_| {})
            .unwrap_err()
            .to_string()
            .contains("original call has no paired")
    );
    let mut fixture = Ordinary::new();
    fixture.image.splice(64..64, 0xd2800020u32.to_le_bytes()); // MOV X0,#1, valid ISA but wrong callee result.
    assert!(
        challenge(&fixture, |_| {})
            .unwrap_err()
            .to_string()
            .contains("callee endpoint")
    );
    let mut fixture = Ordinary::new();
    fixture.image.splice(64..64, 0xf9000000u32.to_le_bytes()); // STR X0,[X0], outside private leaf stack.
    assert!(
        challenge(&fixture, |_| {})
            .unwrap_err()
            .to_string()
            .contains("callee endpoint")
    );
}

#[test]
fn frame_body_decoded_w29_and_wsp_refuse_even_matching_words() {
    for (inst, word) in [
        (
            MachInst::new(
                Op::MOVWrr,
                vec![O::PReg(PReg::new(29)), O::PReg(PReg::new(0))],
            ),
            0x2a0003fdu32,
        ),
        (
            MachInst::new(
                Op::AddRI,
                vec![O::PReg(PReg::new(63)), O::PReg(PReg::new(63)), O::Imm(0)],
            ),
            0x110003ffu32,
        ),
        (
            MachInst::new(
                Op::AddRI,
                vec![
                    O::Special(SpecialReg::SP),
                    O::Special(SpecialReg::SP),
                    O::Imm(0),
                ],
            ),
            0x910003ffu32,
        ),
    ] {
        let mut fixture = Ordinary::new();
        fixture.machine.insts[6] = inst;
        fixture.image[24..28].copy_from_slice(&word.to_le_bytes());
        let error = challenge(&fixture, |_| {}).unwrap_err().to_string();
        assert!(error.contains("body writes"), "{word:x}: {error}");
    }
}

#[test]
fn frame_body_refuses_caller_memory_control_escape_and_nominal_only_calls() {
    let mut fixture = Ordinary::new();
    fixture.machine.insts[6]
        .flags
        .remove(trust_cg_ir::InstFlags::EXACT_MODULE_CALL);
    assert!(
        challenge(&fixture, |_| {})
            .unwrap_err()
            .to_string()
            .contains("exact module callee")
    );
    let mut fixture = Ordinary::new();
    fixture.machine.insts[6].operands[0] = O::Symbol("different_leaf".into());
    assert!(
        challenge(&fixture, |_| {})
            .unwrap_err()
            .to_string()
            .contains("exact module callee")
    );
    let mut fixture = Ordinary::new();
    let store = MachInst::new(
        Op::StrRI,
        vec![O::PReg(PReg::new(0)), O::Special(SpecialReg::SP), O::Imm(0)],
    );
    assert_eq!(
        crate::aarch64_memory_effect::memory_effect_word(&store),
        Some(0xf90003e0)
    );
    fixture.machine.insts[6] = store;
    fixture.image[24..28].copy_from_slice(&0xf90003e0u32.to_le_bytes());
    assert!(challenge(&fixture, |_| {}).is_err());
    let mut fixture = Ordinary::new();
    fixture.machine.insts[6] = MachInst::new(Op::B, vec![O::Imm(-6)]);
    fixture.image[24..28].copy_from_slice(&0x17fffffau32.to_le_bytes());
    assert!(
        challenge(&fixture, |_| {})
            .unwrap_err()
            .to_string()
            .contains("escapes checked body")
    );
    let fixture = Ordinary::new();
    let geometry = fixture.geometry();
    let copy = fixture.image.clone();
    assert!(
        check_frame_body(&geometry, &fixture.module, 1, &copy, 0, &[])
            .unwrap_err()
            .to_string()
            .contains("exact immutable linked caller bytes")
    );
}

#[cfg(target_arch = "aarch64")]
#[test]
fn frame_body_native_two_call_frame_consumes_actual_linked_bytes() {
    use crate::aarch64_affine_lowering::DefinedAffineCallee;
    use crate::provenance_xcheck::ProvenanceXCheckMode;
    use trust_cg_codegen::jit::{JitCompiler, JitConfig};
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let mut fixture = Ordinary::new();
    fixture.certify_original_leaf();
    // Compile the certified original through the ordinary owner. Retain its
    // actual provenance and forced standard frame for the enforced capture.
    let (leaf_lir, lowering_proof) = trust_cg_lower::translate_function_with_license(
        &fixture.module.functions[0],
        &fixture.module,
        &trust_cg_lower::CodegenLicensePolicy::default(),
    )
    .unwrap();
    fixture.lir[0] = leaf_lir;
    let pipeline =
        trust_cg_codegen::pipeline::Pipeline::new(trust_cg_codegen::pipeline::PipelineConfig {
            opt_level: trust_cg_codegen::pipeline::OptLevel::O0,
            verify: false,
            target_triple: "aarch64-apple-darwin".into(),
            aarch64_force_frame_pointers: true,
            ..Default::default()
        });
    let (leaf_machine, _) = pipeline
        .prepare_function_with_metrics_and_trust_ir_module(
            &fixture.lir[0],
            Some(&lowering_proof),
            &fixture.module,
            &fixture.module.functions[0],
        )
        .unwrap();
    let buffer = JitCompiler::new(JitConfig {
        verify: false,
        ..JitConfig::default()
    })
    .compile_raw(
        &[fixture.machine.clone(), leaf_machine.clone()],
        &Default::default(),
    )
    .unwrap();
    let range = |name: &str| {
        buffer
            .function_ranges()
            .iter()
            .find(|(n, _)| n == name)
            .unwrap()
            .1
            .clone()
    };
    let caller_range = range("two_call_frame");
    let leaf_range = range("identity_leaf");
    let image = buffer.code_slice();
    let caller_offset = usize::try_from(caller_range.start).unwrap();
    let leaf_offset = usize::try_from(leaf_range.start).unwrap();
    let caller_bytes = &image[caller_offset..usize::try_from(caller_range.end).unwrap()];
    let leaf_bytes = &image[leaf_offset..usize::try_from(leaf_range.end).unwrap()];
    let geometry = check_static_frame_envelopes(
        &fixture.lir[1],
        &fixture.machine,
        caller_bytes,
        &fixture.claim,
        &fixture.candidates,
        &[],
    )
    .unwrap();
    let verifier = crate::FunctionVerifier::with_config(
        crate::lowering_proof::VerificationConfig::for_proof_promotion(),
    );
    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    let modules = crate::FunctionSourceModules::capture(&fixture.module, &fixture.module).unwrap();
    let captured = crate::resource_limits::run_on_proof_verifier_stack(
        "defined-frame-callee-original-capture",
        || {
            verifier.verify_with_request_and_modules(
                &leaf_machine,
                Some(&fixture.lir[0]),
                &modules,
                &request,
            )
        },
    );
    let summary = DefinedAffineCallee::bind(
        &modules,
        &request,
        &captured,
        fixture.module.functions[0].id,
        &fixture.lir[0],
        &leaf_machine,
        leaf_bytes,
    )
    .unwrap_or_else(|error| panic!("{error}: {:#?}", captured.report()));
    let leaf = summary
        .attach(
            &modules,
            &request,
            fixture.module.functions[0].id,
            &fixture.lir[0],
            leaf_bytes,
        )
        .unwrap();
    let sites: Vec<_> = fixture.lir[1].blocks[&fixture.lir[1].entry_block]
        .instructions
        .iter()
        .enumerate()
        .filter_map(|(i, n)| matches!(n.opcode, Opcode::Call { .. }).then_some(i))
        .collect();
    let calls = [
        FrameBodyCall::from_defined_callee(InstId(6), sites[0], leaf_offset, &leaf, &request)
            .unwrap(),
        FrameBodyCall::from_defined_callee(InstId(7), sites[1], leaf_offset, &leaf, &request)
            .unwrap(),
    ];
    let body =
        check_frame_body(&geometry, &fixture.module, 1, image, caller_offset, &calls).unwrap();
    assert_eq!(body.required_entry_stack_bytes(), 96);
    assert_eq!(summary.effects().required_private_stack_bytes(), 16);
    let composed = conditional_static_frame_with_body(&body).unwrap();
    assert_eq!(composed.exits()[0].premises().len(), 2);
    // Same settings cannot replace the original enforced request identity.
    let foreign_request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    assert!(
        FrameBodyCall::from_defined_callee(
            InstId(6),
            sites[0],
            leaf_offset,
            &leaf,
            &foreign_request
        )
        .is_err()
    );
    let argument = Arc::new(crate::smt::SmtExpr::var("frame_actual_argument", 64));
    // These are conditional return expressions, not proof that either call
    // executes or returns normally, or that caller registers carry these args.
    let first_result = body
        .instantiate_defined_call_result(
            InstId(6),
            &leaf,
            &request,
            std::slice::from_ref(&argument),
        )
        .unwrap()
        .unwrap();
    let result = body
        .instantiate_defined_call_result(InstId(7), &leaf, &request, &[first_result])
        .unwrap()
        .unwrap();
    assert!(
        body.instantiate_defined_call_result(
            InstId(6),
            &leaf,
            &foreign_request,
            std::slice::from_ref(&argument)
        )
        .is_err()
    );
    assert!(
        body.instantiate_defined_call_result(
            InstId(5),
            &leaf,
            &request,
            std::slice::from_ref(&argument)
        )
        .is_err()
    );
    assert!(
        body.instantiate_defined_call_result(InstId(6), &leaf, &request, &[])
            .is_err()
    );
    assert!(
        body.instantiate_defined_call_result(
            InstId(6),
            &leaf,
            &request,
            &[Arc::new(crate::smt::SmtExpr::var("wrong_width", 32))]
        )
        .is_err()
    );
    let reattached = summary
        .attach(
            &modules,
            &request,
            fixture.module.functions[0].id,
            &fixture.lir[0],
            leaf_bytes,
        )
        .unwrap();
    assert!(
        body.instantiate_defined_call_result(
            InstId(6),
            &reattached,
            &request,
            std::slice::from_ref(&argument)
        )
        .is_err(),
        "a separate attachment is not the borrowed call endpoint"
    );
    let wrong_target = [
        FrameBodyCall::from_defined_callee(InstId(6), sites[0], leaf_offset + 4, &leaf, &request)
            .unwrap(),
        FrameBodyCall::from_defined_callee(InstId(7), sites[1], leaf_offset, &leaf, &request)
            .unwrap(),
    ];
    assert!(
        check_frame_body(
            &geometry,
            &fixture.module,
            1,
            image,
            caller_offset,
            &wrong_target
        )
        .is_err(),
        "source-bearing callee cannot authorize a changed BL target"
    );
    // Mutate only the actual caller BL displacement. Rebind all immutable
    // byte borrows honestly; the unchanged source-certified callee and original
    // capture must not bless a different target in the caller's word stream.
    let mut changed_image = image.to_vec();
    let call_at = caller_offset + geometry.byte_offset(InstId(6)).unwrap();
    let word = u32::from_le_bytes(changed_image[call_at..call_at + 4].try_into().unwrap());
    changed_image[call_at..call_at + 4].copy_from_slice(&word.wrapping_add(1).to_le_bytes());
    let changed_geometry = check_static_frame_envelopes(
        &fixture.lir[1],
        &fixture.machine,
        &changed_image[caller_offset..usize::try_from(caller_range.end).unwrap()],
        &fixture.claim,
        &fixture.candidates,
        &[],
    )
    .unwrap();
    let unchanged_leaf = summary
        .attach(
            &modules,
            &request,
            fixture.module.functions[0].id,
            &fixture.lir[0],
            &changed_image[leaf_offset..usize::try_from(leaf_range.end).unwrap()],
        )
        .unwrap();
    let changed_calls = [
        FrameBodyCall::from_defined_callee(
            InstId(6),
            sites[0],
            leaf_offset,
            &unchanged_leaf,
            &request,
        )
        .unwrap(),
        FrameBodyCall::from_defined_callee(
            InstId(7),
            sites[1],
            leaf_offset,
            &unchanged_leaf,
            &request,
        )
        .unwrap(),
    ];
    let error = check_frame_body(
        &changed_geometry,
        &fixture.module,
        1,
        &changed_image,
        caller_offset,
        &changed_calls,
    )
    .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("actual BL target differs from checked callee"),
        "{error}"
    );
    // SAFETY: the original module, retained LIR, machine signature and
    // independently checked linked callees use the same C64-bit unsigned ABI.
    // existing JIT owner keeps the executable mapping alive for each call.
    let function = unsafe {
        buffer
            .get_fn_bound::<extern "C" fn(u64) -> u64>("two_call_frame")
            .unwrap()
    };
    for value in [i64::MIN, -4096, -1, 0, 1, 4096, i64::MAX].map(|value| value as u64) {
        let mut environment = crate::smt::EvalEnv::default();
        environment.insert("frame_actual_argument".into(), value);
        assert_eq!(result.try_eval(&environment).unwrap().as_u64(), value);
        assert_eq!((function.as_ref())(value), value);
    }
    println!(
        "FRAME_BODY_NATIVE_EXECUTION cases=7 caller_frame=80 callee_private=16 calls=2 independent_callee_source=true original_request_capture=true caller_source_result_proof=false native_authority=false"
    );
    println!(
        "DEFINED_FRAME_CALLEE_CAPTURE formal_rows={} original_capture={} caller_machine_promotion=false",
        captured.report().genuinely_verified_count(),
        captured.matches_request_capture(&request),
    );
    {
        // Evidence only, not a compiler/runtime policy control. A unique
        // test-owned directory avoids requiring an ambient output knob.
        let directory = tempfile::Builder::new()
            .prefix("trust-cg-frame-body-")
            .tempdir()
            .unwrap()
            .keep();
        std::fs::write(
            directory.join("original_core.tmbc"),
            trust_cg_codegen::pipeline::encode_tmbc(&fixture.module).unwrap(),
        )
        .unwrap();
        std::fs::write(
            directory.join("caller.lir.json"),
            serde_json::to_vec_pretty(&fixture.lir[1]).unwrap(),
        )
        .unwrap();
        std::fs::write(
            directory.join("callee.lir.json"),
            serde_json::to_vec_pretty(&fixture.lir[0]).unwrap(),
        )
        .unwrap();
        std::fs::write(directory.join("native-linked.bin"), image).unwrap();
        let query = composed.exits()[0].obligation();
        std::fs::write(
            directory.join("raw.smt2"),
            crate::ay_bridge::generate_smt2_query_raw(
                query,
                &crate::ay_bridge::AYConfig::default(),
            ),
        )
        .unwrap();
        std::fs::write(
            directory.join("image.smt2"),
            crate::ay_bridge::generate_lowered_queries(
                query,
                &crate::ay_bridge::AYConfig::default(),
            )
            .into_iter()
            .next()
            .expect("shared array-lowering image")
            .0,
        )
        .unwrap();
        std::fs::write(directory.join("scope.json"), serde_json::to_vec_pretty(&serde_json::json!({
            "caller_offset": caller_offset, "callee_offset": leaf_offset, "caller_frame_bytes":80,
            "callee_private_bytes":16, "entry_nonwrapping_bytes":96, "calls":2,
            "native_cases":7, "entry_numeric_premises":2,
            "independent_callee_source":true, "original_request_capture":true,
            "callee_formal_rows":captured.report().genuinely_verified_count(),
            "callee_machine_input_digest":summary.machine_input_digest(),
            "callee_code_digest":summary.code_digest(),
            "permissions_and_installation_authority":false, "source_result_refinement":false,
            "original_e1_provider_witness":false
        })).unwrap()).unwrap();
        println!(
            "FRAME_BODY_ARTIFACT_DIR={}",
            serde_json::to_string(&directory).unwrap()
        );
    }
}

#[cfg(target_arch = "aarch64")]
#[test]
fn frame_body_readonly_leaf_requires_real_replay_and_exact_linked_endpoints() {
    use crate::provenance_xcheck::ProvenanceXCheckMode;
    use crate::read_only_replay::ReadOnlyCompilerRelations;
    use crate::source_bound_frame::bind_read_only_source;
    use crate::{FunctionVerifier, VerificationConfig};
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let mut fixture = Ordinary::new();
    fixture.module.func_types[0].params = vec![trust_ir::Ty::Ptr];
    for function in &mut fixture.module.functions {
        function.calling_conv = trust_ir::CallingConv::C;
        function.blocks[0].params[0].1 = trust_ir::Ty::Ptr;
    }
    let parameter = fixture.module.functions[0].blocks[0].params[0].0;
    let loaded = trust_ir::ValueId::new(100);
    let mut load = trust_ir::InstrNode::new(trust_ir::Inst::Load {
        ty: trust_ir::Ty::U64,
        ptr: parameter,
        volatile: false,
        align: Some(8),
    });
    load.results = vec![loaded];
    fixture.module.functions[0].blocks[0].body = vec![
        load,
        trust_ir::InstrNode::new(trust_ir::Inst::Return {
            values: vec![loaded],
        }),
    ];
    let result = fixture.module.functions[1].blocks[0].body[0].results[0];
    fixture.module.functions[1].blocks[0].body.truncate(1);
    fixture.module.functions[1].blocks[0]
        .body
        .push(trust_ir::InstrNode::new(trust_ir::Inst::Return {
            values: vec![result],
        }));
    let (lir, _) =
        trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
            &fixture.module,
            trust_cg_lower::GuardCarrierArch::AArch64,
            trust_cg_lower::TlsDialect::MachOTlv,
            &crate::license_test_support::permit_unlicensed(),
        )
        .unwrap();
    fixture.lir = lir.into_iter().map(|(f, _)| f).collect();
    fixture.machine.insts[7] = MachInst::new(Op::AddRI, vec![O::PReg(X0), O::PReg(X0), O::Imm(0)]);
    fixture.image[28..32].copy_from_slice(&0x91000000u32.to_le_bytes());
    let (_, proof_context) = trust_cg_lower::translate_function_with_license(
        &fixture.module.functions[0],
        &fixture.module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let pipeline =
        trust_cg_codegen::pipeline::Pipeline::new(trust_cg_codegen::pipeline::PipelineConfig {
            opt_level: trust_cg_codegen::pipeline::OptLevel::O0,
            verify: false,
            ..trust_cg_codegen::pipeline::PipelineConfig::for_target("aarch64-apple-darwin")
        });
    let (leaf, _) = pipeline
        .prepare_function_with_metrics_and_trust_ir_module(
            &fixture.lir[0],
            Some(&proof_context),
            &fixture.module,
            &fixture.module.functions[0],
        )
        .unwrap();
    let (code, fixups) = trust_cg_codegen::pipeline::encode_function_with_fixups(&leaf).unwrap();
    assert!(fixups.is_empty());
    fixture.image.truncate(56);
    fixture.image.extend_from_slice(&code);
    let source = bind_read_only_source(&fixture.module, 0, &fixture.lir[0]).unwrap();
    let relations = ReadOnlyCompilerRelations::bind(&source, &leaf, &fixture.image[56..]).unwrap();
    let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    let report = relations.replay(&request);
    let certificate = report.certificate().unwrap_or_else(|| {
        panic!(
            "all readonly relations must independently replay; no partial certificate: {:?}",
            report.outcomes()
        )
    });
    let sites: Vec<_> = fixture.lir[1].blocks[&fixture.lir[1].entry_block]
        .instructions
        .iter()
        .enumerate()
        .filter_map(|(i, n)| matches!(n.opcode, Opcode::Call { .. }).then_some(i))
        .collect();
    assert_eq!(sites.len(), 1);
    let calls = [ReadonlyFrameBodyCall::from_replayed_callee(
        InstId(6),
        sites[0],
        56,
        certificate,
        &request,
    )
    .unwrap()];
    let geometry = fixture.geometry();
    let body = check_readonly_frame_body(&geometry, &fixture.module, 1, &fixture.image, 0, &calls)
        .unwrap();
    // Formula transport from the REAL complete readonly replay and exact BL
    // owner, not a supplied result summary or native memory permission.
    let argument = Arc::new(crate::smt::SmtExpr::bv_const(0x1000, 64));
    let memory = Arc::new(crate::memory_proofs::encode_store_le(
        &crate::memory_proofs::zeroed_memory(),
        &argument,
        &crate::smt::SmtExpr::bv_const(0x8877665544332211, 64),
        8,
    ));
    let value_env = std::collections::HashMap::<String, u64>::new();
    let result = body
        .instantiate_readonly_call_result(
            InstId(6),
            certificate,
            &request,
            &[argument.clone()],
            &memory,
        )
        .unwrap();
    assert_eq!(
        result.try_eval(&value_env).unwrap(),
        crate::smt::EvalResult::Bv(0x8877665544332211)
    );
    fn nested_argument(depth: usize) -> crate::smt::SmtExpr {
        if depth == 0 {
            crate::smt::SmtExpr::bv_const(0, 64)
        } else {
            crate::smt::SmtExpr::uf(
                "candidate_argument",
                (0..8).map(|_| nested_argument(depth - 1)).collect(),
                crate::smt::SmtSort::BitVec(64),
            )
        }
    }
    let large = Arc::new(nested_argument(4));
    let transported = body
        .instantiate_readonly_call_result(InstId(6), certificate, &request, &[large], &memory)
        .unwrap();
    // A real shared input DAG stays within the one aggregate bound after
    // appearing in every byte-address calculation. Deep UF copies would not.
    assert!(crate::smt_raw_print::preflight_roots(&[transported.as_ref()]).is_ok());
    let changed = body
        .instantiate_readonly_call_result(
            InstId(6),
            certificate,
            &request,
            &[Arc::new(crate::smt::SmtExpr::bv_const(0x1008, 64))],
            &memory,
        )
        .unwrap();
    assert_ne!(
        changed.try_eval(&value_env).unwrap(),
        crate::smt::EvalResult::Bv(0x8877665544332211)
    );
    assert!(
        body.instantiate_readonly_call_result(
            InstId(7),
            certificate,
            &request,
            &[argument.clone()],
            &memory
        )
        .is_err()
    );
    for bad in [
        Arc::new(crate::smt::SmtExpr::BoolConst(false)),
        Arc::new(crate::smt::SmtExpr::bv_const(0, 32)),
        Arc::new(crate::smt::SmtExpr::BvAdd {
            lhs: Arc::new(crate::smt::SmtExpr::BoolConst(true)),
            rhs: argument.clone(),
            width: 64,
        }),
    ] {
        assert!(
            body.instantiate_readonly_call_result(
                InstId(6),
                certificate,
                &request,
                &[bad],
                &memory
            )
            .is_err()
        );
    }
    assert!(
        body.instantiate_readonly_call_result(InstId(6), certificate, &request, &[], &memory)
            .is_err()
    );
    assert!(
        body.instantiate_readonly_call_result(
            InstId(6),
            certificate,
            &request,
            &[argument.clone()],
            &Arc::new(crate::smt::SmtExpr::bv_const(0, 64))
        )
        .is_err()
    );
    assert_eq!(body.required_entry_stack_bytes(), 80);
    assert_eq!(
        conditional_static_frame_with_body(&body)
            .unwrap()
            .exits()
            .len(),
        1
    );
    let other_request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    assert!(
        body.instantiate_readonly_call_result(
            InstId(6),
            certificate,
            &other_request,
            &[argument],
            &memory
        )
        .is_err()
    );
    assert!(
        ReadonlyFrameBodyCall::from_replayed_callee(
            InstId(6),
            sites[0],
            56,
            certificate,
            &other_request
        )
        .is_err()
    );
    let wrong_target = [ReadonlyFrameBodyCall::from_replayed_callee(
        InstId(6),
        sites[0],
        60,
        certificate,
        &request,
    )
    .unwrap()];
    assert!(
        check_readonly_frame_body(
            &geometry,
            &fixture.module,
            1,
            &fixture.image,
            0,
            &wrong_target
        )
        .is_err()
    );
    assert!(
        check_readonly_frame_body(
            &geometry,
            &fixture.module.clone(),
            1,
            &fixture.image,
            0,
            &calls
        )
        .is_err()
    );
    assert!(
        check_readonly_frame_body(
            &geometry,
            &fixture.module,
            1,
            &fixture.image.clone(),
            0,
            &calls
        )
        .is_err()
    );
    let mut hidden_write = fixture.image[56..].to_vec();
    hidden_write[..4].copy_from_slice(&0xf9000000u32.to_le_bytes());
    assert!(ReadOnlyCompilerRelations::bind(&source, &leaf, &hidden_write).is_err());
    // Deliberately no native invocation or source-license claim: this fixture
    // qualifies the shared frame join and strict replay, not pointee access.
}
