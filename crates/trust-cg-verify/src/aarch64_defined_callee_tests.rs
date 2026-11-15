// Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use crate::FunctionVerifier;
use crate::lowering_proof::VerificationConfig;
use crate::smt::EvalEnv;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, encode_function_with_fixups};
use trust_ir::proof::{
    IslandEnvironment, ProofLineageId, ProofTransform, ProofTransformStage,
    encode_island_declarations_v1,
};
use trust_ir::{GateEvidence, Module, Ty};
use trust_ir_build::clean_kernel::{BinderInfo, Declaration, Expr, Name};
use trust_ir_build::{ModuleBuilder, ValidationConfig, certify_identity_lineage_rung_island_bound};

struct Fixture {
    module: Module,
    id: FuncId,
    lir: Function,
    machine: MachFunction,
    code: Vec<u8>,
}

impl Fixture {
    fn new(bits: u32, parameter: bool, value: u64) -> Self {
        Self::with_shape(bits, parameter, value, false, false)
    }

    fn with_shape(bits: u32, parameter: bool, value: u64, identity: bool, frame: bool) -> Self {
        let target =
            trust_cg_codegen::CoreHostJitTarget::detect().expect("ordinary actual host target");
        let mut builder = ModuleBuilder::new_with_target_info(
            "defined_callee_prerequisite",
            target.trust_ir_target_info().clone(),
        );
        let ty = if bits == 32 { Ty::U32 } else { Ty::U64 };
        let signature = builder.add_func_type(
            if parameter { vec![ty.clone()] } else { vec![] },
            vec![ty.clone()],
        );
        let mut f = builder.function("callee", signature);
        let entry = f.create_block();
        let x = parameter.then(|| f.add_block_param(entry, ty.clone()));
        f.switch_to_block(entry);
        let result = if identity {
            x.unwrap()
        } else {
            let k = f.iconst(ty.clone(), i128::from(value));
            if let Some(x) = x { f.add(ty, x, k) } else { k }
        };
        f.ret(vec![result]);
        let id = f.build();
        let mut module = builder.build().unwrap();
        // Independent source, authored before and separately from every
        // denotation, target word and certificate. Arithmetic really wraps.
        let nat = || Expr::const_str("Nat");
        let result = if identity {
            Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0))
        } else if parameter {
            Expr::lam(
                BinderInfo::Default,
                nat(),
                Expr::apps(
                    Expr::const_str("Nat.mod"),
                    [
                        Expr::apps(
                            Expr::const_str("Nat.add"),
                            [Expr::bvar(0), Expr::nat_lit(value)],
                        ),
                        Expr::nat_lit_u128(1u128 << bits),
                    ],
                ),
            )
        } else {
            Expr::nat_lit(value)
        };
        let declaration = Declaration::Definition {
            name: Name::from_string("Source.callee"),
            level_params: vec![],
            type_: if parameter {
                Expr::arrow(nat(), nat())
            } else {
                nat()
            },
            value: result,
            is_reducible: true,
        };
        let bytes = encode_island_declarations_v1(&[declaration]).unwrap();
        let definition = SourceDefinitionRef {
            decl: "Source.callee".into(),
            closure_digest: ProofDigest::sha256(Sha256::digest(&bytes).into()),
        };
        let (_, obligation, certificate) = certify_identity_lineage_rung_island_bound(
            &module,
            ProofLineageId::new(0),
            trust_ir::value::ProofId::new(0),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "defined-callee",
                "independent-source",
                "1",
            ),
            id,
            &IslandEnvironment::new(bytes),
            definition,
        )
        .expect("genuine independent source equals actual IR");
        let gate = GateEvidence {
            obligation: obligation.id,
            body_digest: module.function_body_digest(id).unwrap(),
        };
        module.functions[0].body_gate = Some(BodyGate::Gated {
            authority: "clean-kernel-tv".into(),
            evidence: Some(gate),
        });
        module.proof_obligations.push(obligation);
        module.proof_certificates.push(certificate);
        assert!(
            trust_ir_build::validate_module_with_config(
                &module,
                &ValidationConfig::pinned()
                    .with_bound_certificates(true)
                    .with_source_bound_certificates(true)
                    .with_gate_evidence(true)
            )
            .is_ok()
        );
        let (lir, proof) = trust_cg_lower::translate_function_with_license(
            &module.functions[0],
            &module,
            &trust_cg_lower::CodegenLicensePolicy::default(),
        )
        .unwrap();
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: OptLevel::O0,
            verify: false,
            target_triple: "aarch64-apple-darwin".into(),
            aarch64_force_frame_pointers: frame,
            ..Default::default()
        });
        let (machine, _) = pipeline
            .prepare_function_with_metrics_and_trust_ir_module(
                &lir,
                Some(&proof),
                &module,
                &module.functions[0],
            )
            .unwrap();
        let (code, fixups) = encode_function_with_fixups(&machine).unwrap();
        assert!(fixups.is_empty());
        Self {
            module,
            id,
            lir,
            machine,
            code,
        }
    }
    fn modules(&self) -> FunctionSourceModules<'_> {
        FunctionSourceModules::capture(&self.module, &self.module).unwrap()
    }
    fn captured(
        &self,
        verifier: &FunctionVerifier,
        request: &FunctionVerificationRequest,
    ) -> CapturedFunctionVerificationReport {
        verifier.verify_with_request_and_modules(
            &self.machine,
            Some(&self.lir),
            &self.modules(),
            request,
        )
    }
}

fn verifier() -> FunctionVerifier {
    FunctionVerifier::with_config(VerificationConfig::for_proof_promotion())
}

#[test]
fn defined_callee_actual_source_constants_replay_and_streaming_summary() {
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let verifier = verifier();
    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    for value in [0, 7, 42, 65_537] {
        let fixture = Fixture::new(64, false, value);
        // The actual qualified reader and original capture survive the same
        // maintained large-stack transport used by the production compiler.
        // No mock checker, fresh request or private worker budget is installed.
        let clone = request.clone();
        let captured = crate::resource_limits::run_on_proof_verifier_stack(
            "defined-callee-actual-capture-worker",
            || fixture.captured(&verifier, &clone),
        );
        assert!(captured.matches_request_capture(&request));
        let summary = DefinedAffineCallee::bind(
            &fixture.modules(),
            &request,
            &captured,
            fixture.id,
            &fixture.lir,
            &fixture.machine,
            &fixture.code,
        )
        .unwrap_or_else(|e| panic!("constant {value}: {e}; report={:#?}", captured.report()));
        assert_eq!(
            summary.result_type(),
            Some(DefinedCalleeScalarType::BitVec(64))
        );
        assert!(summary.estimated_payload_bytes() >= std::mem::size_of::<DefinedAffineCallee>());
        let Fixture {
            module,
            id,
            lir,
            machine,
            code,
        } = fixture;
        drop(machine); // The summary retains no allocated machine graph.
        let modules = FunctionSourceModules::capture(&module, &module).unwrap();
        let attached = summary
            .attach(&modules, &request.clone(), id, &lir, &code)
            .unwrap();
        let result = attached.instantiate_result(&[]).unwrap().unwrap();
        assert_eq!(
            result.try_eval(&EvalEnv::default()).unwrap().as_u64(),
            value
        );
        assert!(matches!(
            summary.effects(),
            DefinedCalleeEffects {
                private_stack_bytes: 0 | 16
            }
        ));
        println!(
            "DEFINED_CALLEE_CONSTANT value={value} code_sha256={:x} genuine={} stack_requirement={} native_credit=false",
            Sha256::digest(&code),
            captured.report().genuinely_verified_count(),
            summary.effects().required_private_stack_bytes()
        );
    }
}

#[test]
fn defined_callee_actual_parameter_affine_relation_wraps_and_shares_arguments() {
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let verifier = verifier();
    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    for bits in [32, 64] {
        let fixture = Fixture::new(bits, true, 3);
        let captured = fixture.captured(&verifier, &request);
        let modules = fixture.modules();
        let summary = DefinedAffineCallee::bind(
            &modules,
            &request,
            &captured,
            fixture.id,
            &fixture.lir,
            &fixture.machine,
            &fixture.code,
        )
        .unwrap_or_else(|e| panic!("i{bits}: {e}; report={:#?}", captured.report()));
        let attached = summary
            .attach(&modules, &request, fixture.id, &fixture.lir, &fixture.code)
            .unwrap();
        let argument = Arc::new(E::var("actual_argument", bits));
        let result = attached
            .instantiate_result(std::slice::from_ref(&argument))
            .unwrap()
            .unwrap();
        let mask = if bits == 32 {
            u32::MAX as u64
        } else {
            u64::MAX
        };
        for input in [0, 1, 253, mask - 2, mask - 1, mask] {
            let mut env = EvalEnv::default();
            env.insert("actual_argument".into(), input);
            assert_eq!(
                result.try_eval(&env).unwrap().as_u64(),
                input.wrapping_add(3) & mask
            );
        }
        let E::BvAdd { rhs, .. } = result.as_ref() else {
            panic!("finite affine sum");
        };
        assert!(Arc::ptr_eq(rhs, &argument));
        let substituted = attached
            .substitute_scalar(&[ScalarValue::Integer {
                bits,
                value: Affine::constant(mask, mask),
            }])
            .unwrap();
        assert_eq!(substituted.unwrap().as_constant(), Some(2));
        println!(
            "DEFINED_CALLEE_AFFINE bits={bits} code_sha256={:x} actual_source=true formal_rows={} native_credit=false",
            Sha256::digest(&fixture.code),
            captured.report().genuinely_verified_count()
        );
    }
}

#[test]
fn defined_callee_wrong_request_source_body_lir_bytes_and_abi_refuse() {
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let verifier = verifier();
    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    let fixture = Fixture::new(64, false, 42);
    let modules = fixture.modules();
    let captured = fixture.captured(&verifier, &request);
    let bind = |m: &FunctionSourceModules<'_>,
                r: &FunctionVerificationRequest,
                id,
                lir: &Function,
                machine: &MachFunction,
                code: &[u8]| {
        DefinedAffineCallee::bind(m, r, &captured, id, lir, machine, code)
    };
    let summary = bind(
        &modules,
        &request,
        fixture.id,
        &fixture.lir,
        &fixture.machine,
        &fixture.code,
    )
    .unwrap();
    let other_request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    assert!(!captured.matches_request_capture(&other_request));
    assert!(captured.matches_request_capture(&request.clone()));
    assert!(matches!(
        bind(
            &modules,
            &other_request,
            fixture.id,
            &fixture.lir,
            &fixture.machine,
            &fixture.code
        ),
        Err(DefinedAffineCalleeError::RequestCapture)
    ));
    assert!(
        summary
            .attach(
                &modules,
                &other_request,
                fixture.id,
                &fixture.lir,
                &fixture.code
            )
            .is_err()
    );
    assert!(
        bind(
            &modules,
            &request,
            FuncId::new(99),
            &fixture.lir,
            &fixture.machine,
            &fixture.code
        )
        .is_err()
    );
    let other = Fixture::new(64, false, 43);
    assert!(
        bind(
            &modules,
            &request,
            fixture.id,
            &fixture.lir,
            &fixture.machine,
            &other.code
        )
        .is_err()
    );
    let mut machine = fixture.machine.clone();
    machine.signature.returns.clear();
    assert!(
        bind(
            &modules,
            &request,
            fixture.id,
            &fixture.lir,
            &machine,
            &fixture.code
        )
        .is_err()
    );
    let mut lir = fixture.lir.clone();
    lir.name.push_str("_wrong");
    assert!(
        bind(
            &modules,
            &request,
            fixture.id,
            &lir,
            &fixture.machine,
            &fixture.code
        )
        .is_err()
    );
    let mut lir = fixture.lir.clone();
    lir.abi_sret_param = Some(trust_cg_lower::function::AbiSretParam { param_index: 0 });
    assert!(matches!(
        bind(
            &modules,
            &request,
            fixture.id,
            &lir,
            &fixture.machine,
            &fixture.code
        ),
        Err(DefinedAffineCalleeError::MachineAbi)
    ));
    let mut foreign = fixture.module.clone();
    foreign.name.push_str("_foreign");
    let foreign = FunctionSourceModules::capture(&foreign, &foreign).unwrap();
    assert!(
        bind(
            &foreign,
            &request,
            fixture.id,
            &fixture.lir,
            &fixture.machine,
            &fixture.code
        )
        .is_err()
    );
    assert!(
        summary
            .attach(&foreign, &request, fixture.id, &fixture.lir, &fixture.code)
            .is_err()
    );
    let lowered = fixture.module.clone();
    let lowered = FunctionSourceModules::capture(&fixture.module, &lowered).unwrap();
    assert!(matches!(
        bind(
            &lowered,
            &request,
            fixture.id,
            &fixture.lir,
            &fixture.machine,
            &fixture.code
        ),
        Err(DefinedAffineCalleeError::ModuleEndpoints)
    ));
    let mut source_none = fixture.module.clone();
    let ProofEvidence::CleanCic {
        kernel_recheck: Some(recheck),
        ..
    } = &mut source_none.proof_certificates[0].evidence
    else {
        panic!("actual source proof");
    };
    recheck.binding.as_mut().unwrap().source = None;
    let source_none = FunctionSourceModules::capture(&source_none, &source_none).unwrap();
    assert!(matches!(
        bind(
            &source_none,
            &request,
            fixture.id,
            &fixture.lir,
            &fixture.machine,
            &fixture.code
        ),
        Err(DefinedAffineCalleeError::MissingSourceBinding)
    ));
    let mut wrong_source = fixture.module.clone();
    let ProofEvidence::CleanCic {
        kernel_recheck: Some(recheck),
        ..
    } = &mut wrong_source.proof_certificates[0].evidence
    else {
        panic!("actual source proof");
    };
    recheck
        .binding
        .as_mut()
        .unwrap()
        .source
        .as_mut()
        .unwrap()
        .decl = "Source.missing".into();
    assert!(
        !trust_ir_build::validate_module_with_config(
            &wrong_source,
            &ValidationConfig::pinned()
                .with_bound_certificates(true)
                .with_source_bound_certificates(true)
                .with_gate_evidence(true)
        )
        .is_ok()
    );
    assert!(
        summary
            .attach(&modules, &request, fixture.id, &fixture.lir, &fixture.code)
            .is_ok()
    );
}

#[test]
fn defined_callee_noformal_and_structural_return_do_not_mint_summary() {
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let fixture = Fixture::new(64, false, 37);
    let evaluation_verifier = FunctionVerifier::with_config(VerificationConfig::default());
    let request = evaluation_verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    let captured = fixture.captured(&evaluation_verifier, &request);
    assert!(matches!(
        DefinedAffineCallee::bind(
            &fixture.modules(),
            &request,
            &captured,
            fixture.id,
            &fixture.lir,
            &fixture.machine,
            &fixture.code
        ),
        Err(DefinedAffineCalleeError::FormalReport)
    ));
    let verifier = verifier();
    let off = verifier.capture_request_with_mode(ProvenanceXCheckMode::Off);
    let captured = fixture.captured(&verifier, &off);
    assert!(matches!(
        DefinedAffineCallee::bind(
            &fixture.modules(),
            &off,
            &captured,
            fixture.id,
            &fixture.lir,
            &fixture.machine,
            &fixture.code
        ),
        Err(DefinedAffineCalleeError::RequestCapture)
    ));
    let identity = Fixture::with_shape(64, true, 0, true, false);
    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    let captured = identity.captured(&verifier, &request);
    assert_eq!(captured.report().genuinely_verified_count(), 0);
    assert!(matches!(
        DefinedAffineCallee::bind(
            &identity.modules(),
            &request,
            &captured,
            identity.id,
            &identity.lir,
            &identity.machine,
            &identity.code
        ),
        Err(DefinedAffineCalleeError::FormalReport)
    ));
}

#[test]
fn defined_callee_actual_standard_frame_retains_conditional_storage_requirement() {
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let verifier = verifier();
    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    let fixture = Fixture::with_shape(64, false, 37, false, true);
    let modules = fixture.modules();
    let captured = fixture.captured(&verifier, &request);
    let summary = DefinedAffineCallee::bind(
        &modules,
        &request,
        &captured,
        fixture.id,
        &fixture.lir,
        &fixture.machine,
        &fixture.code,
    )
    .unwrap_or_else(|e| panic!("{e}; {:#?}", captured.report()));
    assert_eq!(summary.effects().required_private_stack_bytes(), 16);
    assert_eq!(summary.effects().required_entry_sp_alignment(), 16);
    let attached = summary
        .attach(&modules, &request, fixture.id, &fixture.lir, &fixture.code)
        .unwrap();
    assert_eq!(
        attached
            .instantiate_result(&[])
            .unwrap()
            .unwrap()
            .try_eval(&EvalEnv::default())
            .unwrap()
            .as_u64(),
        37
    );
    println!(
        "DEFINED_CALLEE_FRAME bytes=16 storage_permission=false native_credit=false code_sha256={:x}",
        Sha256::digest(&fixture.code)
    );
}

#[test]
fn defined_callee_argument_shape_sort_depth_and_arity_fail_closed() {
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let verifier = verifier();
    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    let fixture = Fixture::new(64, true, 3);
    let modules = fixture.modules();
    let captured = fixture.captured(&verifier, &request);
    let summary = DefinedAffineCallee::bind(
        &modules,
        &request,
        &captured,
        fixture.id,
        &fixture.lir,
        &fixture.machine,
        &fixture.code,
    )
    .unwrap();
    let attached = summary
        .attach(&modules, &request, fixture.id, &fixture.lir, &fixture.code)
        .unwrap();
    assert!(attached.instantiate_result(&[]).is_err());
    assert!(
        attached
            .instantiate_result(&[Arc::new(E::bool_const(true))])
            .is_err()
    );
    assert!(
        attached
            .instantiate_result(&[Arc::new(E::var("wrong_width", 32))])
            .is_err()
    );
    let malformed = E::BvAdd {
        lhs: Arc::new(E::bool_const(false)),
        rhs: Arc::new(E::bv_const(1, 64)),
        width: 64,
    };
    assert!(attached.instantiate_result(&[Arc::new(malformed)]).is_err());
    let mut deep = Arc::new(E::var("deep", 64));
    for _ in 0..crate::smt_raw_print::MAX_DEPTH {
        deep = Arc::new(E::BvAdd {
            lhs: deep.clone(),
            rhs: deep.clone(),
            width: 64,
        });
    }
    assert!(matches!(
        attached.instantiate_result(&[deep]),
        Err(DefinedAffineCalleeError::ArgumentInspection(_))
    ));
    let valid = Arc::new(E::bv_const(9, 64));
    assert_eq!(
        attached
            .instantiate_result(&[valid])
            .unwrap()
            .unwrap()
            .try_eval(&EvalEnv::default())
            .unwrap()
            .as_u64(),
        12
    );
}

#[test]
fn defined_callee_finite_substitution_keeps_modular_predicate_operands() {
    // Mathematical controls for the shared finite normal-form operation; these
    // alone construct no callee summary and obtain no source/proof authority.
    let bits = 32;
    let mask = u32::MAX as u64;
    let arg = ScalarValue::Integer {
        bits,
        value: Affine::constant(mask, mask),
    };
    let parameter_plus_one = Affine::parameter(0).combine(Affine::constant(1, mask), false, mask);
    let predicate = ScalarValue::Bool(Predicate::compare(
        CompareKind::UnsignedLess,
        Affine::parameter(0),
        parameter_plus_one,
        false,
        bits,
    ));
    assert_eq!(
        predicate.substitute(&[arg], bits),
        Some(ScalarValue::Bool(Predicate::Constant(false)))
    );
    let select = ScalarValue::select(
        bits,
        Predicate::compare(
            CompareKind::Equal,
            Affine::parameter(0),
            Affine::constant(3, mask),
            false,
            bits,
        ),
        Affine::constant(7, mask),
        parameter_plus_one,
    );
    assert_eq!(
        select.substitute(&[arg], bits).unwrap().as_constant(),
        Some(0)
    );
    assert!(
        select
            .substitute(
                &[ScalarValue::Integer {
                    bits: 64,
                    value: Affine::constant(1, u64::MAX)
                }],
                bits
            )
            .is_none()
    );
}
