// Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use crate::aarch64_conditional_frame::conditional_static_frame_with_exact_body;
use crate::memory_proofs::encode_store_le;
use crate::smt::{EvalEnv, SmtExpr as E};

fn with_body(fixture: &Ordinary, test: impl FnOnce(&CheckedFrameBody<'_, '_, '_>)) {
    let leaf_offset = fixture.image.len() - 16;
    let geometry = check_static_frame_envelopes(
        &fixture.lir[1],
        &fixture.machine,
        &fixture.image[..leaf_offset],
        &fixture.claim,
        &fixture.candidates,
        &[],
    )
    .unwrap();
    let leaf = check_aarch64_trust_ir_affine_bytes(
        &fixture.module,
        0,
        &fixture.lir[0],
        &fixture.image[leaf_offset..],
    )
    .unwrap();
    let sites: Vec<_> = fixture.lir[1].blocks[&fixture.lir[1].entry_block]
        .instructions
        .iter()
        .enumerate()
        .filter_map(|(i, n)| matches!(n.opcode, Opcode::Call { .. }).then_some(i))
        .collect();
    // Intentionally reversed DATA order. Only actual byte order may decide
    // which BL's real LR store remains at normal return.
    let calls = [
        FrameBodyCall {
            instruction: InstId(7),
            lir_instruction: sites[1],
            callee_offset: leaf_offset,
            callee: &leaf,
        },
        FrameBodyCall {
            instruction: InstId(6),
            lir_instruction: sites[0],
            callee_offset: leaf_offset,
            callee: &leaf,
        },
    ];
    let body = check_frame_body(&geometry, &fixture.module, 1, &fixture.image, 0, &calls).unwrap();
    test(&body);
}

#[test]
fn exact_call_memory_retains_both_real_frames_and_actual_bl_order() {
    let fixture = Ordinary::new();
    with_body(&fixture, |body| {
        let legacy = conditional_static_frame_with_body(body).unwrap();
        assert!(legacy.exits()[0].exact_post_memory().is_none());
        assert!(legacy.exact_call_entry_memory(InstId(6)).is_err());
        let exact = conditional_static_frame_with_exact_body(body).unwrap();
        assert_eq!(
            exact.exact_call_entry_memory(InstId(6)).unwrap(),
            exact.post_save_memory()
        );
        assert_eq!(
            exact.exact_call_entry_memory(InstId(7)).unwrap(),
            exact.exact_call_exit_memory(InstId(6)).unwrap()
        );
        let actual = exact.exits()[0].exact_post_memory().unwrap();
        assert_eq!(actual, exact.exact_call_exit_memory(InstId(7)).unwrap());
        assert_ne!(
            exact.exits()[0].exact_post_memory(),
            Some(exact.post_save_memory())
        );
        assert!(exact.exact_call_entry_memory(InstId(99)).is_err());
        assert!(!actual.to_string().contains("_private_"));
        assert!(actual.to_string().contains("frame_entry_memory"));
        // Evaluate the complete finite array, including its default value at
        // EVERY other address. This tests actual byte values/order, not an AST
        // spelling (e.g. the decoder's zero-extended12-bit ADD immediate).
        let concrete = actual
            .try_rewrite_dag(&mut |node| -> std::result::Result<Option<E>, String> {
                Ok(match node {
                    E::UF { name, args, .. } if name == "frame_entry_memory" && args.is_empty() => {
                        Some(crate::memory_proofs::zeroed_memory())
                    }
                    _ => None,
                })
            })
            .unwrap()
            .unwrap();
        for (sp, base, register_base) in [
            (0x1000u64, 0x4000, 0x12340000),
            (0x2000, 0x8000, 37),
            (0x10000, 0x100000, 42),
        ] {
            let mut env = EvalEnv::default();
            env.insert("frame_entry_sp".into(), sp);
            env.insert("frame_image_base".into(), base);
            for field in 19..=30 {
                env.insert(format!("frame_entry_x{field}"), register_base + field);
            }
            let mut expected = crate::memory_proofs::zeroed_memory();
            // Independent original ISA fixture: ten caller lanes, then the
            // real callee's incoming FP and the SECOND BL's actual LR.
            for (lane, field) in [26u64, 25, 24, 23, 22, 21, 20, 19, 29, 30]
                .into_iter()
                .enumerate()
            {
                expected = encode_store_le(
                    &expected,
                    &E::bv_const(sp - 80 + lane as u64 * 8, 64),
                    &E::bv_const(register_base + field, 64),
                    8,
                );
            }
            expected = encode_store_le(
                &expected,
                &E::bv_const(sp - 96, 64),
                &E::bv_const(sp - 16, 64),
                8,
            );
            expected = encode_store_le(
                &expected,
                &E::bv_const(sp - 88, 64),
                &E::bv_const(base + 32, 64),
                8,
            );
            assert_eq!(
                concrete.try_eval(&env).unwrap(),
                expected.try_eval(&env).unwrap()
            );
        }
        let mut env = EvalEnv::default();
        env.insert("frame_image_base".into(), 0x4000);
        env.insert("frame_entry_sp".into(), 0x1000);
        assert_eq!(
            exact
                .exact_call_return_target(InstId(6))
                .unwrap()
                .try_eval(&env)
                .unwrap()
                .as_u64(),
            0x401c
        );
        assert_eq!(
            exact
                .exact_call_return_target(InstId(7))
                .unwrap()
                .try_eval(&env)
                .unwrap()
                .as_u64(),
            0x4020
        );
        assert_eq!(
            exact.exits()[0]
                .exact_post_sp()
                .unwrap()
                .try_eval(&env)
                .unwrap()
                .as_u64(),
            0x1000
        );
        assert_eq!(exact.exits()[0].premises(), legacy.exits()[0].premises());
    });
}

#[test]
fn exact_call_memory_refuses_branch_order_even_when_footprint_is_valid() {
    let mut fixture = Ordinary::new();
    let branch = InstId(fixture.machine.insts.len() as u32);
    fixture
        .machine
        .insts
        .push(MachInst::new(Op::B, vec![O::Imm(1)]));
    fixture.machine.blocks[0].insts.insert(8, branch);
    fixture.image.splice(32..32, 0x14000001u32.to_le_bytes());
    fixture.image[24..28].copy_from_slice(&0x94000009u32.to_le_bytes());
    fixture.image[28..32].copy_from_slice(&0x94000008u32.to_le_bytes());
    with_body(&fixture, |body| {
        assert!(conditional_static_frame_with_body(body).is_ok());
        let error = conditional_static_frame_with_exact_body(body)
            .err()
            .expect("branch order must refuse");
        assert!(
            error.to_string().contains("does not infer branch order"),
            "{error}"
        );
    });
}

#[cfg(target_arch = "aarch64")]
#[test]
fn exact_call_memory_native_borrowed_reader_37_42_retains_alias_queries() {
    use crate::provenance_xcheck::ProvenanceXCheckMode;
    use crate::read_only_replay::ReadOnlyCompilerRelations;
    use crate::source_bound_frame::bind_read_only_source;
    use trust_cg_codegen::jit::{JitCompiler, JitConfig};
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
    let (lowered, _) =
        trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
            &fixture.module,
            trust_cg_lower::GuardCarrierArch::AArch64,
            trust_cg_lower::TlsDialect::MachOTlv,
            &crate::license_test_support::permit_unlicensed(),
        )
        .unwrap();
    fixture.lir = lowered.into_iter().map(|(f, _)| f).collect();
    fixture.machine.insts[7] = MachInst::new(Op::AddRI, vec![O::PReg(X0), O::PReg(X0), O::Imm(0)]);
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
    let buffer = JitCompiler::new(JitConfig {
        verify: false,
        ..JitConfig::default()
    })
    .compile_raw(
        &[fixture.machine.clone(), leaf.clone()],
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
    let caller = range("two_call_frame");
    let callee = range("identity_leaf");
    let image = buffer.code_slice();
    let image_before = image.to_vec();
    let source = bind_read_only_source(&fixture.module, 0, &fixture.lir[0]).unwrap();
    let relations = ReadOnlyCompilerRelations::bind(
        &source,
        &leaf,
        &image[callee.start as usize..callee.end as usize],
    )
    .unwrap();
    let verifier =
        crate::FunctionVerifier::with_config(crate::VerificationConfig::for_proof_promotion());
    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    let report = relations.replay(&request);
    let certificate = report
        .certificate()
        .unwrap_or_else(|| panic!("actual native readonly relations: {:?}", report.outcomes()));
    let geometry = check_static_frame_envelopes(
        &fixture.lir[1],
        &fixture.machine,
        &image[caller.start as usize..caller.end as usize],
        &fixture.claim,
        &fixture.candidates,
        &[],
    )
    .unwrap();
    let site = fixture.lir[1].blocks[&fixture.lir[1].entry_block]
        .instructions
        .iter()
        .position(|n| matches!(n.opcode, Opcode::Call { .. }))
        .unwrap();
    let calls = [ReadonlyFrameBodyCall::from_replayed_callee(
        InstId(6),
        site,
        callee.start as usize,
        certificate,
        &request,
    )
    .unwrap()];
    let body = check_readonly_frame_body(
        &geometry,
        &fixture.module,
        1,
        image,
        caller.start as usize,
        &calls,
    )
    .unwrap();
    let exact = conditional_static_frame_with_exact_body(&body).unwrap();
    assert_eq!(
        exact.exact_call_entry_memory(InstId(6)).unwrap(),
        exact.post_save_memory()
    );
    assert_eq!(
        exact.exits()[0].exact_post_memory(),
        Some(exact.post_save_memory())
    );
    // A pointer aliased to saved caller FP is deliberately NOT excluded. The
    // transported return must read the actual post-prologue array, not pretend
    // raw memory is unchanged just because the source callee is read-only.
    let alias = Arc::new(E::var("frame_entry_sp", 64).bvadd(E::bv_const((-16i64) as u64, 64)));
    let observed = exact
        .instantiate_readonly_call_result_in_frame(
            InstId(6),
            certificate,
            &request,
            std::slice::from_ref(&alias),
        )
        .unwrap();
    let expected = body
        .instantiate_readonly_call_result(
            InstId(6),
            certificate,
            &request,
            std::slice::from_ref(&alias),
            &Arc::new(exact.post_save_memory().clone()),
        )
        .unwrap();
    assert_eq!(*observed, *expected);
    // A concrete control supplies an explicit constant initial array. Missing
    // or uninterpreted arrays must never be silently evaluated as zero.
    let concrete = observed
        .try_rewrite_dag(&mut |node| -> std::result::Result<Option<E>, String> {
            Ok(match node {
                E::UF { name, args, .. } if name == "frame_entry_memory" && args.is_empty() => {
                    Some(crate::memory_proofs::zeroed_memory())
                }
                _ => None,
            })
        })
        .unwrap()
        .unwrap();
    let mut env = EvalEnv::default();
    env.insert("frame_entry_sp".into(), 0x1000);
    env.insert("frame_image_base".into(), 0x4000);
    for field in 19..=30 {
        env.insert(format!("frame_entry_x{field}"), 0x12340000 + field);
    }
    assert_eq!(concrete.try_eval(&env).unwrap().as_u64(), 0x12340000 + 29);
    let foreign = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
    assert!(
        exact
            .instantiate_readonly_call_result_in_frame(InstId(6), certificate, &foreign, &[alias])
            .is_err()
    );
    // Actual ordinary pointer ABI, backed by one live initialized u64. This
    // executes the SAME original module's emitted linked bytes, unchecked JIT;
    // it is not a nominal-Closure/source-license/native-proof capability.
    let function = unsafe {
        buffer
            .get_fn_bound::<unsafe extern "C" fn(*const u64) -> u64>("two_call_frame")
            .unwrap()
    };
    for value in [37u64, 42] {
        let backing = value;
        assert_eq!(unsafe { (function.as_ref())(&backing) }, value);
        assert_eq!(backing, value);
    }
    assert_eq!(buffer.code_slice(), image_before);
    let directory = tempfile::Builder::new()
        .prefix("trust-cg-exact-callee-memory-")
        .tempdir()
        .unwrap()
        .keep();
    std::fs::write(directory.join("native-linked.bin"), image).unwrap();
    std::fs::write(
        directory.join("original-core.tmbc"),
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
    std::fs::write(
        directory.join("scope.json"),
        serde_json::to_vec_pretty(&serde_json::json!({
            "caller_range":[caller.start,caller.end],"callee_range":[callee.start,callee.end],
            "actual_native_values":[37,42],"computed_entry_array_includes_prologue":true,
            "saved_fp_alias_query_retained":true,"nominal_closure_or_native_proof_authority":false,
            "all_seven_shared_frame_inputs_supplied":false
        }))
        .unwrap(),
    )
    .unwrap();
    println!(
        "EXACT_CALLEE_MEMORY_NATIVE_ARTIFACT_DIR={}",
        serde_json::to_string(&directory).unwrap()
    );
}
