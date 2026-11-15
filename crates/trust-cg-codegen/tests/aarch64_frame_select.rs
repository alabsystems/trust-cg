// Copyright 2026 Andrew Yates | Apache-2.0
//! Actual ordinary Core -> LIR -> allocated frame -> linked select-body check.
//! Native observations supplement conditional frame checking, not promotion.
#![cfg(all(feature = "verify", target_arch = "aarch64", target_os = "macos"))]

#[path = "common/static_frame_geometry.rs"]
mod frame;
use trust_cg_codegen as cg;
use trust_cg_ir::{AArch64Opcode as Op, MachOperand};
use trust_cg_verify::aarch64_affine_lowering::check_aarch64_trust_ir_affine_bytes;
use trust_cg_verify::aarch64_conditional_frame::{
    FrameBodyCall, check_frame_body, conditional_static_frame_with_body,
};
use trust_cg_verify::aarch64_static_frame::check_static_frame_envelopes;
use trust_ir::{ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

#[test]
fn original_ordinary_select_and_call_body_preserves_its_frame() {
    let host = cg::CoreHostJitTarget::detect().unwrap();
    let mut builder = ModuleBuilder::new_with_target_info(
        "ordinary_frame_select",
        host.trust_ir_target_info().clone(),
    );
    let ty = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut leaf = builder.function("select_leaf", ty);
    leaf.set_linkage(trust_ir::Linkage::Internal);
    let entry = leaf.create_block();
    let x = leaf.add_block_param(entry, Ty::U64);
    leaf.switch_to_block(entry);
    let seven = leaf.iconst(Ty::U64, 7);
    let sum = leaf.add(Ty::U64, x, seven);
    leaf.ret(vec![sum]);
    let leaf_id = leaf.build();
    let mut caller = builder.function("select_caller", ty);
    let entry = caller.create_block();
    let x = caller.add_block_param(entry, Ty::U64);
    caller.switch_to_block(entry);
    let sum = caller.call(leaf_id, vec![x]);
    let limit = caller.iconst(Ty::U64, 17);
    let condition = caller.icmp(ICmpOp::Ult, Ty::U64, sum, limit);
    let otherwise = caller.iconst(Ty::U64, 0x55aa);
    let selected = caller.select(Ty::U64, condition, sum, otherwise);
    caller.ret(vec![selected]);
    let caller_id = caller.build();
    let module = builder.build().unwrap();
    let source = cg::pipeline::encode_tmbc(&module).unwrap();
    let license =
        cg::CodegenLicensePolicy::default().with_unlicensed(cg::UnlicensedBodyPolicy::Permit);
    let (functions, _) =
        trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::AArch64,
            trust_cg_lower::TlsDialect::MachOTlv,
            &license,
        )
        .unwrap();
    let (leaf_lir, leaf_proof) = functions
        .iter()
        .find(|(f, _)| f.name == "select_leaf")
        .unwrap();
    let (caller_lir, caller_proof) = functions
        .iter()
        .find(|(f, _)| f.name == "select_caller")
        .unwrap();
    let pipeline = |frame| {
        cg::pipeline::Pipeline::new(cg::pipeline::PipelineConfig {
            opt_level: cg::pipeline::OptLevel::O0,
            verify: false,
            target_triple: "aarch64-apple-darwin".into(),
            aarch64_force_frame_pointers: frame,
            ..Default::default()
        })
    };
    let (leaf_machine, _) = pipeline(false)
        .prepare_function_with_metrics_and_trust_ir_module(
            leaf_lir,
            Some(leaf_proof),
            &module,
            module.function_by_id(leaf_id).unwrap(),
        )
        .unwrap();
    let (caller_machine, metrics) = pipeline(true)
        .prepare_function_with_metrics_and_trust_ir_module(
            caller_lir,
            Some(caller_proof),
            &module,
            module.function_by_id(caller_id).unwrap(),
        )
        .unwrap();
    let emitted: Vec<_> = caller_machine
        .block_order
        .iter()
        .flat_map(|block| {
            caller_machine.blocks[block.0 as usize]
                .insts
                .iter()
                .copied()
        })
        .filter(|id| !caller_machine.insts[id.0 as usize].is_pseudo())
        .collect();
    let selects: Vec<_> = emitted
        .iter()
        .copied()
        .filter(|id| {
            matches!(
                caller_machine.insts[id.0 as usize].opcode,
                Op::Csel | Op::CSet
            )
        })
        .collect();
    assert!(
        !selects.is_empty(),
        "actual source must emit a conditional select"
    );
    let buffer = cg::jit::JitCompiler::new(cg::jit::JitConfig {
        verify: false,
        ..Default::default()
    })
    .compile_raw(&[caller_machine.clone(), leaf_machine], &Default::default())
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
    let caller_range = range("select_caller");
    let leaf_range = range("select_leaf");
    let start = usize::try_from(caller_range.start).unwrap();
    let end = usize::try_from(caller_range.end).unwrap();
    let leaf_start = usize::try_from(leaf_range.start).unwrap();
    let leaf_end = usize::try_from(leaf_range.end).unwrap();
    let image = buffer.code_slice();
    let layout = metrics.frame_layout.unwrap();
    assert_eq!(layout.local_area_size, 0);
    let claim = frame::claim(&caller_machine, &layout);
    let candidates = frame::candidates(&caller_machine, &layout);
    let geometry = check_static_frame_envelopes(
        caller_lir,
        &caller_machine,
        &image[start..end],
        &claim,
        &candidates,
        &[],
    )
    .unwrap();
    // This actual ordinary source caller must also exercise the shared
    // decoded frame-adjustment step, not only its select/body path.
    let frame_adds: Vec<_> = candidates
        .prologue
        .iter()
        .copied()
        .filter(|id| caller_machine.insts[id.0 as usize].opcode == Op::AddRI)
        .collect();
    assert!(!frame_adds.is_empty());
    for id in frame_adds {
        let at = geometry.byte_offset(id).unwrap();
        let word = u32::from_le_bytes(image[start + at..start + at + 4].try_into().unwrap());
        let bound = trust_cg_verify::aarch64_add_sub_immediate::bind_add_sub_immediate_word(
            &caller_machine.insts[id.0 as usize],
            word,
        )
        .unwrap();
        assert_eq!(bound.width(), 64);
    }
    let leaf =
        check_aarch64_trust_ir_affine_bytes(&module, 0, leaf_lir, &image[leaf_start..leaf_end])
            .unwrap();
    let machine_calls: Vec<_> = emitted
        .iter()
        .copied()
        .filter(|id| caller_machine.insts[id.0 as usize].opcode == Op::Bl)
        .collect();
    let lir_calls: Vec<_> = caller_lir.blocks[&caller_lir.entry_block]
        .instructions
        .iter()
        .enumerate()
        .filter(|(_, i)| matches!(i.opcode, trust_cg_lower::instructions::Opcode::Call { .. }))
        .map(|(i, _)| i)
        .collect();
    assert_eq!((machine_calls.len(), lir_calls.len()), (1, 1));
    let calls = [FrameBodyCall {
        instruction: machine_calls[0],
        lir_instruction: lir_calls[0],
        callee_offset: leaf_start,
        callee: &leaf,
    }];
    let directory = tempfile::Builder::new()
        .prefix("trust-cg-select-body-")
        .tempdir()
        .unwrap()
        .keep();
    std::fs::write(directory.join("source.tmbc"), source).unwrap();
    std::fs::write(
        directory.join("caller-lir.json"),
        serde_json::to_vec_pretty(caller_lir).unwrap(),
    )
    .unwrap();
    std::fs::write(
        directory.join("machine.txt"),
        format!("{caller_machine:#?}"),
    )
    .unwrap();
    std::fs::write(directory.join("native-linked.bin"), image).unwrap();
    println!("SELECT_FRAME_BODY_ARTIFACT_DIR={directory:?}");
    let body = check_frame_body(&geometry, &module, 1, image, start, &calls)
        .expect("actual ordinary source select/call body must preserve its frame");
    let composed = conditional_static_frame_with_body(&body).unwrap();
    assert_eq!(composed.exits().len(), 1);
    assert_eq!(composed.exits()[0].premises().len(), 2);
    // Replay the unchanged shared conditional restore obligation. This proves
    // that statement under its two numeric entry premises, not source values
    // or permissions, and cannot promote this caller's instruction inventory.
    use trust_cg_verify::ay_bridge::{
        AYConfig, AYResult, generate_smt2_query_raw, verify_with_cli_raw_attributed,
    };
    use trust_cg_verify::smt::SmtExpr as E;
    fn wrong_sp(expr: &E) -> (E, usize) {
        match expr {
            E::And { lhs, rhs } => {
                let (left, a) = wrong_sp(lhs);
                let (right, b) = wrong_sp(rhs);
                (left.and_expr(right), a + b)
            }
            E::Eq { lhs, rhs } if matches!(rhs.as_ref(), E::Var { name, width: 64 } if name == "frame_entry_sp") => {
                (
                    lhs.as_ref()
                        .clone()
                        .eq_expr(rhs.as_ref().clone().bvadd(E::bv_const(1, 64))),
                    1,
                )
            }
            _ => (expr.clone(), 0),
        }
    }
    let obligation = composed.exits()[0].obligation();
    let config = AYConfig::default();
    let mut wrong = obligation.clone();
    let (expression, changed) = wrong_sp(&wrong.aarch64_expr);
    assert_eq!(changed, 1);
    wrong.aarch64_expr = expression;
    std::fs::write(
        directory.join("restore.smt2"),
        generate_smt2_query_raw(obligation, &config),
    )
    .unwrap();
    std::fs::write(
        directory.join("wrong-sp.smt2"),
        generate_smt2_query_raw(&wrong, &config),
    )
    .unwrap();
    let verdict = verify_with_cli_raw_attributed(obligation, &config);
    std::fs::write(
        directory.join("restore-verdict.txt"),
        format!("{verdict:?}\n{}\n", verdict.provenance()),
    )
    .unwrap();
    assert_eq!(
        verdict.result,
        AYResult::Verified,
        "{}",
        verdict.provenance()
    );
    let wrong_verdict = verify_with_cli_raw_attributed(&wrong, &config);
    std::fs::write(
        directory.join("wrong-sp-verdict.txt"),
        format!("{wrong_verdict:?}\n{}\n", wrong_verdict.provenance()),
    )
    .unwrap();
    assert!(
        matches!(wrong_verdict.result, AYResult::CounterExample(_)),
        "{wrong_verdict:?}"
    );

    // SAFETY: retained actual Core/LIR/machine signatures are C (u64)->u64,
    // and the ordinary JIT execution lease keeps these exact linked bytes live.
    let function = unsafe {
        buffer
            .get_fn_bound::<extern "C" fn(u64) -> u64>("select_caller")
            .unwrap()
    };
    let values = [0, 9, 10, 42, 1 << 63, u64::MAX - 6, u64::MAX];
    for input in values {
        let sum = input.wrapping_add(7);
        assert_eq!(
            (function.as_ref())(input),
            if sum < 17 { sum } else { 0x55aa }
        );
    }
    for &id in &selects {
        let offset = geometry.byte_offset(id).unwrap();
        let word = u32::from_le_bytes(
            image[start + offset..start + offset + 4]
                .try_into()
                .unwrap(),
        );
        for bit in [0, 5, 10, 12, 16, 29, 31] {
            let mut changed = image.to_vec();
            changed[start + offset..start + offset + 4]
                .copy_from_slice(&(word ^ (1 << bit)).to_le_bytes());
            let changed_geometry = check_static_frame_envelopes(
                caller_lir,
                &caller_machine,
                &changed[start..end],
                &claim,
                &candidates,
                &[],
            )
            .unwrap();
            let changed_leaf = check_aarch64_trust_ir_affine_bytes(
                &module,
                0,
                leaf_lir,
                &changed[leaf_start..leaf_end],
            )
            .unwrap();
            let changed_calls = [FrameBodyCall {
                instruction: machine_calls[0],
                lir_instruction: lir_calls[0],
                callee_offset: leaf_start,
                callee: &changed_leaf,
            }];
            assert!(
                check_frame_body(
                    &changed_geometry,
                    &module,
                    1,
                    &changed,
                    start,
                    &changed_calls
                )
                .is_err()
            );
        }
        for destination in [18, 29, 30, 50, 61, 62] {
            let mut machine = caller_machine.clone();
            machine.insts[id.0 as usize].operands[0] =
                MachOperand::PReg(trust_cg_ir::PReg::new(destination));
            // Make W destinations a well-formed W select, so refusal must
            // reach the same protected-register guard as the X form.
            if destination >= 32 {
                for operand in machine.insts[id.0 as usize]
                    .operands
                    .iter_mut()
                    .skip(1)
                    .take(2)
                {
                    match operand {
                        MachOperand::PReg(p) if p.encoding() <= 30 => {
                            *operand = MachOperand::PReg(trust_cg_ir::PReg::new(p.encoding() + 32));
                        }
                        MachOperand::Special(trust_cg_ir::SpecialReg::XZR) => {
                            *operand = MachOperand::Special(trust_cg_ir::SpecialReg::WZR);
                        }
                        _ => {}
                    }
                }
            }
            let mut changed = image.to_vec();
            let sf = u32::from(destination < 32);
            let new_word = (word & !(0x8000_001f)) | (sf << 31) | u32::from(destination % 32);
            changed[start + offset..start + offset + 4].copy_from_slice(&new_word.to_le_bytes());
            let changed_geometry = check_static_frame_envelopes(
                caller_lir,
                &machine,
                &changed[start..end],
                &claim,
                &candidates,
                &[],
            )
            .unwrap();
            let changed_leaf = check_aarch64_trust_ir_affine_bytes(
                &module,
                0,
                leaf_lir,
                &changed[leaf_start..leaf_end],
            )
            .unwrap();
            let changed_calls = [FrameBodyCall {
                instruction: machine_calls[0],
                lir_instruction: lir_calls[0],
                callee_offset: leaf_start,
                callee: &changed_leaf,
            }];
            let error = check_frame_body(
                &changed_geometry,
                &module,
                1,
                &changed,
                start,
                &changed_calls,
            )
            .unwrap_err();
            assert!(
                error.to_string().contains("writes SP/FP/LR/platform"),
                "{error}"
            );
        }
    }
    println!(
        "SELECT_FRAME_BODY_NATIVE cases=7 selections={} frame={} source_result_proof=false machine_promotion=false",
        selects.len(),
        layout.total_frame_size
    );
    std::fs::write(directory.join("result.json"), serde_json::to_vec_pretty(&serde_json::json!({"native_cases":7,"frame_bytes":layout.total_frame_size,"selects":selects.len(),"source_result_proof":false,"machine_promotion":false})).unwrap()).unwrap();
}
