// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ordinary source-to-emitted-frame geometry, not proof credit or execution.

#[path = "common/static_frame_geometry.rs"]
mod fixture;

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, encode_function_with_fixups};
use trust_cg_ir::{AArch64Opcode as Op, InstId, MachFunction, MachOperand as O};
use trust_cg_verify::aarch64_static_frame::*;
use trust_ir::{ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

fn ordinary_source() -> trust_ir::Module {
    let mut module = ModuleBuilder::new("ordinary_static_frame");
    let mut arguments = vec![Ty::Ptr];
    arguments.extend(vec![Ty::I64; 10]);
    let external_type = module.add_func_type(arguments, vec![Ty::I64]);
    let external = module.declare_function("ordinary_observe", external_type);
    let ty = module.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    let mut f = module.function("ordinary_static_frame", ty);
    let entry = f.create_block();
    let left = f.create_block();
    let right = f.create_block();
    let input = f.add_block_param(entry, Ty::Ptr);
    let condition = f.add_block_param(entry, Ty::I64);
    f.switch_to_block(entry);
    let local = f.alloca(Ty::I64);
    let zero = f.iconst(Ty::I64, 0);
    f.store(Ty::I64, local, zero);
    let mut live = Vec::new();
    for index in 0..24 {
        let k = f.iconst(Ty::I64, index);
        let p = f.gep(Ty::I64, input, vec![k]);
        let v = f.load(Ty::I64, p);
        live.push(v);
    }
    let mut args = vec![local];
    args.extend(live[..10].iter().copied());
    let mut total = f.call(external, args);
    for value in live {
        total = f.add(Ty::I64, total, value);
    }
    let take = f.icmp(ICmpOp::Eq, Ty::I64, condition, zero);
    f.condbr(take, left, vec![], right, vec![]);
    f.switch_to_block(left);
    f.ret(vec![total]);
    f.switch_to_block(right);
    let one = f.iconst(Ty::I64, 1);
    let other = f.add(Ty::I64, total, one);
    f.ret(vec![other]);
    f.build();
    module.build().unwrap()
}

fn prepared(
    module: trust_ir::Module,
    name: &str,
) -> (
    trust_cg_lower::Function,
    MachFunction,
    trust_cg_codegen::frame::FrameLayout,
    Vec<u8>,
    Vec<FrameImagePatch>,
) {
    let license = trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit);
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::AArch64,
        trust_cg_lower::TlsDialect::MachOTlv,
        &license,
    )
    .unwrap();
    let (lir, context) = lowered.into_iter().find(|(f, _)| f.name == name).unwrap();
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        ..PipelineConfig::for_target("aarch64-apple-darwin")
    });
    let (machine, metrics) = pipeline
        .prepare_function_with_metrics(&lir, Some(&context))
        .unwrap();
    let layout = metrics.frame_layout.unwrap();
    let (code, fixups) = encode_function_with_fixups(&machine).unwrap();
    (
        lir,
        machine,
        layout,
        code,
        fixups
            .iter()
            .map(|fixup| FrameImagePatch {
                offset: fixup.offset,
                bytes: 1u32 << fixup.kind.default_log2_size(),
            })
            .collect(),
    )
}

fn rewrite_word(machine: &MachFunction, code: &mut [u8], id: InstId) {
    let mut offset = 0;
    for &block in &machine.block_order {
        for &current in &machine.blocks[block.0 as usize].insts {
            let inst = &machine.insts[current.0 as usize];
            if inst.is_pseudo() {
                continue;
            }
            if current == id {
                let word = trust_cg_verify::aarch64_memory_effect::memory_effect_word(inst)
                    .or_else(|| {
                        trust_cg_verify::aarch64_instruction_word_proofs::instruction_word(inst)
                            .map(|word| word.word)
                    })
                    .unwrap();
                code[offset..offset + 4].copy_from_slice(&word.to_le_bytes());
                return;
            }
            offset += 4;
        }
    }
    panic!("missing emitted mutation");
}

#[test]
fn original_ordinary_nonleaf_envelopes_keep_all_body_and_call_obligations_pending() {
    let (lir, machine, layout, code, fixups) = prepared(ordinary_source(), "ordinary_static_frame");
    assert!(layout.callee_saved_pairs.len() >= 3);
    assert!(
        layout.spill_area_size > 0
            && layout.local_area_size == 0
            && layout.outgoing_arg_area_size > 0
    );
    let claim = fixture::claim(&machine, &layout);
    let candidates = fixture::candidates(&machine, &layout);
    let checked =
        check_static_frame_envelopes(&lir, &machine, &code, &claim, &candidates, &fixups).unwrap();
    assert!(std::ptr::eq(checked.source(), &lir) && std::ptr::eq(checked.machine(), &machine));
    assert_eq!(checked.image().as_ptr(), code.as_ptr());
    assert_eq!(
        checked.saved_slots().len(),
        layout.callee_saved_pairs.len() * 2
    );
    assert_eq!(checked.fixed_slots().len(), machine.stack_slots.len());
    assert_eq!(checked.conditional_exits().len(), 2);
    assert_eq!(checked.required_entry_sp_alignment(), 16);
    assert_eq!(
        checked.required_nonwrapping_frame_range().start,
        -i64::from(layout.total_frame_size)
    );
    assert_eq!(
        checked
            .unresolved_body()
            .iter()
            .map(|part| part.calls.len())
            .sum::<usize>(),
        1
    );
    for exit in checked.conditional_exits() {
        assert_eq!(exit.required_sp, -i64::from(layout.total_frame_size));
        assert_eq!(exit.required_fp, Some(-16));
    }
}

#[test]
fn darwin_startup_frame_checks_geometry_and_keeps_external_call_pending() {
    use trust_cg_lower::instructions::{DirectCallBinding, Opcode};

    let mut module = ModuleBuilder::new("startup_frame");
    let external_type = module.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    let external = module.declare_function("startup_observe", external_type);
    let ty = module.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut f = module.function("startup_frame", ty);
    let entry = f.create_block();
    let input = f.add_block_param(entry, Ty::I64);
    f.switch_to_block(entry);
    let local = f.alloca(Ty::I64);
    f.store(Ty::I64, local, input);
    let result = f.call(external, vec![local]);
    f.ret(vec![result]);
    f.build();

    let (lir, machine, layout, code, fixups) = prepared(module.build().unwrap(), "startup_frame");
    let instructions = lir.blocks.values().flat_map(|block| &block.instructions);
    let address = instructions
        .clone()
        .find(|inst| matches!(&inst.opcode, Opcode::StackAddr { slot: 0 }))
        .unwrap();
    let source_calls: Vec<_> = instructions
        .filter(|inst| matches!(&inst.opcode, Opcode::Call { .. }))
        .collect();
    let [source_call] = source_calls.as_slice() else {
        panic!("expected one source call");
    };
    assert!(matches!(
        &source_call.opcode,
        Opcode::Call { name, binding: DirectCallBinding::Interposable } if name == "startup_observe"
    ));
    assert_eq!(source_call.args, address.results);

    let claim = fixture::claim(&machine, &layout);
    let candidates = fixture::candidates(&machine, &layout);
    let checked =
        check_static_frame_envelopes(&lir, &machine, &code, &claim, &candidates, &fixups).unwrap();
    assert!(!layout.is_leaf && layout.uses_frame_pointer);
    assert_eq!(claim.total_bytes, 32);
    assert_eq!(
        claim.saved_pairs,
        [[SavedFrameRegister::X(29), SavedFrameRegister::X(30)]]
    );
    assert_eq!(
        checked.fixed_slots(),
        &[RelativeFrameRegion {
            start: -24,
            end: -16
        }]
    );
    assert_eq!(candidates.prologue.len(), 3);
    let prologue_words: Vec<_> = code[..12]
        .chunks_exact(4)
        .map(|bytes| u32::from_le_bytes(bytes.try_into().unwrap()))
        .collect();
    assert_eq!(prologue_words, [0xa9bf_7bfd, 0x9100_03fd, 0xd100_43ff]);

    let [exit] = checked.conditional_exits() else {
        panic!("expected one conditional exit");
    };
    assert_eq!((exit.required_sp, exit.required_fp), (-32, Some(-16)));
    let [body] = checked.unresolved_body() else {
        panic!("expected one unresolved body");
    };
    let [call] = body.calls.as_slice() else {
        panic!("expected one pending call");
    };
    assert_eq!(machine.insts[call.0 as usize].opcode, Op::Bl);
    assert!(body.instructions.contains(call) && body.instructions.len() > 1);
    assert_eq!(
        fixups,
        [FrameImagePatch {
            offset: checked.byte_offset(*call).unwrap().try_into().unwrap(),
            bytes: 4,
        }]
    );
}

#[test]
fn wrong_frame_setup_restore_save_word_and_slot_placement_refuse() {
    let (lir, machine, layout, code, fixups) = prepared(ordinary_source(), "ordinary_static_frame");
    let claim = fixture::claim(&machine, &layout);
    let candidates = fixture::candidates(&machine, &layout);
    let fp = *candidates
        .prologue
        .iter()
        .find(|id| machine.insts[id.0 as usize].opcode == Op::AddRI)
        .unwrap();
    let save = *candidates
        .prologue
        .iter()
        .find(|id| machine.insts[id.0 as usize].opcode == Op::StpRI)
        .unwrap();
    for (id, position, delta) in [(fp, 2, 8), (save, 3, 16)] {
        let mut changed = machine.clone();
        let mut bytes = code.clone();
        let O::Imm(value) = &mut changed.insts[id.0 as usize].operands[position] else {
            panic!("immediate");
        };
        *value += delta;
        rewrite_word(&changed, &mut bytes, id);
        assert!(
            check_static_frame_envelopes(&lir, &changed, &bytes, &claim, &candidates, &fixups)
                .is_err()
        );
    }
    let post = *candidates.epilogues[0]
        .iter()
        .find(|id| machine.insts[id.0 as usize].opcode == Op::LdpPostIndex)
        .unwrap();
    let mut changed = machine.clone();
    let mut bytes = code.clone();
    let O::Imm(value) = &mut changed.insts[post.0 as usize].operands[3] else {
        panic!("post offset");
    };
    *value += 16;
    rewrite_word(&changed, &mut bytes, post);
    assert!(
        check_static_frame_envelopes(&lir, &changed, &bytes, &claim, &candidates, &fixups).is_err()
    );
    let checked =
        check_static_frame_envelopes(&lir, &machine, &code, &claim, &candidates, &fixups).unwrap();
    let at = checked.byte_offset(fp).unwrap();
    let mut bytes = code.clone();
    bytes[at] ^= 1;
    assert!(
        check_static_frame_envelopes(&lir, &machine, &bytes, &claim, &candidates, &fixups).is_err()
    );
    let mut wrong = claim.clone();
    wrong.slot_fp_offsets[0] = Some(0);
    assert!(
        check_static_frame_envelopes(&lir, &machine, &code, &wrong, &candidates, &fixups).is_err()
    );
    let mut wrong = claim.clone();
    wrong.slot_fp_offsets[1] = wrong.slot_fp_offsets[0];
    assert!(
        check_static_frame_envelopes(&lir, &machine, &code, &wrong, &candidates, &fixups).is_err()
    );
}

#[test]
fn missing_reused_exits_fixups_and_dynamic_or_red_zone_claims_refuse() {
    let (lir, machine, layout, code, fixups) = prepared(ordinary_source(), "ordinary_static_frame");
    let claim = fixture::claim(&machine, &layout);
    let candidates = fixture::candidates(&machine, &layout);
    let mut wrong = candidates.clone();
    wrong.epilogues.pop();
    assert!(check_static_frame_envelopes(&lir, &machine, &code, &claim, &wrong, &fixups).is_err());
    let mut wrong = candidates.clone();
    wrong.epilogues.push(wrong.epilogues[0].clone());
    assert!(check_static_frame_envelopes(&lir, &machine, &code, &claim, &wrong, &fixups).is_err());
    assert!(
        check_static_frame_envelopes(
            &lir,
            &machine,
            &code,
            &claim,
            &candidates,
            &[FrameImagePatch {
                offset: 0,
                bytes: 4
            }]
        )
        .is_err()
    );
    let checked =
        check_static_frame_envelopes(&lir, &machine, &code, &claim, &candidates, &fixups).unwrap();
    let at = checked.byte_offset(candidates.epilogues[0][0]).unwrap();
    // A wider patch starts in the unresolved body but reaches the first
    // envelope word: checking only its starting coordinate would miss it.
    assert!(
        check_static_frame_envelopes(
            &lir,
            &machine,
            &code,
            &claim,
            &candidates,
            &[FrameImagePatch {
                offset: (at - 4) as u32,
                bytes: 8
            }],
        )
        .unwrap_err()
        .0
        .contains("patch overlaps envelope")
    );
    for dynamic in [false, true] {
        let mut wrong = claim.clone();
        wrong.dynamic_allocation = dynamic;
        wrong.red_zone = !dynamic;
        assert!(
            check_static_frame_envelopes(&lir, &machine, &code, &wrong, &candidates, &fixups)
                .is_err()
        );
    }
}

#[test]
fn early_sp_deallocation_fp_clobber_and_relabelled_pairs_refuse() {
    let (lir, machine, layout, code, fixups) = prepared(ordinary_source(), "ordinary_static_frame");
    let claim = fixture::claim(&machine, &layout);
    let candidates = fixture::candidates(&machine, &layout);
    let mut wrong = claim.clone();
    let old = wrong.saved_pairs[0][1];
    wrong.saved_pairs[0][1] = wrong.saved_pairs[1][1];
    wrong.saved_pairs[1][1] = old;
    assert!(
        check_static_frame_envelopes(&lir, &machine, &code, &wrong, &candidates, &fixups).is_err()
    );

    // Preserve every effective restore address and final SP while deallocating
    // the CSA before loading it. Access-time live-SP checking must refuse.
    let mut changed = machine.clone();
    let mut bytes = code.clone();
    for &id in &candidates.epilogues[0] {
        let inst = &mut changed.insts[id.0 as usize];
        match inst.opcode {
            Op::AddRI => {
                let O::Imm(value) = &mut inst.operands[2] else {
                    panic!("SP adjustment")
                };
                *value += i64::from(layout.callee_saved_area_size);
            }
            Op::LdpRI | Op::LdpPostIndex => {
                let old_offset = if inst.opcode == Op::LdpPostIndex {
                    0
                } else {
                    let O::Imm(value) = inst.operands[3] else {
                        panic!("pair offset")
                    };
                    value
                };
                inst.opcode = Op::LdpRI;
                inst.operands[3] = O::Imm(old_offset - i64::from(layout.callee_saved_area_size));
            }
            _ => continue,
        }
        rewrite_word(&changed, &mut bytes, id);
    }
    assert!(
        check_static_frame_envelopes(&lir, &changed, &bytes, &claim, &candidates, &fixups)
            .unwrap_err()
            .0
            .contains("live SP")
    );

    // Set the final FP value before saving incoming X29, retaining all final
    // coordinates. This would save the new FP instead of the caller's X29.
    let mut changed = machine.clone();
    let fp = *candidates
        .prologue
        .iter()
        .find(|id| changed.insts[id.0 as usize].opcode == Op::AddRI)
        .unwrap();
    let entry = &mut changed.blocks[changed.entry.0 as usize].insts;
    entry.retain(|id| *id != fp);
    entry.insert(0, fp);
    let inst = &mut changed.insts[fp.0 as usize];
    inst.opcode = Op::SubRI;
    inst.operands[2] = O::Imm(16);
    let mut wrong = candidates.clone();
    wrong.prologue.retain(|id| *id != fp);
    wrong.prologue.insert(0, fp);
    // Re-encode from original words in their new order, replacing only FP.
    let mut bytes = Vec::new();
    let original =
        check_static_frame_envelopes(&lir, &machine, &code, &claim, &candidates, &fixups).unwrap();
    for &block in &changed.block_order {
        for &id in &changed.blocks[block.0 as usize].insts {
            if changed.insts[id.0 as usize].is_pseudo() {
                continue;
            }
            let offset = original.byte_offset(id).unwrap();
            bytes.extend_from_slice(&code[offset..offset + 4]);
        }
    }
    rewrite_word(&changed, &mut bytes, fp);
    // No fixup is part of this prefix; unchanged starts are sufficient here.
    assert!(
        check_static_frame_envelopes(&lir, &changed, &bytes, &claim, &wrong, &fixups)
            .unwrap_err()
            .0
            .contains("incoming X29")
    );
}

#[test]
fn restored_fp_clobber_refuses_and_body_call_flags_cannot_hide_pending_calls() {
    let (lir, machine, layout, code, fixups) = prepared(ordinary_source(), "ordinary_static_frame");
    let claim = fixture::claim(&machine, &layout);
    let candidates = fixture::candidates(&machine, &layout);
    let original =
        check_static_frame_envelopes(&lir, &machine, &code, &claim, &candidates, &fixups).unwrap();
    let ret = *candidates.epilogues[0].last().unwrap();
    let at = original.byte_offset(ret).unwrap();
    let mut changed = machine.clone();
    let id = InstId(changed.insts.len() as u32);
    let clobber = trust_cg_ir::MachInst::new(
        Op::AddRI,
        vec![
            O::PReg(trust_cg_ir::aarch64_regs::X29),
            O::Special(trust_cg_ir::SpecialReg::SP),
            O::Imm(0),
        ],
    );
    let word = trust_cg_verify::aarch64_instruction_word_proofs::instruction_word(&clobber)
        .unwrap()
        .word;
    changed.insts.push(clobber);
    let row = changed
        .blocks
        .iter_mut()
        .find(|block| block.insts.contains(&ret))
        .unwrap();
    row.insts.insert(
        row.insts.iter().position(|other| *other == ret).unwrap(),
        id,
    );
    let mut wrong = candidates.clone();
    let last = wrong.epilogues[0].len() - 1;
    wrong.epilogues[0].insert(last, id);
    let mut bytes = code.clone();
    bytes.splice(at..at, word.to_le_bytes());
    let mut patches = fixups.clone();
    for patch in &mut patches {
        if patch.offset as usize >= at {
            patch.offset += 4;
        }
    }
    assert!(
        check_static_frame_envelopes(&lir, &changed, &bytes, &claim, &wrong, &patches)
            .unwrap_err()
            .0
            .contains("after restoring incoming X29")
    );

    let call = original
        .unresolved_body()
        .iter()
        .flat_map(|part| &part.calls)
        .next()
        .unwrap();
    let mut changed = machine.clone();
    changed.insts[call.0 as usize]
        .flags
        .remove(trust_cg_ir::InstFlags::IS_CALL);
    let checked =
        check_static_frame_envelopes(&lir, &changed, &code, &claim, &candidates, &fixups).unwrap();
    assert_eq!(
        checked
            .unresolved_body()
            .iter()
            .map(|part| part.calls.len())
            .sum::<usize>(),
        1
    );
}
