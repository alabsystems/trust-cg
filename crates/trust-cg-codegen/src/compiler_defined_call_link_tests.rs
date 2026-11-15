// Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use crate::pipeline::{EncodedAarch64FixupSite, encode_function_with_fixups_and_sites};
use trust_cg_ir::{AArch64Opcode as Op, InstId, MachFunction, MachInst, MachOperand as O};

fn fixture() -> (trust_cg_lower::Function, MachFunction) {
    use trust_cg_lower::instructions::{DirectCallBinding, Instruction, Opcode, Value};
    let mut lir = trust_cg_lower::Function::new(
        "caller",
        trust_cg_lower::function::Signature {
            params: vec![],
            returns: vec![trust_cg_lower::Type::I64],
        },
    );
    lir.blocks.insert(
        lir.entry_block,
        trust_cg_lower::function::BasicBlock {
            instructions: vec![Instruction {
                opcode: Opcode::Call {
                    name: "leaf".into(),
                    binding: DirectCallBinding::ExactModuleFunction { function: 0 },
                },
                args: vec![],
                results: vec![Value(0)],
            }],
            ..Default::default()
        },
    );
    let mut machine = MachFunction::new(
        "caller".into(),
        trust_cg_ir::function::Signature::new(vec![], vec![trust_cg_ir::function::Type::I64]),
    );
    let instruction = machine.push_inst(MachInst::with_flags(
        Op::Bl,
        vec![O::Symbol("leaf".into())],
        Op::Bl
            .default_flags()
            .union(trust_cg_ir::InstFlags::EXACT_MODULE_CALL),
    ));
    machine.blocks[machine.entry.0 as usize]
        .insts
        .push(instruction);
    machine.set_inst_lowering_provenance(
        instruction,
        trust_cg_ir::LoweringProvenance::SourceInst {
            id: trust_cg_ir::SourceInstId {
                block: lir.entry_block.0,
                index: 0,
            },
            digest: lir.blocks[&lir.entry_block].instructions[0].lowering_digest(),
            trust_ir_inst: None,
        },
    );
    lir.blocks
        .get_mut(&lir.entry_block)
        .unwrap()
        .instructions
        .push(Instruction {
            opcode: Opcode::Return,
            args: vec![Value(0)],
            results: vec![],
        });
    let ret = machine.push_inst(
        MachInst::new(Op::Ret, vec![O::PReg(trust_cg_ir::regs::PReg::new(30))])
            .with_implicit_uses(&[trust_cg_ir::regs::X0]),
    );
    machine.blocks[machine.entry.0 as usize].insts.push(ret);
    // Use normal non-leaf frame lowering so the final encoder checks actual LR restoration.
    let frame = crate::frame::try_compute_frame_layout(&machine, 0, false).unwrap();
    assert_eq!(frame.total_frame_size, 16);
    crate::frame::insert_prologue_epilogue(&mut machine, &frame).unwrap();
    (lir, machine)
}

#[test]
fn exact_reemission_rejects_byte_or_complete_site_mutation() {
    let (_, machine) = fixture();
    let (code, fixups, sites) = encode_function_with_fixups_and_sites(&machine).unwrap();
    validate_core_aarch64_fixup_sites(&machine, &code, &fixups, &sites).unwrap();
    compare_emission(&code, &sites, &code, &sites).unwrap();
    let mut changed = code.clone();
    changed[0] ^= 1;
    assert!(compare_emission(&changed, &sites, &code, &sites).is_err());
    for altered in [
        EncodedAarch64FixupSite {
            offset: sites[0].offset + 4,
            ..sites[0]
        },
        EncodedAarch64FixupSite {
            inst: InstId(sites[0].inst.0 + 1),
            ..sites[0]
        },
        EncodedAarch64FixupSite {
            placeholder_word: 0x14000000,
            ..sites[0]
        },
        EncodedAarch64FixupSite {
            fixup_index: 1,
            ..sites[0]
        },
    ] {
        assert!(compare_emission(&code, &[altered], &code, &sites).is_err());
        assert!(validate_core_aarch64_fixup_sites(&machine, &code, &fixups, &[altered]).is_err());
    }
}

#[test]
fn call_binding_refuses_target_source_digest_symbol_and_external_mutations() {
    let (lir, machine) = fixture();
    let (_, fixups, sites) = encode_function_with_fixups_and_sites(&machine).unwrap();
    let fixup = fixups.iter().next().unwrap();
    authenticate_call_site(
        &lir,
        &machine,
        &sites[0],
        fixup,
        trust_ir::FuncId::new(0),
        "leaf",
    )
    .unwrap();
    assert!(
        authenticate_call_site(
            &lir,
            &machine,
            &sites[0],
            fixup,
            trust_ir::FuncId::new(1),
            "leaf"
        )
        .is_err()
    );
    assert!(
        authenticate_call_site(
            &lir,
            &machine,
            &sites[0],
            fixup,
            trust_ir::FuncId::new(0),
            "foreign"
        )
        .is_err()
    );
    let external = crate::macho::fixup::Fixup::branch_sym(sites[0].offset, "leaf".into());
    assert!(
        authenticate_call_site(
            &lir,
            &machine,
            &sites[0],
            &external,
            trust_ir::FuncId::new(0),
            "leaf"
        )
        .is_err()
    );
    let mut stale_source = lir.clone();
    stale_source
        .blocks
        .get_mut(&lir.entry_block)
        .unwrap()
        .instructions[0]
        .args
        .push(trust_cg_lower::instructions::Value(77));
    assert!(
        authenticate_call_site(
            &stale_source,
            &machine,
            &sites[0],
            fixup,
            trust_ir::FuncId::new(0),
            "leaf"
        )
        .is_err()
    );
    let mut altered = machine.clone();
    altered.insts[0].operands[0] = O::Symbol("foreign".into());
    assert!(
        authenticate_call_site(
            &lir,
            &altered,
            &sites[0],
            fixup,
            trust_ir::FuncId::new(0),
            "leaf"
        )
        .is_err()
    );
    let mut altered = machine.clone();
    altered.insts[0]
        .flags
        .remove(trust_cg_ir::InstFlags::EXACT_MODULE_CALL);
    assert!(
        authenticate_call_site(
            &lir,
            &altered,
            &sites[0],
            fixup,
            trust_ir::FuncId::new(0),
            "leaf"
        )
        .is_err()
    );
}

#[test]
fn final_layout_keeps_normal_padding_and_refuses_invalid_extents() {
    let mut image = Vec::new();
    let leaf = 0xd65f03c0u32.to_le_bytes();
    assert_eq!(append_function(&mut image, &leaf, 2).unwrap(), 0..4);
    assert_eq!(append_function(&mut image, &leaf, 4).unwrap(), 16..20);
    for word in image[4..16].as_chunks::<4>().0 {
        assert_eq!(*word, 0xd503201fu32.to_le_bytes());
    }
    assert!(append_function(&mut image, &leaf, 13).is_err());
    assert!(append_function(&mut image, &[0], 2).is_err());
}

#[cfg(target_arch = "aarch64")]
#[test]
fn typed_patch_requires_exact_unpatched_bl_and_decodes_actual_backward_target() {
    let mut image = Vec::new();
    image.extend_from_slice(&0xd65f03c0u32.to_le_bytes());
    image.extend_from_slice(&0x94000000u32.to_le_bytes());
    patch_defined_bl(&mut image, 4, 0).unwrap();
    assert_eq!(
        u32::from_le_bytes(image[4..8].try_into().unwrap()),
        0x97ffffff
    );
    assert!(patch_defined_bl(&mut image, 4, 0).is_err()); // No second patch.
    for word in [0x14000000u32, 0x94000001, 0xd63f0000, 0xd503201f] {
        let mut bytes = word.to_le_bytes().to_vec();
        bytes.extend_from_slice(&0xd65f03c0u32.to_le_bytes());
        assert!(patch_defined_bl(&mut bytes, 0, 4).is_err());
    }
    let mut bytes = 0x94000000u32.to_le_bytes().repeat(2);
    assert!(patch_defined_bl(&mut bytes, 1, 4).is_err());
    assert!(patch_defined_bl(&mut bytes, 0, 2).is_err());
    assert!(patch_defined_bl(&mut bytes, 0, 8).is_err());
}

#[test]
fn retained_standard_frame_metadata_and_actual_complete_words_must_agree() {
    let frame = crate::frame::FrameLayout {
        callee_saved_pairs: vec![crate::frame::CalleeSavedPair {
            reg1: trust_cg_ir::regs::PReg::new(29),
            reg2: trust_cg_ir::regs::PReg::new(30),
            fp_offset: 0,
            is_fpr: false,
        }],
        callee_saved_area_size: 16,
        spill_area_size: 0,
        local_area_size: 0,
        outgoing_arg_area_size: 0,
        total_frame_size: 16,
        uses_frame_pointer: true,
        is_leaf: false,
        uses_red_zone: false,
        fp_to_spill_offset: 0,
        has_dynamic_alloc: false,
    };
    let code: Vec<_> = [
        0xa9bf7bfdu32,
        0x910003fd,
        0x94000000,
        0xa8c17bfd,
        0xd65f03c0,
    ]
    .into_iter()
    .flat_map(u32::to_le_bytes)
    .collect();
    standard_frame(Some(&frame), &code).unwrap();
    assert!(standard_frame(None, &code).is_err());
    let mut changed = frame.clone();
    changed.total_frame_size = 32;
    assert!(standard_frame(Some(&changed), &code).is_err());
    let mut changed = frame.clone();
    changed.spill_area_size = 16;
    assert!(standard_frame(Some(&changed), &code).is_err());
    let mut changed = frame.clone();
    changed.has_dynamic_alloc = true;
    assert!(standard_frame(Some(&changed), &code).is_err());
    let mut changed = frame.clone();
    changed.uses_red_zone = true;
    assert!(standard_frame(Some(&changed), &code).is_err());
    let mut changed = frame.clone();
    changed.callee_saved_pairs[0].reg2 = trust_cg_ir::regs::PReg::new(28);
    assert!(standard_frame(Some(&changed), &code).is_err());
    for offset in [0, 4, code.len() - 8, code.len() - 4] {
        let mut altered = code.clone();
        altered[offset] ^= 1;
        assert!(standard_frame(Some(&frame), &altered).is_err());
    }
}
