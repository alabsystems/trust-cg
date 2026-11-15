// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Final-layout cross-check: positive controls on real encoder output after
//! loop-head alignment and after branch relaxation, and fail-closed
//! corruption controls for words, offsets, tables and fixups.

use super::*;
use crate::macho::fixup::{Fixup, FixupList};
use crate::pipeline::{Pipeline, PipelineConfig, PipelineError};
use std::collections::HashMap;
use trust_cg_ir::function::{JumpTableData, Signature, Type};
use trust_cg_ir::regs::{W2, X0, X1, X3, X4, X16, X30};

fn word(code: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes(code[offset..offset + 4].try_into().unwrap())
}

fn set_word(code: &mut [u8], offset: usize, value: u32) {
    code[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
}

fn add(func: &mut MachFunction, block: BlockId, inst: MachInst) -> InstId {
    let id = func.push_inst(inst);
    func.append_inst(block, id);
    id
}

fn edge(func: &mut MachFunction, from: BlockId, to: BlockId) {
    func.blocks[from.0 as usize].succs.push(to);
    func.blocks[to.0 as usize].preds.push(from);
}

/// entry(6 adds) -> head(add; cbnz head) -> exit(ret), with exact CFG
/// metadata, before loop-head alignment and branch resolution.
fn loop_fixture() -> (MachFunction, BlockId, InstId) {
    let mut f = MachFunction::new(
        "aligned_loop".into(),
        Signature::new(vec![Type::I64, Type::I64], vec![Type::I64]),
    );
    let entry = f.entry;
    for _ in 0..6 {
        add(
            &mut f,
            entry,
            MachInst::new(
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X0),
                    MachOperand::Imm(1),
                ],
            ),
        );
    }
    let head = f.create_block();
    let exit = f.create_block();
    add(
        &mut f,
        head,
        MachInst::new(
            AArch64Opcode::SubRI,
            vec![
                MachOperand::PReg(X1),
                MachOperand::PReg(X1),
                MachOperand::Imm(1),
            ],
        ),
    );
    let back = add(
        &mut f,
        head,
        MachInst::new(
            AArch64Opcode::Cbnz,
            vec![MachOperand::PReg(X1), MachOperand::Block(head)],
        ),
    );
    add(
        &mut f,
        exit,
        MachInst::new(AArch64Opcode::Ret, vec![MachOperand::PReg(X30)]).with_implicit_uses(&[X0]),
    );
    edge(&mut f, entry, head);
    edge(&mut f, head, head);
    edge(&mut f, head, exit);
    f.blocks[head.0 as usize].loop_depth = 1;
    (f, head, back)
}

/// [`loop_fixture`] aligned and resolved exactly as the pipeline's final
/// phase does.
fn aligned_loop() -> (MachFunction, BlockId, InstId) {
    let (mut f, head, back) = loop_fixture();
    assert!(crate::loop_align::align_innermost_loop_heads(&mut f));
    crate::pipeline::resolve_branches(&mut f).unwrap();
    (f, head, back)
}

fn encode(pipeline: &Pipeline, func: &MachFunction) -> (Vec<u8>, FixupList, HashMap<BlockId, u32>) {
    crate::pipeline::encode_function_with_fixups_and_blocks_for_pipeline(pipeline, func).unwrap()
}

fn offset_of(func: &MachFunction, target: InstId) -> usize {
    let mut offset = 0;
    for &block in &func.block_order {
        for &id in &func.block(block).insts {
            if id == target {
                return offset;
            }
            offset += 4 * usize::from(!func.inst(id).is_pseudo());
        }
    }
    unreachable!("instruction is laid out")
}

#[test]
fn aligned_loop_encodes_on_both_policies_and_object_formats() {
    for triple in ["aarch64-apple-darwin", "aarch64-unknown-linux-gnu"] {
        let config = PipelineConfig {
            target_triple: triple.into(),
            ..PipelineConfig::for_host_aarch64()
        };
        let (func, head, _) = aligned_loop();
        // Padding moved the head to a 32-byte boundary before resolution.
        let padded = func
            .insts
            .iter()
            .filter(|inst| inst.opcode == AArch64Opcode::AlignNop)
            .count();
        assert_eq!(padded, 2);
        for pipeline in [
            Pipeline::new(config.clone()),
            Pipeline::new(config.clone()).with_proof_grade_aarch64_publication(),
        ] {
            let (code, fixups, blocks) = encode(&pipeline, &func);
            assert_eq!(blocks[&head], 32);
            assert!(fixups.is_empty());
            check_final_layout(&func, &code, Some(&fixups), &blocks, true).unwrap();
        }
    }
}

#[test]
fn corrupted_branch_words_and_stale_offsets_fail_closed() {
    let pipeline = Pipeline::new(PipelineConfig::for_host_aarch64());
    let (func, head, back) = aligned_loop();
    let (code, fixups, blocks) = encode(&pipeline, &func);
    let at = offset_of(&func, back);

    // A branch word whose displacement differs from the layout.
    let mut wrong = code.clone();
    set_word(&mut wrong, at, word(&code, at) ^ (1 << 5));
    assert!(matches!(
        check_final_layout(&func, &wrong, Some(&fixups), &blocks, false),
        Err(LayoutCrossCheckError::Displacement { .. })
    ));
    // A word of the wrong class for its intent.
    let mut wrong = code.clone();
    set_word(&mut wrong, at, 0xD503_201F);
    assert!(matches!(
        check_final_layout(&func, &wrong, Some(&fixups), &blocks, false),
        Err(LayoutCrossCheckError::WordClass { .. })
    ));
    // An encoder block map that drifted from the final layout.
    let mut drifted = blocks.clone();
    drifted.insert(head, 28);
    assert!(matches!(
        check_final_layout(&func, &code, Some(&fixups), &drifted, false),
        Err(LayoutCrossCheckError::BlockOffset { .. })
    ));
    // Late padding inserted after resolution: stale immediates and bytes.
    let mut late = func.clone();
    let pad = late.push_inst(MachInst::new(AArch64Opcode::AlignNop, vec![]));
    late.blocks[head.0 as usize].insts.insert(0, pad);
    assert!(check_final_layout(&late, &code, Some(&fixups), &blocks, false).is_err());
    let late_blocks: HashMap<_, _> = late
        .block_order
        .iter()
        .map(|block| (*block, blocks[block] + 4 * u32::from(block.0 > head.0)))
        .collect();
    let mut late_code = code.clone();
    late_code.splice(
        blocks[&head] as usize..blocks[&head] as usize,
        [0x1f, 0x20, 0x03, 0xd5],
    );
    assert!(matches!(
        check_final_layout(&late, &late_code, Some(&fixups), &late_blocks, false),
        Err(LayoutCrossCheckError::BranchTarget { .. })
    ));
    // A trailing byte beyond the body.
    let mut long = code.clone();
    long.extend_from_slice(&[0; 4]);
    assert!(matches!(
        check_final_layout(&func, &long, Some(&fixups), &blocks, false),
        Err(LayoutCrossCheckError::TrailingBytes { .. })
    ));
}

#[test]
fn cfg_authority_binds_encoded_edges_to_recorded_successors() {
    let pipeline = Pipeline::new(PipelineConfig::for_host_aarch64());
    let (func, head, back) = aligned_loop();
    let (code, fixups, blocks) = encode(&pipeline, &func);
    let at = offset_of(&func, back);
    // Retarget the loop branch to the entry block, consistently in intent and
    // bytes: a valid block start, but not a recorded successor of `head`.
    let mut retargeted = func.clone();
    let displacement = -(at as i64) / 4;
    retargeted.insts[back.0 as usize].operands[1] = MachOperand::Imm(displacement);
    let mut bytes = code.clone();
    let cbnz = (word(&code, at) & !(0x7_FFFF << 5)) | (((displacement as u32) & 0x7_FFFF) << 5);
    set_word(&mut bytes, at, cbnz);
    check_final_layout(&retargeted, &bytes, Some(&fixups), &blocks, false).unwrap();
    assert!(matches!(
        check_final_layout(&retargeted, &bytes, Some(&fixups), &blocks, true),
        Err(LayoutCrossCheckError::SuccessorMismatch { block, .. }) if block == head
    ));
    // A fallthrough the recorded CFG does not name.
    let mut metadata = func.clone();
    let exit = metadata.block_order[2];
    metadata.blocks[head.0 as usize]
        .succs
        .retain(|block| *block != exit);
    assert!(matches!(
        check_final_layout(&metadata, &code, Some(&fixups), &blocks, true),
        Err(LayoutCrossCheckError::FallthroughMismatch { .. })
    ));
    // The proof-grade encoder itself refuses the retargeted function.
    let proof_grade =
        Pipeline::new(PipelineConfig::for_host_aarch64()).with_proof_grade_aarch64_publication();
    assert!(matches!(
        crate::pipeline::encode_function_with_fixups_and_blocks_for_pipeline(
            &proof_grade,
            &retargeted
        ),
        Err(PipelineError::Aarch64LayoutCrossCheck {
            error: LayoutCrossCheckError::SuccessorMismatch { .. },
            ..
        })
    ));
}

/// `ADD x3,x3,#1; LDXR x0,[x4]; ADD x1,x0,x3; STXR w2,x1,[store_base];
/// CBNZ w2,-3; RET`: the exclusive retry loop `crate::llsc` expands in place
/// after register allocation, whose backward `CBNZ` lands on the loop head
/// at byte 4, inside the block and not at a block start.
fn llsc_loop(store_base: trust_cg_ir::regs::PReg) -> MachFunction {
    let mut f = MachFunction::new(
        "llsc_loop".into(),
        Signature::new(vec![Type::I64, Type::I64], vec![Type::I64]),
    );
    let entry = f.entry;
    for inst in [
        MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                MachOperand::PReg(X3),
                MachOperand::PReg(X3),
                MachOperand::Imm(1),
            ],
        ),
        MachInst::new(
            AArch64Opcode::Ldxr,
            vec![MachOperand::PReg(X0), MachOperand::PReg(X4)],
        ),
        MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::PReg(X1),
                MachOperand::PReg(X0),
                MachOperand::PReg(X3),
            ],
        ),
        MachInst::new(
            AArch64Opcode::Stxr,
            vec![
                MachOperand::PReg(W2),
                MachOperand::PReg(X1),
                MachOperand::PReg(store_base),
            ],
        ),
        MachInst::new(
            AArch64Opcode::Cbnz,
            vec![MachOperand::PReg(W2), MachOperand::Imm(-3)],
        ),
        MachInst::new(AArch64Opcode::Ret, vec![MachOperand::PReg(X30)]).with_implicit_uses(&[X0]),
    ] {
        add(&mut f, entry, inst);
    }
    f
}

#[test]
fn expanded_llsc_loop_branch_is_a_validated_intra_block_target() {
    let pipeline = Pipeline::new(PipelineConfig::for_host_aarch64());
    let func = llsc_loop(X4);
    let (code, fixups, blocks) = encode(&pipeline, &func);
    // The exact template is admitted on both policies, including the
    // proof-grade encoder's own cross-check under CFG authority.
    check_final_layout(&func, &code, Some(&fixups), &blocks, false).unwrap();
    check_final_layout(&func, &code, Some(&fixups), &blocks, true).unwrap();
    let proof_grade =
        Pipeline::new(PipelineConfig::for_host_aarch64()).with_proof_grade_aarch64_publication();
    crate::pipeline::encode_function_with_fixups_and_blocks_for_pipeline(&proof_grade, &func)
        .unwrap();
    // The waiver covers only the block-start requirement: a retry word whose
    // displacement disagrees with the intent still fails closed.
    let at = 16;
    let mut short = code.clone();
    let cbnz = (word(&code, at) & !(0x7_FFFF << 5)) | (((-2i64 as u32) & 0x7_FFFF) << 5);
    set_word(&mut short, at, cbnz);
    assert!(matches!(
        check_final_layout(&func, &short, Some(&fixups), &blocks, false),
        Err(LayoutCrossCheckError::Displacement {
            offset: 16,
            encoded: -2,
            expected: -3
        })
    ));
    // A near miss of the template (the store-exclusive names another base)
    // keeps the ordinary intra-block refusal for the same backward branch:
    // the cross-check refuses it on the same bytes with that base patched
    // into the STXR's Rn field, and the pipeline's structural validator
    // already refuses the intent before encoding.
    let near_miss = llsc_loop(X3);
    let mut other_base = code.clone();
    let stxr = (word(&code, 12) & !(0x1F << 5)) | (3 << 5);
    set_word(&mut other_base, 12, stxr);
    assert!(matches!(
        check_final_layout(&near_miss, &other_base, Some(&fixups), &blocks, false),
        Err(LayoutCrossCheckError::BranchTarget {
            offset: 16,
            target: 4
        })
    ));
    assert!(matches!(
        crate::pipeline::encode_function_with_fixups_and_blocks_for_pipeline(&pipeline, &near_miss),
        Err(PipelineError::MalformedAarch64Function { .. })
    ));
}

/// entry: ADR x16, table; BR x16 -- b1: RET -- b2: RET; table [b1, b2].
fn jump_table() -> (MachFunction, Vec<u8>, HashMap<BlockId, u32>) {
    let mut f = MachFunction::new("jump".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let b1 = f.create_block();
    let b2 = f.create_block();
    f.jump_tables.push(JumpTableData {
        min_val: 0,
        targets: vec![b1, b2],
    });
    add(
        &mut f,
        entry,
        MachInst::new(
            AArch64Opcode::Adr,
            vec![MachOperand::PReg(X16), MachOperand::JumpTableIndex(0)],
        ),
    );
    add(
        &mut f,
        entry,
        MachInst::new(AArch64Opcode::Br, vec![MachOperand::PReg(X16)]),
    );
    for block in [b1, b2] {
        add(
            &mut f,
            block,
            MachInst::new(AArch64Opcode::Ret, vec![MachOperand::PReg(X30)]),
        );
        edge(&mut f, entry, block);
    }
    let mut code = Vec::new();
    for value in [
        crate::aarch64::encoding_mem::encode_adr(16, 16).unwrap(),
        crate::aarch64::encode_instruction(f.inst(InstId(1))).unwrap(),
        0xD65F_03C0,
        0xD65F_03C0,
    ] {
        code.extend_from_slice(&value.to_le_bytes());
    }
    code.extend_from_slice(&(-8i32).to_le_bytes());
    code.extend_from_slice(&(-4i32).to_le_bytes());
    let blocks = HashMap::from([(entry, 0), (b1, 8), (b2, 12)]);
    (f, code, blocks)
}

#[test]
fn jump_table_address_and_entries_are_rederived() {
    let (func, code, blocks) = jump_table();
    let fixups = FixupList::new();
    check_final_layout(&func, &code, Some(&fixups), &blocks, true).unwrap();
    let mut wrong = code.clone();
    wrong[16..20].copy_from_slice(&(-4i32).to_le_bytes());
    assert!(matches!(
        check_final_layout(&func, &wrong, Some(&fixups), &blocks, false),
        Err(LayoutCrossCheckError::JumpTableEntry { entry: 0, .. })
    ));
    let mut wrong = code.clone();
    set_word(
        &mut wrong,
        0,
        crate::aarch64::encoding_mem::encode_adr(20, 16).unwrap(),
    );
    assert!(matches!(
        check_final_layout(&func, &wrong, Some(&fixups), &blocks, false),
        Err(LayoutCrossCheckError::JumpTableAddress { .. })
    ));
    let mut short = code.clone();
    short.truncate(20);
    assert!(check_final_layout(&func, &short, Some(&fixups), &blocks, false).is_err());
    let mut unrecorded = func.clone();
    unrecorded.blocks[0].succs.pop();
    assert!(matches!(
        check_final_layout(&unrecorded, &code, Some(&fixups), &blocks, true),
        Err(LayoutCrossCheckError::JumpTableSuccessor { .. })
    ));
}

/// A resolved tail call may leave the function, but never into the function's
/// own trailing jump-table data.
#[test]
fn resolved_tail_call_never_lands_in_jump_table_data() {
    let (mut func, mut code, blocks) = jump_table();
    let fixups = FixupList::new();
    // b2's RET at byte 12 becomes a resolved tail call.
    for (displacement, lands_in_table) in [(1i64, true), (2, true), (3, false), (-4, false)] {
        func.insts[3] = MachInst::new(
            AArch64Opcode::TailCall,
            vec![MachOperand::Imm(displacement)],
        );
        set_word(
            &mut code,
            12,
            0x1400_0000 | (displacement as u32 & 0x03FF_FFFF),
        );
        let result = check_final_layout(&func, &code, Some(&fixups), &blocks, false);
        if lands_in_table {
            assert!(
                matches!(
                    result,
                    Err(LayoutCrossCheckError::BranchTarget { offset: 12, .. })
                ),
                "tail call +{displacement} into the table was accepted: {result:?}"
            );
        } else {
            result.unwrap();
        }
    }
}

/// BL callee; ADRP x0, g; ADD x0, x0, :lo12:g; RET with their fixups.
fn symbolic() -> (MachFunction, Vec<u8>, FixupList, HashMap<BlockId, u32>) {
    let mut f = MachFunction::new("symbolic".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    add(
        &mut f,
        entry,
        MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("callee".into())],
        ),
    );
    add(
        &mut f,
        entry,
        MachInst::new(
            AArch64Opcode::Adrp,
            vec![MachOperand::PReg(X0), MachOperand::Symbol("g".into())],
        ),
    );
    add(
        &mut f,
        entry,
        MachInst::new(
            AArch64Opcode::AddPCRel,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::Symbol("g".into()),
            ],
        ),
    );
    add(
        &mut f,
        entry,
        MachInst::new(AArch64Opcode::Ret, vec![MachOperand::PReg(X30)]),
    );
    let mut code = Vec::new();
    for value in [0x9400_0000u32, 0x9000_0000, 0x9100_0000, 0xD65F_03C0] {
        code.extend_from_slice(&value.to_le_bytes());
    }
    let mut fixups = FixupList::new();
    fixups.push(Fixup::branch_sym(0, "callee".into()));
    for (offset, kind) in [
        (4, AArch64RelocKind::Page21),
        (8, AArch64RelocKind::Pageoff12),
    ] {
        fixups.push(Fixup {
            offset,
            kind,
            tls_model: None,
            target: crate::macho::FixupTarget::NamedSymbol("g".into()),
            addend: 0,
        });
    }
    let blocks = HashMap::from([(entry, 0)]);
    (f, code, fixups, blocks)
}

#[test]
fn fixups_bind_exact_symbolic_sites_and_zero_placeholders() {
    let (func, code, fixups, blocks) = symbolic();
    check_final_layout(&func, &code, Some(&fixups), &blocks, true).unwrap();
    // A nonzero relocated field would add a hidden addend.
    for (offset, value) in [(0, 0x9400_0001u32), (4, 0xB000_0000), (8, 0x9100_0400)] {
        let mut wrong = code.clone();
        set_word(&mut wrong, offset, value);
        assert!(
            matches!(
                check_final_layout(&func, &wrong, Some(&fixups), &blocks, false),
                Err(LayoutCrossCheckError::FixupPlaceholder { .. })
            ),
            "placeholder at {offset}"
        );
    }
    // A kind that patches another word class.
    let mut swapped = fixups.clone();
    swapped.as_mut_slice()[2].kind = AArch64RelocKind::Page21;
    assert!(matches!(
        check_final_layout(&func, &code, Some(&swapped), &blocks, false),
        Err(LayoutCrossCheckError::FixupPlaceholder { .. })
    ));
    // A fixup moved off its instruction, duplicated, or dropped.
    let mut moved = fixups.clone();
    moved.as_mut_slice()[0].offset = 12;
    assert!(matches!(
        check_final_layout(&func, &code, Some(&moved), &blocks, false),
        Err(LayoutCrossCheckError::FixupSite { .. })
    ));
    let mut duplicated = fixups.clone();
    duplicated.push(Fixup::branch_sym(0, "callee".into()));
    assert!(matches!(
        check_final_layout(&func, &code, Some(&duplicated), &blocks, false),
        Err(LayoutCrossCheckError::DuplicateFixup { .. })
    ));
    let mut dropped = FixupList::new();
    for fixup in fixups.iter().skip(1) {
        dropped.push(fixup.clone());
    }
    assert!(matches!(
        check_final_layout(&func, &code, Some(&dropped), &blocks, false),
        Err(LayoutCrossCheckError::MissingFixup { .. })
    ));
}

/// Adversarial: a fixup on the right instruction, with the right kind and a
/// zero placeholder, that names a different symbol (or flips the exact-module
/// binding) relocates the call or address to another definition. Site, kind
/// and placeholder agreement alone cannot see it; the fixup must also name
/// exactly the symbol its instruction names.
#[test]
fn fixups_bind_the_symbol_their_instruction_names() {
    use crate::macho::FixupTarget;
    let (func, code, fixups, blocks) = symbolic();
    for (index, target) in [
        (0, FixupTarget::NamedSymbol("other".into())),
        (0, FixupTarget::ExactNamedSymbol("callee".into())),
        (1, FixupTarget::NamedSymbol("h".into())),
        (1, FixupTarget::Symbol(0)),
        (2, FixupTarget::ExactNamedSymbol("g".into())),
    ] {
        let mut wrong = fixups.clone();
        wrong.as_mut_slice()[index].target = target.clone();
        assert!(
            matches!(
                check_final_layout(&func, &code, Some(&wrong), &blocks, false),
                Err(LayoutCrossCheckError::FixupSymbol { index: refused, .. }) if refused == index
            ),
            "fixup {index} retargeted to {target:?} was accepted"
        );
    }
    // Swapping the symbols of two otherwise valid page fixups.
    let mut swapped = fixups.clone();
    swapped.as_mut_slice()[1].target = FixupTarget::NamedSymbol("callee".into());
    swapped.as_mut_slice()[0].target = FixupTarget::NamedSymbol("g".into());
    assert!(matches!(
        check_final_layout(&func, &code, Some(&swapped), &blocks, false),
        Err(LayoutCrossCheckError::FixupSymbol { .. })
    ));
    // An exact in-module call must keep its exact binding, and only it.
    let mut exact = func.clone();
    exact.insts[0]
        .flags
        .insert(trust_cg_ir::InstFlags::EXACT_MODULE_CALL);
    assert!(matches!(
        check_final_layout(&exact, &code, Some(&fixups), &blocks, false),
        Err(LayoutCrossCheckError::FixupSymbol { index: 0, .. })
    ));
    let mut exact_fixups = fixups.clone();
    exact_fixups.as_mut_slice()[0].target = FixupTarget::ExactNamedSymbol("callee".into());
    check_final_layout(&exact, &code, Some(&exact_fixups), &blocks, true).unwrap();
}

#[test]
fn pc_relative_literals_stay_inside_the_image() {
    let mut f = MachFunction::new("literal".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let load = add(
        &mut f,
        entry,
        MachInst::new(
            AArch64Opcode::LdrLiteral,
            vec![MachOperand::PReg(X0), MachOperand::Imm(1)],
        ),
    );
    add(
        &mut f,
        entry,
        MachInst::new(AArch64Opcode::Ret, vec![MachOperand::PReg(X30)]),
    );
    let blocks = HashMap::from([(entry, 0)]);
    let mut code = Vec::new();
    code.extend_from_slice(
        &crate::aarch64::encode_instruction(f.inst(load))
            .unwrap()
            .to_le_bytes(),
    );
    code.extend_from_slice(&0xD65F_03C0u32.to_le_bytes());
    // Offset +4 names the 8-byte window [4, 12) of an 8-byte image.
    assert!(matches!(
        check_final_layout(&f, &code, None, &blocks, false),
        Err(LayoutCrossCheckError::PcRelativeOutOfImage { .. })
    ));
    f.insts[load.0 as usize].operands[1] = MachOperand::Imm(-1);
    set_word(
        &mut code,
        0,
        crate::aarch64::encode_instruction(f.inst(load)).unwrap(),
    );
    assert!(check_final_layout(&f, &code, None, &blocks, false).is_err());
}

/// A conditional branch beyond +/-1 MiB relaxes into `B.cond_inv +2; B far`.
/// The relaxed bytes are checked against symbolic intents re-derived from the
/// relaxed layout, never against the relaxer's own resolved sequence.
#[test]
fn relaxed_far_branch_is_rederived_from_final_layout() {
    let mut f = MachFunction::new("far".into(), Signature::new(vec![], vec![]));
    let entry = f.entry;
    let filler = f.create_block();
    let far = f.create_block();
    add(
        &mut f,
        entry,
        MachInst::new(
            AArch64Opcode::BCond,
            vec![MachOperand::Imm(0), MachOperand::Block(far)],
        ),
    );
    for _ in 0..(1 << 18) + 8 {
        add(&mut f, filler, MachInst::new(AArch64Opcode::Nop, vec![]));
        let last = *f.blocks[filler.0 as usize].insts.last().unwrap();
        f.insts[last.0 as usize].flags = trust_cg_ir::InstFlags::EMPTY;
    }
    add(
        &mut f,
        far,
        MachInst::new(AArch64Opcode::Ret, vec![MachOperand::PReg(X30)]),
    );
    edge(&mut f, entry, far);
    edge(&mut f, entry, filler);
    edge(&mut f, filler, far);
    let relaxed = crate::relax::relax_branches(&mut f).unwrap();
    assert_eq!(
        f.blocks[entry.0 as usize].insts.len(),
        2,
        "relaxed in place"
    );
    let mut code = Vec::new();
    for inst in &relaxed.instructions {
        code.extend_from_slice(
            &crate::aarch64::encode_instruction(inst)
                .unwrap()
                .to_le_bytes(),
        );
    }
    let blocks: HashMap<_, _> = f
        .block_order
        .iter()
        .map(|block| (*block, relaxed.block_offsets[block.0 as usize]))
        .collect();
    check_final_layout(&f, &code, None, &blocks, true).unwrap();
    // The far B must land exactly on the recomputed far-block start.
    let mut wrong = code.clone();
    set_word(&mut wrong, 4, word(&code, 4) + 1);
    assert!(matches!(
        check_final_layout(&f, &wrong, None, &blocks, false),
        Err(LayoutCrossCheckError::Displacement { offset: 4, .. })
    ));
    // The skip must remain exactly one instruction.
    let mut wrong = code.clone();
    set_word(&mut wrong, 0, word(&code, 0) + (1 << 5));
    assert!(check_final_layout(&f, &wrong, None, &blocks, false).is_err());
    // A relaxer that misreported the far block's start.
    let mut drifted = blocks.clone();
    *drifted.get_mut(&far).unwrap() += 4;
    assert!(matches!(
        check_final_layout(&f, &code, None, &drifted, false),
        Err(LayoutCrossCheckError::BlockOffset { .. })
    ));
}

#[test]
fn proof_grade_routes_refuse_ambient_late_layout_controls() {
    let (func, _, _) = aligned_loop();
    for control in crate::pipeline::AARCH64_LATE_LAYOUT_CONTROLS {
        trust_cg_process_env::with_env_overrides(&[(*control, "1")], || {
            let proof_grade = Pipeline::new(PipelineConfig::for_host_aarch64())
                .with_proof_grade_aarch64_publication();
            match crate::pipeline::encode_function_with_fixups_and_blocks_for_pipeline(
                &proof_grade,
                &func,
            ) {
                Err(PipelineError::AmbientLateLayoutControl {
                    control: refused, ..
                }) => {
                    assert_eq!(refused, *control)
                }
                other => panic!("{control} was not refused: {other:?}"),
            }
            // The compatibility route keeps its legacy switch semantics.
            let compatibility = Pipeline::new(PipelineConfig::for_host_aarch64());
            crate::pipeline::encode_function_with_fixups_and_blocks_for_pipeline(
                &compatibility,
                &func,
            )
            .unwrap();
        });
    }
}

/// Adversarial: the late-layout passes read their controls from the process
/// environment, not from thread-local overrides. A removal override must not
/// hide a process-level control from the proof-grade refusal while the pass
/// still honors it. Cargo runs unit tests concurrently, so the process-level
/// control is set only in an isolated child running this same test.
#[test]
fn proof_grade_refusal_sees_process_controls_hidden_by_removal_overrides() {
    const CHILD_MARKER: &str = "LAYOUT_XCHECK_PROCESS_CONTROL_CHILD";
    const CONTROL: &str = "TCG_NO_LOOP_HEAD_ALIGN";
    if std::env::var_os(CHILD_MARKER).is_none() {
        let output = std::process::Command::new(
            std::env::current_exe().expect("current trust-cg-codegen test executable"),
        )
        .arg(
            "aarch64::layout_crosscheck::tests::\
             proof_grade_refusal_sees_process_controls_hidden_by_removal_overrides",
        )
        .arg("--exact")
        .arg("--nocapture")
        .env(CONTROL, "1")
        .env(CHILD_MARKER, "1")
        .output()
        .expect("run isolated process-control child test");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success(),
            "process-control child failed:\nstdout:\n{}\nstderr:\n{stderr}",
            String::from_utf8_lossy(&output.stdout)
        );
        assert!(
            stderr.contains("[TCG-A64-LATE-LAYOUT-CHILD-PASS]"),
            "child test did not execute the refusal assertion: {stderr}"
        );
        return;
    }
    trust_cg_process_env::with_env_overrides_removed(&[CONTROL], || {
        assert!(trust_cg_process_env::var_os(CONTROL).is_none());
        let (mut func, _, _) = loop_fixture();
        // The pass still reads the process environment and is steered.
        assert!(!crate::loop_align::align_innermost_loop_heads(&mut func));
        crate::pipeline::resolve_branches(&mut func).unwrap();
        let proof_grade = Pipeline::new(PipelineConfig::for_host_aarch64())
            .with_proof_grade_aarch64_publication();
        match crate::pipeline::encode_function_with_fixups_and_blocks_for_pipeline(
            &proof_grade,
            &func,
        ) {
            Err(PipelineError::AmbientLateLayoutControl { control, .. }) => {
                assert_eq!(control, CONTROL)
            }
            other => panic!("process-level {CONTROL} hidden by a removal override: {other:?}"),
        }
    });
    eprintln!("[TCG-A64-LATE-LAYOUT-CHILD-PASS]");
}

#[test]
fn proof_grade_routes_ignore_integrity_downgrades() {
    // Clobber x1 before its only read: a reaching-definition violation. The
    // compatibility route honors the diagnostic `off` downgrade; the
    // proof-grade route forces Enforce and refuses the stream.
    let mut f = MachFunction::new(
        "downgrade".into(),
        Signature::new(vec![Type::I64], vec![Type::I64]),
    );
    let entry = f.entry;
    add(
        &mut f,
        entry,
        MachInst::new(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::PReg(trust_cg_ir::regs::X9),
            ],
        ),
    );
    add(
        &mut f,
        entry,
        MachInst::new(AArch64Opcode::Ret, vec![MachOperand::PReg(X30)]).with_implicit_uses(&[X0]),
    );
    trust_cg_process_env::with_env_overrides(
        &[("TCG_AARCH64_POST_RA_REACHING_DEF", "off")],
        || {
            let compatibility = Pipeline::new(PipelineConfig::for_host_aarch64());
            let proof_grade = Pipeline::new(PipelineConfig::for_host_aarch64())
                .with_proof_grade_aarch64_publication();
            assert!(
                crate::pipeline::encode_function_with_fixups_for_pipeline(&compatibility, &f)
                    .is_ok()
            );
            assert!(matches!(
                crate::pipeline::encode_function_with_fixups_for_pipeline(&proof_grade, &f),
                Err(PipelineError::RegAlloc(message)) if message.contains("[TCG-A64-REACHING-DEF]")
            ));
        },
    );
}

/// Every environment read in the late-layout modules that can change bytes
/// is in the refused list; only named trace/dump switches are exempt.
#[test]
fn late_layout_control_list_covers_every_module_env_read() {
    const DIAGNOSTIC_ONLY: &[&str] = &["TCG_LOOP_ALIGN_TRACE", "TCG_DUMP_POSTIDX_LATE"];
    for source in [
        include_str!("../loop_align.rs"),
        include_str!("../post_index_late.rs"),
    ] {
        let code = source.split("#[cfg(test)]").next().unwrap();
        for line in code
            .lines()
            .filter(|line| line.contains("env::var") || line.contains("env_lock::var"))
        {
            for name in line.split('"').skip(1).step_by(2) {
                if name.starts_with("TCG_") && !DIAGNOSTIC_ONLY.contains(&name) {
                    assert!(
                        crate::pipeline::AARCH64_LATE_LAYOUT_CONTROLS.contains(&name),
                        "{name} is read by a late-layout pass but not refused"
                    );
                }
            }
        }
    }
}

#[cfg(feature = "verify")]
#[test]
fn rebased_core_placement_refuses_page_sensitive_words_and_literal_classes() {
    use super::check_rebased_function_placement;
    let bytes = |words: &[u32]| {
        words
            .iter()
            .flat_map(|word| word.to_le_bytes())
            .collect::<Vec<_>>()
    };
    // ADRP X0,#0; ADD X0,X0,#32 at function offset4. At origin0,
    // its result is32. Put the identical function at4092 and ADRP now sees
    // page4096, so the result is4128 rather than relocated result4124.
    // This distinguishes page-position dependence from a relative branch.
    let origin = 0u64;
    let relocated = 4092u64;
    let evaluate_page_pair = |base: u64| ((base + 4) & !4095) + 32;
    assert_eq!(evaluate_page_pair(origin), 32);
    assert_ne!(
        evaluate_page_pair(relocated),
        relocated + evaluate_page_pair(origin)
    );
    let image = bytes(&[0xd503201f, 0x90000000, 0x91008000, 0xd65f03c0]);
    assert!(matches!(
        check_rebased_function_placement(&image),
        Err(
            super::RebasedFunctionPlacementError::RebasedPcRelativeWord {
                offset: 4,
                what: "ADR/ADRP",
                ..
            }
        )
    ));

    // All free opcode/V choices in the architectural literal class refuse,
    // including LDR W/X/S/D/Q, LDRSW, PRFM and reserved combinations. Neither
    // immediate bits nor destination bits may evade a placement refusal.
    for opc in 0..4 {
        for vector in 0..2 {
            for immediate in [0, 1, 0x7ffff] {
                for register in [0, 30, 31] {
                    let word =
                        0x18000000 | (opc << 30) | (vector << 26) | (immediate << 5) | register;
                    assert!(
                        check_rebased_function_placement(&bytes(&[word])).is_err(),
                        "{word:#010x}"
                    );
                }
            }
        }
    }
    for page in 0..2 {
        for immediate in [0, 1, 0x1fffff] {
            for register in [0, 30, 31] {
                let word = 0x10000000
                    | (page << 31)
                    | ((immediate & 3) << 29)
                    | ((immediate >> 2) << 5)
                    | register;
                assert!(
                    check_rebased_function_placement(&bytes(&[word])).is_err(),
                    "{word:#010x}"
                );
            }
        }
    }
    for len in [1, 2, 3, 5] {
        assert!(check_rebased_function_placement(&vec![0; len]).is_err());
    }
    // A separately encoded relative edge may not escape this function, even
    // if the broader final-layout owner permits a resolved tail call there.
    for word in [
        0x14000001, 0x94000001, 0x17ffffff, 0x97ffffff, 0x54000020, 0xb4000020, 0x36000020,
        0x54ffffe0, 0xb4ffffe0, 0x3607ffe0,
    ] {
        assert!(
            matches!(
                check_rebased_function_placement(&bytes(&[word])),
                Err(super::RebasedFunctionPlacementError::RebasedBranchOutOfImage { .. })
            ),
            "{word:#010x}"
        );
    }
    assert!(check_rebased_function_placement(&bytes(&[0xd503201f, 0x17ffffff])).is_ok());
    // This check adds no semantic proof credit. Existing CFG and certificate
    // owners must still establish these relative edges and the complete body.
    assert!(
        check_rebased_function_placement(&bytes(&[
            0xd2800540, 0x14000001, 0x54000020, 0xb4000020, 0x36000020, 0xd65f03c0,
        ]))
        .is_ok()
    );
}
