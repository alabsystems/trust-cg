// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Producer retirement and metadata custody, not a certificate or byte proof.

use super::*;
use trust_cg_ir::regs::{NZCV, X0};
use trust_cg_ir::{
    InstFlags, LoweringProvenance, ProofAnnotation, Signature, SourceInstDigest, SourceInstId,
    SourceLoc, TrustIrInstId,
};

fn vr(id: u32, class: RegClass) -> MachOperand {
    MachOperand::VReg(VReg::new(id, class))
}

fn access(opcode: AArch64Opcode, id: u32, class: RegClass, offset: i64) -> MachInst {
    MachInst::new(
        opcode,
        vec![
            vr(id, class),
            vr(10, RegClass::Gpr64),
            MachOperand::Imm(offset),
        ],
    )
}

fn gap() -> MachInst {
    MachInst::new(
        AArch64Opcode::MovR,
        vec![vr(8, RegClass::Gpr64), vr(9, RegClass::Gpr64)],
    )
}

fn function(instructions: Vec<MachInst>) -> (MachFunction, Vec<InstId>) {
    let mut func = MachFunction::new("pair_retirement".into(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    let ids = instructions
        .into_iter()
        .map(|inst| {
            let id = func.push_inst(inst);
            func.append_inst(entry, id);
            id
        })
        .collect();
    func.try_sync_vreg_counter().expect("bounded fixture arena");
    (func, ids)
}

fn same(actual: &MachInst, original: &MachInst) {
    assert_eq!(actual.opcode, original.opcode);
    assert_eq!(actual.operands, original.operands);
    assert_eq!(actual.flags, original.flags);
    assert_eq!(actual.implicit_defs, original.implicit_defs);
    assert_eq!(actual.implicit_uses, original.implicit_uses);
    assert_eq!(actual.proof, original.proof);
    assert_eq!(actual.source_loc, original.source_loc);
}

fn retired(func: &MachFunction, id: InstId) {
    let inst = func.inst(id);
    assert_eq!(inst.opcode, AArch64Opcode::Nop);
    assert_eq!(inst.flags, InstFlags::IS_PSEUDO);
    assert!(inst.operands.is_empty());
    assert!(inst.implicit_defs.is_empty());
    assert!(inst.implicit_uses.is_empty());
    assert!(inst.proof.is_none());
    assert!(inst.source_loc.is_none());
}

fn history(index: u32) -> LoweringProvenance {
    LoweringProvenance::SourceInst {
        id: SourceInstId { block: 0, index },
        digest: SourceInstDigest::compute("Load", 1, 1),
        trust_ir_inst: Some(TrustIrInstId(index + 100)),
    }
}

fn annotate(func: &mut MachFunction, ids: &[InstId]) -> ProvenanceMap {
    let mut provenance = ProvenanceMap::new();
    for (index, &id) in ids.iter().enumerate() {
        func.set_inst_lowering_provenance(id, history(index as u32));
        func.inst_mut(id).source_loc = Some(SourceLoc {
            file: 7,
            line: index as u32 + 20,
            col: 2,
        });
        provenance.record_lowering(
            TrustIrInstId(index as u32 + 100),
            &[id],
            PassId::new("original-isel"),
        );
    }
    provenance
}

#[test]
fn adjacent_pairs_retire_exact_ids_all_existing_banks_and_preserve_source_history() {
    for class in [
        RegClass::Gpr32,
        RegClass::Gpr64,
        RegClass::Fpr32,
        RegClass::Fpr64,
        RegClass::Fpr128,
    ] {
        for opcode in [AArch64Opcode::LdrRI, AArch64Opcode::StrRI] {
            let width = access_size(class).unwrap();
            let (mut func, ids) = function(vec![
                access(opcode, 1, class, width),
                access(opcode, 2, class, 0),
            ]);
            let mut provenance = annotate(&mut func, &ids);
            let source_location = func.inst(ids[0]).source_loc;
            let orphan = func.push_inst(gap());
            let orphan_before = func.inst(orphan).clone();
            let arena_before = func.insts.len();
            assert!(MemPairFormation.run_with_provenance(&mut func, &mut provenance));
            assert_eq!(func.insts.len(), arena_before + 1);
            let pair_id = func.block(func.entry).insts[0];
            assert_eq!(func.block(func.entry).insts, [pair_id]);
            let pair = func.inst(pair_id);
            assert_eq!(pair.opcode, pair_opcode(opcode).unwrap());
            assert_eq!(
                pair.operands,
                [
                    vr(2, class),
                    vr(1, class),
                    vr(10, RegClass::Gpr64),
                    MachOperand::Imm(0),
                ]
            );
            assert_eq!(pair.source_loc, source_location);
            assert_eq!(pair.flags, pair.opcode.default_flags());
            assert!(pair.proof.is_none());
            for (index, &id) in ids.iter().enumerate() {
                retired(&func, id);
                assert_eq!(func.inst_lowering_provenance(id), history(index as u32));
                assert_eq!(
                    provenance.get_mach_insts(TrustIrInstId(index as u32 + 100)),
                    Some([pair_id].as_slice())
                );
            }
            let entry = provenance.get_entry(pair_id).unwrap();
            assert_eq!(
                entry.trust_ir_origins,
                [TrustIrInstId(100), TrustIrInstId(101)]
            );
            assert!(entry.is_active());
            same(func.inst(orphan), &orphan_before);
            let before = func.insts.clone();
            assert!(!MemPairFormation.run_with_provenance(&mut func, &mut provenance));
            for (actual, expected) in func.insts.iter().zip(&before) {
                same(actual, expected);
            }
        }
    }
}

#[test]
fn windowed_loads_and_sunk_stores_retire_both_sources_without_changing_the_gap() {
    for opcode in [AArch64Opcode::LdrRI, AArch64Opcode::StrRI] {
        let (mut func, ids) = function(vec![
            access(opcode, 1, RegClass::Fpr64, 0),
            gap(),
            access(opcode, 2, RegClass::Fpr64, 8),
        ]);
        let original_gap = func.inst(ids[1]).clone();
        let mut provenance = annotate(&mut func, &ids);
        let mut plain = func.clone();
        assert!(MemPairFormation.run(&mut plain));
        assert!(MemPairFormation.run_with_provenance(&mut func, &mut provenance));
        assert_eq!(func.block(func.entry).insts, plain.block(plain.entry).insts);
        for (actual, expected) in func.insts.iter().zip(&plain.insts) {
            same(actual, expected);
        }
        retired(&func, ids[0]);
        retired(&func, ids[2]);
        // annotate only adds the retained source location to this live gap.
        let mut expected_gap = original_gap;
        expected_gap.source_loc = func.inst(ids[1]).source_loc;
        same(func.inst(ids[1]), &expected_gap);
        let linked = &func.block(func.entry).insts;
        let pair_id = linked[usize::from(opcode == AArch64Opcode::StrRI)];
        assert_eq!(linked.len(), 2);
        assert_eq!(func.inst(pair_id).opcode, pair_opcode(opcode).unwrap());
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(100)),
            Some([pair_id].as_slice())
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(102)),
            Some([pair_id].as_slice())
        );
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(101)),
            Some([ids[1]].as_slice())
        );
    }
}

fn damage(inst: &mut MachInst, mutation: usize, next_vreg: u32) {
    match mutation {
        0 => inst.flags = InstFlags::EMPTY,
        1 => inst.flags |= InstFlags::IS_PSEUDO,
        2 => inst.flags |= InstFlags::IS_CALL_ARG_SETUP,
        3 => inst.implicit_defs = &[NZCV],
        4 => inst.implicit_uses = &[NZCV],
        5 => inst.implicit_defs = &[X0],
        6 => inst.implicit_uses = &[X0],
        7 => inst.proof = Some(ProofAnnotation::InBounds),
        8 => inst.operands.push(MachOperand::Imm(99)),
        9 => inst.operands[0] = MachOperand::Imm(0),
        10 => inst.operands[0] = vr(next_vreg, RegClass::Gpr64),
        11 => inst.operands[1] = vr(next_vreg, RegClass::Gpr64),
        12 => inst.operands[1] = vr(10, RegClass::Gpr32),
        13 => inst.operands[0] = vr(1, RegClass::Fpr16),
        14 => inst.operands[1] = vr(10, RegClass::System),
        _ => unreachable!(),
    }
}

#[test]
fn protected_or_malformed_accesses_are_unchanged_in_both_modes_on_either_side() {
    for opcode in [AArch64Opcode::LdrRI, AArch64Opcode::StrRI] {
        for side in 0..2 {
            for mutation in 0..15 {
                let (mut func, ids) = function(vec![
                    access(opcode, 1, RegClass::Gpr64, 0),
                    access(opcode, 2, RegClass::Gpr64, 8),
                ]);
                let mut provenance = annotate(&mut func, &ids);
                let next_vreg = func.next_vreg;
                damage(func.inst_mut(ids[side]), mutation, next_vreg);
                let original = func.clone();
                let mut plain = func.clone();
                assert!(
                    !MemPairFormation.run(&mut plain),
                    "{opcode:?}/{side}/{mutation}"
                );
                assert!(!MemPairFormation.run_with_provenance(&mut func, &mut provenance));
                assert_eq!(func.block(func.entry).insts, ids);
                assert_eq!(plain.block(plain.entry).insts, ids);
                assert_eq!(func.insts.len(), original.insts.len());
                for ((actual, ordinary), expected) in
                    func.insts.iter().zip(&plain.insts).zip(&original.insts)
                {
                    same(actual, expected);
                    same(ordinary, expected);
                }
                for (index, id) in ids.iter().enumerate() {
                    assert_eq!(
                        provenance.get_mach_insts(TrustIrInstId(index as u32 + 100)),
                        Some([*id].as_slice())
                    );
                }
            }
        }
    }
}

#[test]
fn original_unencodable_scalar_offsets_cannot_be_hidden_by_an_encodable_pair() {
    let (mut func, ids) = function(vec![
        access(AArch64Opcode::LdrRI, 1, RegClass::Gpr64, -512),
        access(AArch64Opcode::LdrRI, 2, RegClass::Gpr64, -504),
    ]);
    let before = func.insts.clone();
    assert!(!MemPairFormation.run(&mut func));
    assert_eq!(func.block(func.entry).insts, ids);
    for (actual, original) in func.insts.iter().zip(&before) {
        same(actual, original);
    }
}

#[test]
fn opaque_gap_effects_or_proofs_never_license_load_hoisting_or_store_sinking() {
    for opcode in [AArch64Opcode::LdrRI, AArch64Opcode::StrRI] {
        for mutation in 0..5 {
            let (mut func, ids) = function(vec![
                access(opcode, 1, RegClass::Fpr64, 0),
                gap(),
                access(opcode, 2, RegClass::Fpr64, 8),
            ]);
            let gap = func.inst_mut(ids[1]);
            match mutation {
                0 => gap.flags |= InstFlags::HAS_SIDE_EFFECTS,
                1 => gap.flags |= InstFlags::READS_MEMORY,
                2 => gap.implicit_defs = &[NZCV],
                3 => gap.implicit_uses = &[X0],
                4 => gap.proof = Some(ProofAnnotation::ValidBorrow),
                _ => unreachable!(),
            }
            let before = func.insts.clone();
            assert!(!MemPairFormation.run(&mut func), "{opcode:?}/{mutation}");
            assert_eq!(func.block(func.entry).insts, ids);
            for (actual, original) in func.insts.iter().zip(&before) {
                same(actual, original);
            }
        }
    }
}

#[test]
fn protected_base_definitions_and_accesses_are_not_rewritten_by_fold_back() {
    for side in [0, 2] {
        let (mut func, ids) = function(vec![
            MachInst::new(
                AArch64Opcode::AddRI,
                vec![
                    vr(11, RegClass::Gpr64),
                    vr(10, RegClass::Gpr64),
                    MachOperand::Imm(8),
                ],
            ),
            access(AArch64Opcode::LdrRI, 1, RegClass::Fpr64, 0),
            MachInst::new(
                AArch64Opcode::LdrRI,
                vec![
                    vr(2, RegClass::Fpr64),
                    vr(11, RegClass::Gpr64),
                    MachOperand::Imm(0),
                ],
            ),
        ]);
        func.inst_mut(ids[side]).proof = Some(ProofAnnotation::NotNull);
        let before = func.insts.clone();
        assert!(!MemPairFormation.run(&mut func));
        for (actual, original) in func.insts.iter().zip(&before) {
            same(actual, original);
        }
    }
}

#[test]
fn remaining_reference_outside_layout_keeps_original_instruction_and_active_history() {
    let (mut func, ids) = function(vec![
        access(AArch64Opcode::LdrRI, 1, RegClass::Gpr64, 0),
        access(AArch64Opcode::LdrRI, 2, RegClass::Gpr64, 8),
    ]);
    let mut provenance = annotate(&mut func, &ids);
    let other = func.create_block();
    func.append_inst(other, ids[0]);
    func.block_order.retain(|id| *id != other);
    let original = func.clone();
    let mut plain = func.clone();
    assert!(!MemPairFormation.run(&mut plain));
    assert!(!MemPairFormation.run_with_provenance(&mut func, &mut provenance));
    assert_eq!(func.block(func.entry).insts, ids);
    assert_eq!(func.block(other).insts, [ids[0]]);
    for (index, &id) in ids.iter().enumerate() {
        same(func.inst(id), original.inst(id));
        same(plain.inst(id), original.inst(id));
        assert_eq!(func.inst_lowering_provenance(id), history(index as u32));
        assert!(provenance.get_entry(id).unwrap().is_active());
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(index as u32 + 100)),
            Some([id].as_slice())
        );
    }
}

#[test]
fn shared_source_in_two_actual_pair_sites_preserves_both_blocks_and_all_origins() {
    for opcode in [AArch64Opcode::LdrRI, AArch64Opcode::StrRI] {
        let (mut func, mut ids) = function(vec![
            access(opcode, 1, RegClass::Gpr64, 0),
            access(opcode, 2, RegClass::Gpr64, 8),
        ]);
        let other = func.create_block();
        let third = func.push_inst(access(opcode, 3, RegClass::Gpr64, 8));
        func.append_inst(other, ids[0]);
        func.append_inst(other, third);
        ids.push(third);
        let mut provenance = annotate(&mut func, &ids);
        let original = func.clone();
        let mut plain = func.clone();
        assert!(!MemPairFormation.run(&mut plain));
        assert!(!MemPairFormation.run_with_provenance(&mut func, &mut provenance));
        assert_eq!(func.insts.len(), original.insts.len());
        for (actual, expected) in func.blocks.iter().zip(&original.blocks) {
            assert_eq!(actual.insts, expected.insts);
        }
        for (actual, expected) in plain.blocks.iter().zip(&original.blocks) {
            assert_eq!(actual.insts, expected.insts);
        }
        for (index, &id) in ids.iter().enumerate() {
            same(func.inst(id), original.inst(id));
            same(plain.inst(id), original.inst(id));
            let entry = provenance.get_entry(id).unwrap();
            assert!(entry.is_active());
            assert_eq!(entry.trust_ir_origins, [TrustIrInstId(index as u32 + 100)]);
            assert_eq!(
                provenance.get_mach_insts(TrustIrInstId(index as u32 + 100)),
                Some([id].as_slice())
            );
        }
    }
}

#[test]
fn shared_memory_access_or_base_definition_never_changes_during_fold_back() {
    for shared_side in [0, 2] {
        let (mut func, ids) = function(vec![
            MachInst::new(
                AArch64Opcode::AddRI,
                vec![
                    vr(11, RegClass::Gpr64),
                    vr(10, RegClass::Gpr64),
                    MachOperand::Imm(8),
                ],
            ),
            access(AArch64Opcode::LdrRI, 1, RegClass::Fpr64, 0),
            MachInst::new(
                AArch64Opcode::LdrRI,
                vec![
                    vr(2, RegClass::Fpr64),
                    vr(11, RegClass::Gpr64),
                    MachOperand::Imm(0),
                ],
            ),
        ]);
        let other = func.create_block();
        func.append_inst(other, ids[shared_side]);
        func.block_order.retain(|id| *id != other);
        let mut provenance = annotate(&mut func, &ids);
        let original = func.clone();
        let mut plain = func.clone();
        assert!(!MemPairFormation.run(&mut plain));
        assert!(!MemPairFormation.run_with_provenance(&mut func, &mut provenance));
        assert_eq!(func.insts.len(), original.insts.len());
        for &id in &ids {
            same(func.inst(id), original.inst(id));
            same(plain.inst(id), original.inst(id));
        }
        assert_eq!(
            func.block(func.entry).insts,
            original.block(original.entry).insts
        );
        assert_eq!(func.block(other).insts, [ids[shared_side]]);
    }
}

#[test]
fn repeated_pair_creation_retires_all_actual_consumed_ids_once() {
    let (mut func, ids) = function(
        (0..4)
            .map(|i| access(AArch64Opcode::StrRI, i, RegClass::Gpr32, i64::from(i * 4)))
            .collect(),
    );
    assert!(MemPairFormation.run(&mut func));
    assert_eq!(func.insts.len(), 6);
    assert_eq!(func.block(func.entry).insts, [InstId(4), InstId(5)]);
    for id in ids {
        retired(&func, id);
    }
    assert!(!MemPairFormation.run(&mut func));
    assert_eq!(func.insts.len(), 6);
}

#[test]
fn ownership_storage_is_sparse_but_counts_candidate_references_in_every_block() {
    let base = MachInst::new(
        AArch64Opcode::AddRI,
        vec![
            vr(11, RegClass::Gpr64),
            vr(10, RegClass::Gpr64),
            MachOperand::Imm(8),
        ],
    );
    let (mut func, ids) = function(vec![
        access(AArch64Opcode::LdrRI, 1, RegClass::Gpr64, 0),
        access(AArch64Opcode::StrRI, 2, RegClass::Gpr64, 8),
        base.clone(),
    ]);
    // A large ordinary block must not allocate ownership entries for inert
    // instructions or unrelated computation, even though their links count
    // toward the all-block traversal.
    for _ in 0..512 {
        for inst in [MachInst::new(AArch64Opcode::Nop, vec![]), gap()] {
            let id = func.push_inst(inst);
            func.append_inst(func.entry, id);
        }
    }
    for mutation in 0..5 {
        let mut ineligible = base.clone();
        match mutation {
            0 => ineligible.proof = Some(ProofAnnotation::NotNull),
            1 => ineligible.operands[2] = MachOperand::Imm(4096),
            2 => ineligible.operands[0] = vr(11, RegClass::Gpr32),
            3 => ineligible.operands[0] = ineligible.operands[1].clone(),
            4 => ineligible.implicit_uses = &[NZCV],
            _ => unreachable!(),
        }
        assert!(ordinary_addri_base(&ineligible, func.next_vreg).is_none());
        let id = func.push_inst(ineligible);
        func.append_inst(func.entry, id);
    }
    assert_eq!(
        ordinary_addri_base(&base, func.next_vreg),
        Some((
            VReg::new(11, RegClass::Gpr64),
            VReg::new(10, RegClass::Gpr64),
            8,
        ))
    );
    let hidden = func.create_block();
    for id in [ids[0], ids[0], ids[2], ids[2]] {
        func.append_inst(hidden, id);
    }
    let hidden_only = func.push_inst(access(AArch64Opcode::LdrRI, 3, RegClass::Gpr64, 16));
    func.append_inst(hidden, hidden_only);
    func.block_order.retain(|id| *id != hidden);

    let ownership = candidate_ownership(&func);
    assert_eq!(ownership.len(), 3);
    assert_eq!(ownership.get(&ids[0]), Some(&2));
    assert_eq!(ownership.get(&ids[1]), Some(&1));
    assert_eq!(ownership.get(&ids[2]), Some(&2));
    assert!(!ownership.contains_key(&hidden_only));
    for &id in &func.block(func.entry).insts[3..] {
        assert!(!ownership.contains_key(&id), "noncandidate {id:?}");
    }
}

fn assert_pairing_refusal_preserves(mut func: MachFunction, ids: &[InstId]) {
    let mut provenance = annotate(&mut func, ids);
    let original_provenance = provenance.clone();
    let original = func.clone();
    let mut plain = func.clone();
    assert!(!MemPairFormation.run(&mut plain));
    assert!(!MemPairFormation.run_with_provenance(&mut func, &mut provenance));
    assert_eq!(func.insts.len(), original.insts.len());
    assert_eq!(plain.insts.len(), original.insts.len());
    assert_eq!(
        func.block(func.entry).insts,
        original.block(original.entry).insts
    );
    assert_eq!(
        plain.block(plain.entry).insts,
        original.block(original.entry).insts
    );
    for actual in [&func, &plain] {
        assert_eq!(actual.block_order, original.block_order);
        assert_eq!(actual.blocks.len(), original.blocks.len());
        for (actual, expected) in actual.blocks.iter().zip(&original.blocks) {
            assert_eq!(actual.insts, expected.insts);
            assert_eq!(actual.preds, expected.preds);
            assert_eq!(actual.succs, expected.succs);
            assert_eq!(actual.loop_depth, expected.loop_depth);
        }
        assert_eq!(actual.next_vreg, original.next_vreg);
        assert_eq!(actual.lowering_provenance, original.lowering_provenance);
        assert_eq!(actual.source_fusion_targets, original.source_fusion_targets);
        assert_eq!(actual.call_abi_facts, original.call_abi_facts);
        for (actual, expected) in actual.insts.iter().zip(&original.insts) {
            same(actual, expected);
        }
    }
    for (index, &id) in ids.iter().enumerate() {
        same(func.inst(id), original.inst(id));
        same(plain.inst(id), original.inst(id));
        assert_eq!(func.inst_lowering_provenance(id), history(index as u32));
        assert!(provenance.get_entry(id).unwrap().is_active());
        let actual = provenance.get_entry(id).unwrap();
        let expected = original_provenance.get_entry(id).unwrap();
        assert_eq!(actual.trust_ir_origins, expected.trust_ir_origins);
        assert_eq!(actual.transforms, expected.transforms);
        assert_eq!(actual.status, expected.status);
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(index as u32 + 100)),
            Some([id].as_slice())
        );
    }
}

fn width_alias_gap(destination: u32, left: u32, right: u32, class: RegClass) -> MachInst {
    MachInst::new(
        AArch64Opcode::AddRR,
        vec![vr(destination, class), vr(left, class), vr(right, class)],
    )
}

fn assert_pairing_positive_preserves_gap(mut func: MachFunction, ids: &[InstId]) {
    let first = ids[0];
    let last = *ids.last().unwrap();
    let opcode = func.inst(first).opcode;
    let mut provenance = annotate(&mut func, ids);
    let before = func.clone();
    let mut plain = func.clone();
    assert!(
        MemPairFormation.run(&mut plain),
        "mandatory ordinary positive"
    );
    assert!(
        MemPairFormation.run_with_provenance(&mut func, &mut provenance),
        "mandatory provenance positive"
    );
    assert_eq!(func.insts.len(), before.insts.len() + 1);
    assert_eq!(func.insts.len(), plain.insts.len());
    assert_eq!(func.block(func.entry).insts, plain.block(plain.entry).insts);
    for (actual, expected) in func.insts.iter().zip(&plain.insts) {
        same(actual, expected);
    }
    let pair_pos = if opcode == AArch64Opcode::StrRI {
        ids.len() - 2
    } else {
        0
    };
    let paired = func.block(func.entry).insts[pair_pos];
    assert_eq!(func.inst(paired).opcode, pair_opcode(opcode).unwrap());
    assert_eq!(func.block(func.entry).insts.len(), ids.len() - 1);
    let expected_pair =
        try_form_pair(before.inst(first), before.inst(last), before.next_vreg).unwrap();
    same(func.inst(paired), &expected_pair);
    let mut expected_links = ids[1..ids.len() - 1].to_vec();
    expected_links.insert(pair_pos, paired);
    assert_eq!(func.block(func.entry).insts, expected_links);
    let pair_origins = provenance.get_entry(paired).unwrap();
    assert!(pair_origins.is_active());
    assert_eq!(
        pair_origins.trust_ir_origins,
        [TrustIrInstId(100), TrustIrInstId(ids.len() as u32 + 99)]
    );
    retired(&func, first);
    retired(&func, last);
    for (index, &id) in ids.iter().enumerate().take(ids.len() - 1).skip(1) {
        same(func.inst(id), before.inst(id));
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(index as u32 + 100)),
            Some([id].as_slice())
        );
    }
    for index in [0, ids.len() - 1] {
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(index as u32 + 100)),
            Some([paired].as_slice())
        );
        assert_eq!(
            func.inst_lowering_provenance(ids[index]),
            history(index as u32)
        );
    }
    assert_eq!(func.lowering_provenance, before.lowering_provenance);
    assert_eq!(func.source_fusion_targets, before.source_fusion_targets);
    assert_eq!(func.call_abi_facts, before.call_abi_facts);
    assert_eq!(func.next_vreg, before.next_vreg);
}

#[test]
fn windowed_load_pairing_preserves_moved_destination_width_alias_uses_and_defs() {
    for class in [RegClass::Gpr32, RegClass::Gpr64] {
        let alias_class = if class == RegClass::Gpr32 {
            RegClass::Gpr64
        } else {
            RegClass::Gpr32
        };
        let size = access_size(class).unwrap();
        let (adjacent, ids) = function(vec![
            access(AArch64Opcode::LdrRI, 1, class, 0),
            access(AArch64Opcode::LdrRI, 2, class, size),
        ]);
        assert_pairing_positive_preserves_gap(adjacent, &ids);
        let (unrelated, ids) = function(vec![
            access(AArch64Opcode::LdrRI, 1, class, 0),
            width_alias_gap(8, 6, 7, alias_class),
            access(AArch64Opcode::LdrRI, 2, class, size),
        ]);
        assert_pairing_positive_preserves_gap(unrelated, &ids);

        for defines_alias in [false, true] {
            let gap = if defines_alias {
                width_alias_gap(2, 3, 4, alias_class)
            } else {
                width_alias_gap(3, 2, 4, alias_class)
            };
            let (func, ids) = function(vec![
                access(AArch64Opcode::LdrRI, 1, class, 0),
                gap,
                access(AArch64Opcode::LdrRI, 2, class, size),
            ]);
            assert!(try_form_pair(func.inst(ids[0]), func.inst(ids[2]), func.next_vreg).is_some());
            assert_ne!(VReg::new(2, class), VReg::new(2, alias_class));
            // Moving the later load above this gap either changes an earlier
            // aliased read or lets the gap overwrite the newly loaded value.
            assert_pairing_refusal_preserves(func, &ids);
        }
    }
}

#[test]
fn windowed_store_pairing_preserves_sunk_data_and_base_width_alias_defs() {
    crate::env_lock::with_env_overrides_removed(&["TCG_NO_MEM_PAIR_XSTORE"], || {
        // The existing production getter still reads the OS environment. This
        // mandatory positive makes any process-wide disable a visible refusal,
        // rather than allowing it to satisfy the no-change controls vacuously.
        assert!(
            xstore_sink_enabled(),
            "GPR store-sink positives must actually run"
        );
        for class in [RegClass::Gpr32, RegClass::Gpr64] {
            let alias_class = if class == RegClass::Gpr32 {
                RegClass::Gpr64
            } else {
                RegClass::Gpr32
            };
            let size = access_size(class).unwrap();
            let (adjacent, ids) = function(vec![
                access(AArch64Opcode::StrRI, 1, class, 0),
                access(AArch64Opcode::StrRI, 2, class, size),
            ]);
            assert_pairing_positive_preserves_gap(adjacent, &ids);
            let (unrelated, ids) = function(vec![
                access(AArch64Opcode::StrRI, 1, class, 0),
                width_alias_gap(8, 6, 7, alias_class),
                access(AArch64Opcode::StrRI, 2, class, size),
            ]);
            assert_pairing_positive_preserves_gap(unrelated, &ids);

            for base_alias in [false, true] {
                let (destination, gap_class) = if base_alias {
                    (10, RegClass::Gpr32)
                } else {
                    (1, alias_class)
                };
                let (func, ids) = function(vec![
                    access(AArch64Opcode::StrRI, 1, class, 0),
                    width_alias_gap(destination, 8, 9, gap_class),
                    access(AArch64Opcode::StrRI, 2, class, size),
                ]);
                assert!(
                    try_form_pair(func.inst(ids[0]), func.inst(ids[2]), func.next_vreg).is_some()
                );
                // Delaying the first store past a different-width write to its
                // data/base ID changes the value/address of that memory write.
                assert_pairing_refusal_preserves(func, &ids);
            }
        }
    });
}

#[test]
fn word_load_destination_base_numeric_overlap_preserves_both_original_accesses() {
    for overlap in 0..2 {
        for reverse_offsets in [false, true] {
            for windowed in [false, true] {
                let offsets = if reverse_offsets { [4, 0] } else { [0, 4] };
                let loads = [0, 1].map(|index| {
                    access(
                        AArch64Opcode::LdrRI,
                        if index == overlap { 10 } else { index + 1 },
                        RegClass::Gpr32,
                        offsets[index as usize],
                    )
                });
                assert!(try_form_pair(&loads[0], &loads[1], 11).is_none());
                let mut instructions = vec![loads[0].clone()];
                if windowed {
                    instructions.push(gap());
                }
                instructions.push(loads[1].clone());
                let (func, ids) = function(instructions);
                assert_pairing_refusal_preserves(func, &ids);
            }
        }
    }
}

#[test]
fn windowed_word_loads_cannot_cross_a_word_view_write_to_the_x_base() {
    for destination in [10, 8] {
        let (mut func, ids) = function(vec![
            access(AArch64Opcode::LdrRI, 1, RegClass::Gpr32, 0),
            MachInst::new(
                AArch64Opcode::MovR,
                vec![vr(destination, RegClass::Gpr32), vr(9, RegClass::Gpr32)],
            ),
            access(AArch64Opcode::LdrRI, 2, RegClass::Gpr32, 4),
        ]);
        // The loads themselves are pairable: only the gap's numeric base
        // clobber must distinguish refusal from the nearby positive control.
        assert!(try_form_pair(func.inst(ids[0]), func.inst(ids[2]), func.next_vreg).is_some());
        if destination == 10 {
            assert_pairing_refusal_preserves(func, &ids);
        } else {
            let original_gap = func.inst(ids[1]).clone();
            assert!(MemPairFormation.run(&mut func));
            assert_eq!(func.block(func.entry).insts.len(), 2);
            assert_eq!(
                func.inst(func.block(func.entry).insts[0]).opcode,
                AArch64Opcode::LdpRI
            );
            same(func.inst(ids[1]), &original_gap);
            retired(&func, ids[0]);
            retired(&func, ids[2]);
        }
    }
}

#[test]
fn pairing_requires_positive_unique_ownership_not_just_absence_of_sharing() {
    let (func, ids) = function(vec![
        access(AArch64Opcode::LdrRI, 1, RegClass::Gpr64, 0),
        access(AArch64Opcode::LdrRI, 2, RegClass::Gpr64, 8),
    ]);
    let ownership = candidate_ownership(&func);
    assert!(pair_at(&func, ids[0], ids[1], &ownership).is_some());
    for source in ids {
        for count in [None, Some(0), Some(2)] {
            let mut invalid = ownership.clone();
            invalid.remove(&source);
            if let Some(count) = count {
                invalid.insert(source, count);
            }
            let linked = &func.block(func.entry).insts;
            assert!(pair_at(&func, linked[0], linked[1], &invalid).is_none());
        }
    }
}

#[test]
fn store_sink_keeps_exact_original_window_and_memory_hazards() {
    with_xstore_enabled(|| {
        for class in [RegClass::Gpr32, RegClass::Gpr64] {
            let size = access_size(class).unwrap();
            for reverse in [false, true] {
                for distance in [1, STORE_SINK_WINDOW, STORE_SINK_WINDOW + 1] {
                    let mut body = vec![access(
                        AArch64Opcode::StrRI,
                        1,
                        class,
                        if reverse { size } else { 0 },
                    )];
                    body.extend((1..distance).map(|_| gap()));
                    body.push(access(
                        AArch64Opcode::StrRI,
                        2,
                        class,
                        if reverse { 0 } else { size },
                    ));
                    let (func, ids) = function(body);
                    if distance <= STORE_SINK_WINDOW {
                        assert_pairing_positive_preserves_gap(func, &ids);
                    } else {
                        assert_pairing_refusal_preserves(func, &ids);
                    }
                }
            }
            // Reads cannot be crossed, even though the endpoints pair.
            let (func, ids) = function(vec![
                access(AArch64Opcode::StrRI, 1, class, 0),
                access(AArch64Opcode::LdrRI, 3, class, 0),
                access(AArch64Opcode::StrRI, 2, class, size),
            ]);
            assert!(try_form_pair(func.inst(ids[0]), func.inst(ids[2]), func.next_vreg).is_some());
            assert_pairing_refusal_preserves(func, &ids);

            // Compatible stores in different blocks cannot share a window.
            let (mut func, ids) = function(vec![
                access(AArch64Opcode::StrRI, 1, class, 0),
                access(AArch64Opcode::StrRI, 2, class, size),
            ]);
            let other = func.create_block();
            func.block_mut(func.entry).insts.pop();
            func.append_inst(other, ids[1]);
            assert_pairing_refusal_preserves(func, &ids);
        }
    });
}

#[test]
fn noncanonical_or_shared_store_candidates_preserve_actual_custody() {
    let (ordinary, ids) = function(vec![
        access(AArch64Opcode::StrRI, 1, RegClass::Gpr64, 0),
        access(AArch64Opcode::StrRI, 2, RegClass::Gpr64, 8),
    ]);
    assert_pairing_positive_preserves_gap(ordinary, &ids);
    for side in 0..2 {
        for mutation in 0..15 {
            let (mut func, ids) = function(vec![
                access(AArch64Opcode::StrRI, 1, RegClass::Gpr64, 0),
                access(AArch64Opcode::StrRI, 2, RegClass::Gpr64, 8),
            ]);
            let next = func.next_vreg;
            damage(func.inst_mut(ids[side]), mutation, next);
            assert_pairing_refusal_preserves(func, &ids);
        }
        let (mut func, ids) = function(vec![
            access(AArch64Opcode::StrRI, 1, RegClass::Gpr64, 0),
            access(AArch64Opcode::StrRI, 2, RegClass::Gpr64, 8),
        ]);
        let hidden = func.create_block();
        func.append_inst(hidden, ids[side]);
        func.block_order.retain(|id| *id != hidden);
        assert_pairing_refusal_preserves(func, &ids);
    }
}

fn with_xstore_enabled(f: impl FnOnce()) {
    crate::env_lock::with_env_overrides_removed(&["TCG_NO_MEM_PAIR_XSTORE"], || {
        // Production reads the process environment. Positives must visibly
        // refuse a disabled policy, not silently make the negatives pass.
        assert!(xstore_sink_enabled(), "mandatory GPR sink controls are ON");
        f();
    });
}

fn symbol_roots(class: RegClass) -> Vec<MachInst> {
    let symbol = |name: &str| MachOperand::Symbol(name.into());
    vec![
        MachInst::new(
            AArch64Opcode::Movz,
            vec![vr(1, class), MachOperand::Imm(0x11)],
        ),
        MachInst::new(
            AArch64Opcode::Movz,
            vec![vr(2, class), MachOperand::Imm(0x22)],
        ),
        MachInst::new(
            AArch64Opcode::Movz,
            vec![vr(3, class), MachOperand::Imm(0x33)],
        ),
        MachInst::new(
            AArch64Opcode::Adrp,
            vec![vr(11, RegClass::Gpr64), symbol("a")],
        ),
        MachInst::new(
            AArch64Opcode::AddPCRel,
            vec![
                vr(10, RegClass::Gpr64),
                vr(11, RegClass::Gpr64),
                symbol("a"),
            ],
        ),
        MachInst::new(
            AArch64Opcode::Adrp,
            vec![vr(13, RegClass::Gpr64), symbol("b")],
        ),
        MachInst::new(
            AArch64Opcode::AddPCRel,
            vec![
                vr(12, RegClass::Gpr64),
                vr(13, RegClass::Gpr64),
                symbol("b"),
            ],
        ),
    ]
}

fn store_at(data: u32, class: RegClass, base: u32, offset: i64) -> MachInst {
    let mut inst = access(AArch64Opcode::StrRI, data, class, offset);
    inst.operands[1] = vr(base, RegClass::Gpr64);
    inst
}

fn assert_symbol_sink_refusal(body: Vec<MachInst>, endpoints: [usize; 2]) {
    let (func, ids) = function(body);
    assert!(
        try_form_pair(
            func.inst(ids[endpoints[0]]),
            func.inst(ids[endpoints[1]]),
            func.next_vreg,
        )
        .is_some(),
        "the endpoints themselves remain pairable"
    );
    assert_pairing_refusal_preserves(func, &ids);
}

#[test]
fn unauthenticated_symbol_names_cannot_justify_aliasing_store_sink() {
    with_xstore_enabled(|| {
        for class in [RegClass::Gpr32, RegClass::Gpr64] {
            let size = access_size(class).unwrap();
            let mut body = symbol_roots(class);
            let first = body.len();
            body.extend([
                store_at(1, class, 10, size),
                store_at(3, class, 12, size),
                store_at(2, class, 10, 0),
            ]);
            // A resolver may bind both strings to the SAME live buffer. Then
            // original p+size contains 0x33; the old sink changed it to 0x11.
            // No module-owned distinct-object fact is present in this MachIR.
            assert_symbol_sink_refusal(body, [first, first + 2]);
        }
    });
}

#[test]
fn unauthenticated_additive_symbol_roots_cannot_justify_store_sink() {
    with_xstore_enabled(|| {
        for class in [RegClass::Gpr32, RegClass::Gpr64] {
            let size = access_size(class).unwrap();
            for operation in [
                AArch64Opcode::AddRI,
                AArch64Opcode::AddRR,
                AArch64Opcode::AddRRShift,
            ] {
                let mut body = symbol_roots(class);
                let operands = if operation == AArch64Opcode::AddRI {
                    vec![
                        vr(15, RegClass::Gpr64),
                        vr(10, RegClass::Gpr64),
                        MachOperand::Imm(32),
                    ]
                } else {
                    body.push(MachInst::new(
                        AArch64Opcode::Movz,
                        vec![
                            vr(16, RegClass::Gpr64),
                            MachOperand::Imm(if operation == AArch64Opcode::AddRR {
                                32
                            } else {
                                4
                            }),
                        ],
                    ));
                    let mut operands = vec![
                        vr(15, RegClass::Gpr64),
                        vr(10, RegClass::Gpr64),
                        vr(16, RegClass::Gpr64),
                    ];
                    if operation == AArch64Opcode::AddRRShift {
                        operands.push(MachOperand::Imm(3));
                    }
                    operands
                };
                body.push(MachInst::new(operation, operands));
                let first = body.len();
                body.extend([
                    store_at(1, class, 15, size),
                    store_at(3, class, 12, size),
                    store_at(2, class, 15, 0),
                ]);
                // Distinct root addresses A=p and B=p+32 still overlap after
                // additive addressing: both first and gap write p+32+size.
                // This is a raw-Mach control, not a defined LLVM inbounds GEP.
                assert_symbol_sink_refusal(body, [first, first + 2]);
            }
        }
    });
}

#[test]
fn unauthenticated_ro_indices_cannot_justify_symbol_store_sink() {
    with_xstore_enabled(|| {
        for class in [RegClass::Gpr32, RegClass::Gpr64] {
            let size = access_size(class).unwrap();
            // Exact supported RO carriers: default X/LSL0, W/SXTW0, and
            // W/SXTW with the actual transfer-size shift (mode 13).
            for mode in [None, Some(12), Some(13)] {
                let shifted = mode == Some(13);
                let index = if shifted { -1 } else { size - 32 };
                let root_b = if shifted {
                    0x100 + 2 * size
                } else {
                    0x100 + 32
                };
                let offset = if shifted { index * size } else { index };
                assert_eq!(root_b + offset, 0x100 + size);
                let mut body = symbol_roots(class);
                let index_class = if mode.is_none() {
                    RegClass::Gpr64
                } else {
                    RegClass::Gpr32
                };
                body.push(MachInst::new(
                    AArch64Opcode::Movn,
                    vec![vr(14, index_class), MachOperand::Imm(-index - 1)],
                ));
                let mut gap_operands =
                    vec![vr(3, class), vr(12, RegClass::Gpr64), vr(14, index_class)];
                if let Some(mode) = mode {
                    gap_operands.push(MachOperand::Imm(mode));
                }
                let first = body.len();
                body.extend([
                    store_at(1, class, 10, size),
                    MachInst::new(AArch64Opcode::StrRO, gap_operands),
                    store_at(2, class, 10, 0),
                ]);
                // Legal negative index addressing crosses from distinct B to
                // the first store's address. Symbol inequality says nothing
                // about the RO index, its extension or its shift.
                assert_symbol_sink_refusal(body, [first, first + 2]);
            }
        }
    });
}

#[test]
fn unauthenticated_narrowed_symbol_roots_do_not_gain_store_sink_authority() {
    with_xstore_enabled(|| {
        for class in [RegClass::Gpr32, RegClass::Gpr64] {
            let size = access_size(class).unwrap();
            let mut body = symbol_roots(class);
            body.extend([
                MachInst::new(
                    AArch64Opcode::MovR,
                    vec![vr(15, RegClass::Gpr32), vr(12, RegClass::Gpr32)],
                ),
                MachInst::new(
                    AArch64Opcode::Uxtw,
                    vec![vr(16, RegClass::Gpr64), vr(15, RegClass::Gpr32)],
                ),
            ]);
            let first = body.len();
            body.extend([
                store_at(1, class, 10, size),
                store_at(3, class, 16, size),
                store_at(2, class, 10, 0),
            ]);
            assert_symbol_sink_refusal(body, [first, first + 2]);
        }
    });
}

#[test]
fn safe_store_sink_intervals_retain_both_widths_and_metadata_custody() {
    with_xstore_enabled(|| {
        for class in [RegClass::Gpr32, RegClass::Gpr64] {
            let size = access_size(class).unwrap();
            let body = vec![
                access(AArch64Opcode::StrRI, 1, class, size),
                access(AArch64Opcode::StrRI, 3, class, 3 * size),
                access(AArch64Opcode::StrRI, 2, class, 0),
            ];
            let (positive, ids) = function(body.clone());
            assert_pairing_positive_preserves_gap(positive, &ids);
            for mutation in 0..5 {
                let (mut func, ids) = function(body.clone());
                let gap = func.inst_mut(ids[1]);
                match mutation {
                    0 => gap.flags |= InstFlags::IS_TERMINATOR,
                    1 => gap.flags |= InstFlags::READS_MEMORY,
                    2 => gap.implicit_defs = &[NZCV],
                    3 => gap.implicit_uses = &[X0],
                    4 => gap.proof = Some(ProofAnnotation::ValidBorrow),
                    _ => unreachable!(),
                }
                assert!(
                    !ordinary_metadata(gap),
                    "mutation {mutation} must change admission"
                );
                assert_symbol_sink_refusal(func.insts, [0, 2]);
            }
        }
    });
}

fn original_fixture_v10_definitions(func: &MachFunction) -> (usize, Option<InstId>) {
    let mut count = 0;
    let mut last = None;
    for block in &func.blocks {
        for &id in &block.insts {
            let inst = func.inst(id);
            aarch64_for_each_def_position(inst.opcode, inst.operands.len(), |position| {
                if inst.operands[position]
                    .as_vreg()
                    .is_some_and(|value| value.id == 10)
                {
                    count += 1;
                    last = Some(id);
                }
            });
        }
    }
    (count, last)
}

#[test]
fn store_sink_retains_original_hidden_and_multiple_definitions_without_symbol_authority() {
    with_xstore_enabled(|| {
        let (mut func, ids) = function(vec![
            access(AArch64Opcode::StrRI, 1, RegClass::Gpr64, 0),
            gap(),
            access(AArch64Opcode::StrRI, 2, RegClass::Gpr64, 8),
        ]);
        let hidden = func.create_block();
        let first = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                vr(10, RegClass::Gpr64),
                vr(11, RegClass::Gpr64),
                MachOperand::Imm(8),
            ],
        ));
        let second = func.push_inst(MachInst::new(
            AArch64Opcode::AddRI,
            vec![
                vr(10, RegClass::Gpr64),
                vr(11, RegClass::Gpr64),
                MachOperand::Imm(16),
            ],
        ));
        func.append_inst(hidden, first);
        func.append_inst(hidden, second);
        let other_owner = func.create_block();
        func.append_inst(other_owner, second);
        func.block_order
            .retain(|id| *id != hidden && *id != other_owner);
        assert!(func.try_sync_vreg_counter().is_some());
        assert_eq!(original_fixture_v10_definitions(&func), (3, Some(second)));
        let mut provenance = annotate(&mut func, &ids);
        let before = func.clone();
        let mut plain = func.clone();
        assert!(
            MemPairFormation.run(&mut plain),
            "original ordinary positive"
        );
        assert!(MemPairFormation.run_with_provenance(&mut func, &mut provenance));
        let expected_pair =
            try_form_pair(before.inst(ids[0]), before.inst(ids[2]), before.next_vreg)
                .expect("the original endpoints stay pairable");
        for actual in [&plain, &func] {
            assert_eq!(actual.insts.len(), before.insts.len() + 1);
            assert_eq!(actual.block_order, before.block_order);
            assert_eq!(actual.blocks.len(), before.blocks.len());
            assert_eq!(original_fixture_v10_definitions(actual), (3, Some(second)));
            let paired = actual.block(actual.entry).insts[1];
            assert_eq!(actual.block(actual.entry).insts, [ids[1], paired]);
            same(actual.inst(paired), &expected_pair);
            retired(actual, ids[0]);
            retired(actual, ids[2]);
            for (current, original) in actual.blocks.iter().zip(&before.blocks) {
                assert_eq!(current.preds, original.preds);
                assert_eq!(current.succs, original.succs);
                assert_eq!(current.loop_depth, original.loop_depth);
            }
            for block in [hidden, other_owner] {
                assert_eq!(actual.block(block).insts, before.block(block).insts);
            }
            for (position, original) in before.insts.iter().enumerate() {
                if position != (ids[0].0 as usize) && position != (ids[2].0 as usize) {
                    same(&actual.insts[position], original);
                }
            }
            assert_eq!(actual.next_vreg, before.next_vreg);
            assert_eq!(actual.lowering_provenance, before.lowering_provenance);
            assert_eq!(actual.source_fusion_targets, before.source_fusion_targets);
            assert_eq!(actual.call_abi_facts, before.call_abi_facts);
        }
        let paired = func.block(func.entry).insts[1];
        let pair_origins = provenance.get_entry(paired).unwrap();
        assert!(pair_origins.is_active());
        assert_eq!(
            pair_origins.trust_ir_origins,
            [TrustIrInstId(100), TrustIrInstId(102)]
        );
        for index in [0, 2] {
            assert_eq!(
                provenance.get_mach_insts(TrustIrInstId(index as u32 + 100)),
                Some([paired].as_slice())
            );
            assert_eq!(
                func.inst_lowering_provenance(ids[index]),
                history(index as u32)
            );
        }
        assert_eq!(
            provenance.get_mach_insts(TrustIrInstId(101)),
            Some([ids[1]].as_slice())
        );
    });
}
