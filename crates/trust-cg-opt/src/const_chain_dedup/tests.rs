// trust-cg-opt - const-chain-dedup unit tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use trust_cg_ir::{
    LoweringProvenance, MachInst, MachOperand as MO, Signature, SourceInstDigest, SourceInstId,
    SourceLoc, TrustIrInstId,
};

fn g64(id: u32) -> VReg {
    VReg::new(id, RegClass::Gpr64)
}
fn g32(id: u32) -> VReg {
    VReg::new(id, RegClass::Gpr32)
}
fn push(func: &mut MachFunction, b: BlockId, inst: MachInst) -> InstId {
    let id = func.push_inst(inst);
    func.append_inst(b, id);
    id
}
fn rr(op: AArch64Opcode, d: VReg, a: VReg, b: VReg) -> MachInst {
    MachInst::new(op, vec![MO::VReg(d), MO::VReg(a), MO::VReg(b)])
}

/// `MOVZ` + `MOVK`s materializing `value` into `v` (16-bit chunks, low first,
/// zero chunks above the first skipped), as the selector spells it.
fn chain(func: &mut MachFunction, b: BlockId, v: VReg, value: u64) -> Vec<InstId> {
    let width = if v.class == RegClass::Gpr32 { 32 } else { 64 };
    let mut ids = vec![push(
        func,
        b,
        MachInst::new(
            AArch64Opcode::Movz,
            vec![MO::VReg(v), MO::Imm((value & 0xFFFF) as i64)],
        ),
    )];
    for shift in (16..width).step_by(16) {
        let chunk = (value >> shift) & 0xFFFF;
        if chunk != 0 {
            ids.push(push(
                func,
                b,
                MachInst::new(
                    AArch64Opcode::Movk,
                    vec![MO::VReg(v), MO::Imm(chunk as i64), MO::Imm(shift as i64)],
                ),
            ));
        }
    }
    ids
}

const A: u64 = 0x5851_F42D_4C95_7F2D;
const B: u64 = 0x1405_7B7E_F767_814F;

/// The `p3_gcd` shape after LICM: the preheader holds the two LCG constants
/// twice (`v1`/`v2` = A, `v3`/`v4` = B); the body computes
/// `s = s*A + B` twice, the second time through the duplicates.
///
/// ```text
///   bb0 preheader: chains v1=A v2=B v3=A v4=B ; B header
///   bb1 header:    CmpRR i, n ; BCond LO body ; B exit
///   bb2 body:      t=Madd s,v1,v2 ; s=Madd t,v3,v4 ; i+=1 ; B header
///   bb3 exit:      Ret
/// ```
fn lcg_loop() -> (MachFunction, BlockId, BlockId) {
    let mut f = MachFunction::new("p3".into(), Signature::new(vec![], vec![]));
    let pre = f.entry;
    let header = f.create_block();
    let body = f.create_block();
    let exit = f.create_block();
    let (s, t, i, n) = (g64(10), g64(11), g64(12), g64(13));
    chain(&mut f, pre, g64(1), A);
    chain(&mut f, pre, g64(2), B);
    chain(&mut f, pre, g64(3), A);
    chain(&mut f, pre, g64(4), B);
    push(
        &mut f,
        pre,
        MachInst::new(AArch64Opcode::B, vec![MO::Block(header)]),
    );
    push(
        &mut f,
        header,
        MachInst::new(AArch64Opcode::CmpRR, vec![MO::VReg(i), MO::VReg(n)]),
    );
    push(
        &mut f,
        header,
        MachInst::new(AArch64Opcode::BCond, vec![MO::Imm(3), MO::Block(body)]),
    );
    push(
        &mut f,
        header,
        MachInst::new(AArch64Opcode::B, vec![MO::Block(exit)]),
    );
    push(
        &mut f,
        body,
        MachInst::new(
            AArch64Opcode::Madd,
            vec![MO::VReg(t), MO::VReg(s), MO::VReg(g64(1)), MO::VReg(g64(2))],
        ),
    );
    push(
        &mut f,
        body,
        MachInst::new(
            AArch64Opcode::Madd,
            vec![MO::VReg(s), MO::VReg(t), MO::VReg(g64(3)), MO::VReg(g64(4))],
        ),
    );
    push(
        &mut f,
        body,
        MachInst::new(
            AArch64Opcode::AddRI,
            vec![MO::VReg(i), MO::VReg(i), MO::Imm(1)],
        ),
    );
    push(
        &mut f,
        body,
        MachInst::new(AArch64Opcode::B, vec![MO::Block(header)]),
    );
    push(&mut f, exit, MachInst::new(AArch64Opcode::Ret, vec![]));
    (f, pre, body)
}

fn run(f: &mut MachFunction) -> bool {
    ConstChainDedup.run(f)
}

fn vreg_operands(f: &MachFunction, b: BlockId) -> Vec<Vec<VReg>> {
    f.block(b)
        .insts
        .iter()
        .map(|&id| {
            f.inst(id)
                .operands
                .iter()
                .filter_map(|op| match op {
                    MO::VReg(v) => Some(*v),
                    _ => None,
                })
                .collect()
        })
        .collect()
}

fn same_instruction(actual: &MachInst, expected: &MachInst) {
    assert_eq!(actual.opcode, expected.opcode);
    assert_eq!(actual.operands, expected.operands);
    assert_eq!(actual.flags, expected.flags);
    assert_eq!(actual.implicit_defs, expected.implicit_defs);
    assert_eq!(actual.implicit_uses, expected.implicit_uses);
    assert_eq!(actual.proof, expected.proof);
    assert_eq!(actual.source_loc, expected.source_loc);
}

/// Capture fixture source-lowering history independently of active provenance.
/// This is a custody regression, not a source-to-machine semantic certificate.
fn capture_history(func: &mut MachFunction) -> ProvenanceMap {
    let mut provenance = ProvenanceMap::new();
    for index in 0..func.insts.len() {
        let id = InstId(index as u32);
        let origin = TrustIrInstId(index as u32 + 100);
        func.set_inst_lowering_provenance(
            id,
            LoweringProvenance::SourceInst {
                id: SourceInstId {
                    block: 0,
                    index: index as u32,
                },
                digest: SourceInstDigest::compute("fixture-source", 1, 1),
                trust_ir_inst: Some(origin),
            },
        );
        func.inst_mut(id).source_loc = Some(SourceLoc {
            file: 7,
            line: index as u32 + 20,
            col: 2,
        });
        provenance.record_lowering(origin, &[id], PassId::new("original-isel"));
    }
    provenance
}

fn assert_provenance_unchanged(actual: &ProvenanceMap, expected: &ProvenanceMap, arena_len: usize) {
    for index in 0..arena_len {
        let id = InstId(index as u32);
        let actual_entry = actual.get_entry(id).expect("captured entry");
        let expected_entry = expected.get_entry(id).expect("captured entry");
        assert_eq!(
            actual_entry.trust_ir_origins,
            expected_entry.trust_ir_origins
        );
        assert_eq!(actual_entry.transforms, expected_entry.transforms);
        assert_eq!(actual_entry.status, expected_entry.status);
        let origin = TrustIrInstId(index as u32 + 100);
        assert_eq!(
            actual.get_mach_insts(origin),
            expected.get_mach_insts(origin)
        );
    }
}

fn repeated_constant(class: RegClass) -> (MachFunction, Vec<InstId>, Vec<InstId>, InstId) {
    let mut f = MachFunction::new("retirement".into(), Signature::new(vec![], vec![]));
    let b = f.entry;
    let value = if class == RegClass::Gpr32 {
        A & 0xFFFF_FFFF
    } else {
        A
    };
    let keep = chain(&mut f, b, VReg::new(1, class), value);
    let duplicate = chain(&mut f, b, VReg::new(2, class), value);
    let reader = push(
        &mut f,
        b,
        rr(
            AArch64Opcode::AddRR,
            VReg::new(3, class),
            VReg::new(1, class),
            VReg::new(2, class),
        ),
    );
    push(&mut f, b, MachInst::new(AArch64Opcode::Ret, vec![]));
    f.try_sync_vreg_counter().expect("bounded fixture arena");
    (f, keep, duplicate, reader)
}

#[test]
fn actual_consumed_chains_retire_exact_arena_ids_and_preserve_source_capture() {
    for class in [RegClass::Gpr32, RegClass::Gpr64] {
        for unrelated_orphan in [false, true] {
            let (mut f, keep, duplicate, reader) = repeated_constant(class);
            let orphan = unrelated_orphan.then(|| {
                f.push_inst(
                    rr(AArch64Opcode::AddRR, g64(20), g64(21), g64(22))
                        .with_proof(trust_cg_ir::ProofAnnotation::NoSignedOverflow),
                )
            });
            let mut provenance = capture_history(&mut f);
            let before = f.clone();
            let mut plain = before.clone();
            assert!(ConstChainDedup.run(&mut plain), "ordinary positive");
            assert!(ConstChainDedup.run_with_provenance(&mut f, &mut provenance));
            assert_eq!(format!("{f:?}"), format!("{plain:?}"));
            assert_eq!(f.insts.len(), before.insts.len(), "stable arena IDs");
            assert_eq!(f.next_vreg, before.next_vreg, "no register allocation");
            assert_eq!(f.lowering_provenance, before.lowering_provenance);
            assert_eq!(f.source_fusion_targets, before.source_fusion_targets);
            assert_eq!(f.call_abi_facts, before.call_abi_facts);
            let expected_links: Vec<_> = before
                .block(before.entry)
                .insts
                .iter()
                .copied()
                .filter(|id| !duplicate.contains(id))
                .collect();
            assert_eq!(f.block(f.entry).insts, expected_links);
            let kept_last = *keep.last().unwrap();
            for &id in &duplicate {
                same_instruction(f.inst(id), &MachInst::new(AArch64Opcode::Nop, vec![]));
                assert!(f.blocks.iter().all(|b| !b.insts.contains(&id)));
                assert_eq!(
                    f.inst_lowering_provenance(id),
                    before.inst_lowering_provenance(id)
                );
                assert_eq!(
                    provenance.get_mach_insts(TrustIrInstId(id.0 + 100)),
                    Some([kept_last].as_slice())
                );
                assert!(provenance.get_entry(id).is_none());
            }
            for index in 0..before.insts.len() {
                let id = InstId(index as u32);
                if duplicate.contains(&id) {
                    continue;
                }
                let mut expected = before.inst(id).clone();
                if id == reader {
                    expected.operands[2] = MO::VReg(VReg::new(1, class));
                }
                same_instruction(f.inst(id), &expected);
            }
            if let Some(orphan) = orphan {
                same_instruction(f.inst(orphan), before.inst(orphan));
                assert!(provenance.get_entry(orphan).unwrap().is_active());
            }
            let once = format!("{f:?}");
            let once_provenance = provenance.clone();
            assert!(!ConstChainDedup.run_with_provenance(&mut f, &mut provenance));
            assert_eq!(format!("{f:?}"), once);
            for index in 0..f.insts.len() {
                let id = InstId(index as u32);
                if let Some(expected) = once_provenance.get_entry(id) {
                    let actual = provenance.get_entry(id).unwrap();
                    assert_eq!(actual.trust_ir_origins, expected.trust_ir_origins);
                    assert_eq!(actual.transforms, expected.transforms);
                    assert_eq!(actual.status, expected.status);
                } else {
                    assert!(provenance.get_entry(id).is_none());
                }
                let origin = TrustIrInstId(index as u32 + 100);
                assert_eq!(
                    provenance.get_mach_insts(origin),
                    once_provenance.get_mach_insts(origin)
                );
            }
        }
    }
}

#[test]
fn shared_chain_ownership_refuses_before_retirement_or_source_capture_changes() {
    for class in [RegClass::Gpr32, RegClass::Gpr64] {
        for shared_keep in [false, true] {
            for shape in 0..3 {
                let (mut f, keep, duplicate, _) = repeated_constant(class);
                let shared = if shared_keep { keep[0] } else { duplicate[0] };
                if shape == 0 {
                    f.block_mut(f.entry).insts.insert(0, shared);
                } else {
                    let other = f.create_block();
                    f.append_inst(other, shared);
                    if shape == 2 {
                        f.block_order.retain(|&b| b != other);
                    }
                }
                let mut provenance = capture_history(&mut f);
                let original_provenance = provenance.clone();
                let before = f.clone();
                let mut plain = before.clone();
                assert!(!ConstChainDedup.run(&mut plain));
                assert_eq!(format!("{plain:?}"), format!("{before:?}"));
                assert!(!ConstChainDedup.run_with_provenance(&mut f, &mut provenance));
                assert_eq!(format!("{f:?}"), format!("{before:?}"));
                assert_provenance_unchanged(&provenance, &original_provenance, before.insts.len());
            }
        }
    }
}

#[test]
fn refusal_of_one_constant_never_retires_its_still_owned_chain() {
    for outside_layout in [false, true] {
        let (mut f, pre, _) = lcg_loop();
        let links = f.block(pre).insts.clone();
        let refused = links[8..12].to_vec();
        let consumed = links[12..16].to_vec();
        let other = f.create_block();
        f.append_inst(other, refused[0]);
        if outside_layout {
            f.block_order.retain(|&b| b != other);
        }
        let mut provenance = capture_history(&mut f);
        let original_provenance = provenance.clone();
        let before = f.clone();
        assert!(ConstChainDedup.run_with_provenance(&mut f, &mut provenance));
        for &id in &refused {
            same_instruction(f.inst(id), before.inst(id));
            let actual = provenance.get_entry(id).unwrap();
            let expected = original_provenance.get_entry(id).unwrap();
            assert_eq!(actual.trust_ir_origins, expected.trust_ir_origins);
            assert_eq!(actual.transforms, expected.transforms);
            assert_eq!(actual.status, expected.status);
            let origin = TrustIrInstId(id.0 + 100);
            assert_eq!(provenance.get_mach_insts(origin), Some([id].as_slice()));
        }
        for &id in &consumed {
            same_instruction(f.inst(id), &MachInst::new(AArch64Opcode::Nop, vec![]));
            assert!(f.blocks.iter().all(|b| !b.insts.contains(&id)));
        }
        assert_eq!(f.lowering_provenance, before.lowering_provenance);
        assert_eq!(f.insts.len(), before.insts.len());
    }
}

/// The ARM ARM semantics of the opcodes these straight-line blocks use, on
/// 64-bit register IDs: a W write zero-extends, a W read takes the low half.
fn eval_block(f: &MachFunction, b: BlockId, regs: &mut HashMap<u32, u64>) {
    for &id in &f.block(b).insts {
        let inst = f.inst(id);
        let read = |regs: &HashMap<u32, u64>, i: usize| match inst.operands[i] {
            MO::VReg(v) => {
                let x = regs[&v.id];
                if v.class == RegClass::Gpr32 {
                    x & 0xFFFF_FFFF
                } else {
                    x
                }
            }
            _ => panic!("register operand"),
        };
        let imm = |i: usize| match inst.operands[i] {
            MO::Imm(v) => v as u64,
            _ => panic!("immediate operand"),
        };
        let MO::VReg(d) = inst.operands[0] else {
            continue;
        };
        let value = match inst.opcode {
            AArch64Opcode::Movz => imm(1),
            AArch64Opcode::Movk => {
                let shift = imm(2);
                (regs.get(&d.id).copied().unwrap_or(0) & !(0xFFFF << shift)) | (imm(1) << shift)
            }
            AArch64Opcode::AddRR => read(regs, 1).wrapping_add(read(regs, 2)),
            AArch64Opcode::EorRR => read(regs, 1) ^ read(regs, 2),
            AArch64Opcode::Madd => read(regs, 1)
                .wrapping_mul(read(regs, 2))
                .wrapping_add(read(regs, 3)),
            other => panic!("unexpected opcode {other:?}"),
        };
        let value = if d.class == RegClass::Gpr32 {
            value & 0xFFFF_FFFF
        } else {
            value
        };
        regs.insert(d.id, value);
    }
}

#[test]
fn merges_each_repeated_constant_of_a_preheader() {
    let (mut f, pre, body) = lcg_loop();
    let before = f.block(pre).insts.len();
    assert!(run(&mut f));
    // Two of the four 4-instruction chains are gone.
    assert_eq!(f.block(pre).insts.len(), before - 8);
    let ops = vreg_operands(&f, body);
    assert_eq!(ops[0], vec![g64(11), g64(10), g64(1), g64(2)]);
    assert_eq!(
        ops[1],
        vec![g64(10), g64(11), g64(1), g64(2)],
        "second Madd reads the kept chains"
    );
    // The kept chains still produce A and B.
    let mut regs = HashMap::default();
    eval_block(
        &{
            let mut g = f.clone();
            let last = g.block(pre).insts.len() - 1;
            g.block_mut(pre).insts.truncate(last);
            g
        },
        pre,
        &mut regs,
    );
    assert_eq!((regs[&1], regs[&2]), (A, B));
    assert!(!regs.contains_key(&3) && !regs.contains_key(&4));
    // Idempotent.
    let again = format!("{f:?}");
    assert!(!run(&mut f));
    assert_eq!(format!("{f:?}"), again);
}

#[test]
fn a_straight_line_block_computes_the_same_values() {
    // v1 = A ; v2 = A ; v3 = B ; x = v1 + v2 ; y = v3 ^ v2 (W view) ;
    // z = v1 + v3: every read of a removed duplicate sees the same value.
    let build = || {
        let mut f = MachFunction::new("s".into(), Signature::new(vec![], vec![]));
        let b = f.entry;
        chain(&mut f, b, g64(1), A);
        chain(&mut f, b, g64(2), A);
        chain(&mut f, b, g64(3), B);
        push(&mut f, b, rr(AArch64Opcode::AddRR, g64(4), g64(1), g64(2)));
        push(&mut f, b, rr(AArch64Opcode::EorRR, g32(5), g32(3), g32(2)));
        push(&mut f, b, rr(AArch64Opcode::AddRR, g64(6), g64(1), g64(3)));
        (f, b)
    };
    let (reference, b) = build();
    let mut want = HashMap::default();
    eval_block(&reference, b, &mut want);
    let (mut f, b) = build();
    assert!(run(&mut f));
    assert_eq!(f.block(b).insts.len(), reference.block(b).insts.len() - 4);
    let ops = vreg_operands(&f, b);
    let n = ops.len();
    assert_eq!(ops[n - 3], vec![g64(4), g64(1), g64(1)]);
    assert_eq!(
        ops[n - 2],
        vec![g32(5), g32(3), g32(1)],
        "the W view of the kept chain"
    );
    let mut got = HashMap::default();
    eval_block(&f, b, &mut got);
    for id in [4u32, 5, 6] {
        assert_eq!(got[&id], want[&id], "v{id}");
    }
}

/// Places two chains: `(func, first block, other block)`.
type Build = dyn Fn(&mut MachFunction, BlockId, BlockId);

#[test]
fn keeps_chains_that_differ_or_stand_alone() {
    // Different values; the same low 32 bits in two classes; a single MOVZ
    // twice; the duplicate in another block. None merges.
    let cases: Vec<(&str, Box<Build>)> = vec![
        (
            "different values",
            Box::new(|f, b, _| {
                chain(f, b, g64(1), A);
                chain(f, b, g64(2), A ^ (1 << 40));
            }),
        ),
        (
            "different classes",
            Box::new(|f, b, _| {
                chain(f, b, g64(1), 0x4C95_7F2D);
                chain(f, b, g32(2), 0x4C95_7F2D);
            }),
        ),
        (
            "single MOVZ",
            Box::new(|f, b, _| {
                chain(f, b, g64(1), 0x7F2D);
                chain(f, b, g64(2), 0x7F2D);
            }),
        ),
        (
            "other block",
            Box::new(|f, b, other| {
                chain(f, b, g64(1), A);
                chain(f, other, g64(2), A);
            }),
        ),
    ];
    for (name, build) in cases {
        let mut f = MachFunction::new("k".into(), Signature::new(vec![], vec![]));
        let b = f.entry;
        let other = f.create_block();
        build(&mut f, b, other);
        push(
            &mut f,
            other,
            rr(AArch64Opcode::AddRR, g64(3), g64(1), g64(1)),
        );
        push(
            &mut f,
            other,
            rr(AArch64Opcode::AddRR, g64(4), g64(2), g64(2)),
        );
        let before = format!("{f:?}");
        assert!(!run(&mut f), "{name}");
        assert_eq!(format!("{f:?}"), before, "{name}");
    }
}

#[test]
fn keeps_a_register_written_outside_its_chain() {
    // Either carrier written again (a copy into it in the body, or a W write
    // of its ID) is not a constant: no merge.
    for (victim, class) in [
        (1u32, RegClass::Gpr64),
        (3, RegClass::Gpr64),
        (3, RegClass::Gpr32),
    ] {
        let (mut f, _, body) = lcg_loop();
        let pos = f.block(body).insts.len() - 1;
        let id = f.push_inst(MachInst::new(
            AArch64Opcode::MovR,
            vec![
                MO::VReg(VReg::new(victim, class)),
                MO::VReg(VReg::new(12, class)),
            ],
        ));
        f.block_mut(body).insts.insert(pos, id);
        assert!(run(&mut f), "the other constant still merges");
        let ops = vreg_operands(&f, body);
        let reads_victim =
            ops[1].iter().any(|v| v.id == victim) || ops[0].iter().any(|v| v.id == victim);
        assert!(
            reads_victim,
            "v{victim} ({class:?}) keeps its own readers: {ops:?}"
        );
    }
}

#[test]
fn keeps_a_duplicate_when_the_first_chain_is_dead_by_then() {
    // v1 = A ; x = v1 + v1 ; v2 = A ; y = v2 + v2: v1 dies before v2's chain,
    // so pointing y at v1 would lengthen v1's live range.
    for v1_read_later in [false, true] {
        let mut f = MachFunction::new("d".into(), Signature::new(vec![], vec![]));
        let b = f.entry;
        chain(&mut f, b, g64(1), A);
        push(&mut f, b, rr(AArch64Opcode::AddRR, g64(3), g64(1), g64(1)));
        chain(&mut f, b, g64(2), A);
        push(&mut f, b, rr(AArch64Opcode::AddRR, g64(4), g64(2), g64(2)));
        if v1_read_later {
            push(&mut f, b, rr(AArch64Opcode::AddRR, g64(5), g64(1), g64(4)));
        }
        assert_eq!(run(&mut f), v1_read_later, "v1 read later: {v1_read_later}");
    }
}

#[test]
fn keeps_chains_with_metadata_beyond_their_operands() {
    use trust_cg_ir::regs::{NZCV, X0};
    use trust_cg_ir::{InstFlags, ProofAnnotation};
    // Any instruction of either chain carrying extra metadata: no merge of
    // that constant (the other one still merges).
    for chain_index in [0usize, 2] {
        for inst_index in [0usize, 3] {
            for mutation in 0..4 {
                let (mut f, pre, body) = lcg_loop();
                let id = f.block(pre).insts[chain_index * 4 + inst_index];
                let inst = f.inst_mut(id);
                match mutation {
                    0 => inst.flags |= InstFlags::IS_PSEUDO,
                    1 => inst.implicit_defs = &[NZCV],
                    2 => inst.implicit_uses = &[X0],
                    _ => inst.proof = Some(ProofAnnotation::InBounds),
                }
                assert!(run(&mut f));
                let ops = vreg_operands(&f, body);
                assert_eq!(
                    ops[1],
                    vec![g64(10), g64(11), g64(3), g64(2)],
                    "chain {chain_index} inst {inst_index} mutation {mutation}"
                );
            }
        }
    }
}

#[test]
fn keeps_a_duplicate_whose_reader_another_block_also_links() {
    // The second Madd (a reader of both duplicates) is also linked from a
    // block outside the layout: it cannot be rewritten in place. A block
    // outside the layout naming a duplicate refuses the same way.
    for case in 0..3 {
        let (mut f, _, body) = lcg_loop();
        let hidden = f.create_block();
        let reader = f.block(body).insts[1];
        match case {
            0 => f.append_inst(hidden, reader),
            1 => {
                push(
                    &mut f,
                    hidden,
                    rr(AArch64Opcode::AddRR, g64(20), g64(3), g64(4)),
                );
            }
            _ => {}
        }
        f.block_order.retain(|&b| b != hidden);
        assert_eq!(run(&mut f), case == 2, "case {case}");
    }
}

#[test]
fn provenance_of_a_removed_chain_moves_to_the_kept_one() {
    let (mut f, pre, _) = lcg_loop();
    let insts = f.block(pre).insts.clone();
    let mut provenance = ProvenanceMap::new();
    for (k, &id) in insts.iter().enumerate() {
        provenance.record_lowering(TrustIrInstId(k as u32), &[id], PassId::new("isel"));
    }
    assert!(ConstChainDedup.run_with_provenance(&mut f, &mut provenance));
    // The kept A chain's last MOVK (index 3) carries the removed A chain's
    // origins (indices 8..12) too.
    let entry = provenance.get_entry(insts[3]).expect("kept entry");
    for k in [3u32, 8, 9, 10, 11] {
        assert!(
            entry.trust_ir_origins.contains(&TrustIrInstId(k)),
            "origin {k}: {:?}",
            entry.trust_ir_origins
        );
    }
}

/// The pre-batching apply order, retained only as a differential oracle.
/// Discovery and retirement are the same production contracts; this checks
/// mutation/history equivalence, not a semantic certificate or benchmark.
fn sequential_apply(
    func: &mut MachFunction,
    merges: Vec<Merge>,
    mut provenance: Option<&mut ProvenanceMap>,
) -> bool {
    if merges.is_empty() {
        return false;
    }
    let mut rewritten = HashSet::default();
    let mut consumed = Vec::new();
    for merge in &merges {
        let block = func
            .block_order
            .iter()
            .copied()
            .find(|&b| func.block(b).insts.contains(&merge.dup_insts[0]))
            .expect("original duplicate owner");
        let dead: HashSet<_> = merge.dup_insts.iter().copied().collect();
        for block in func.block_order.clone() {
            for id in func.block(block).insts.clone() {
                if dead.contains(&id) {
                    continue;
                }
                let inst = func.inst_mut(id);
                let mut hit = false;
                for op in &mut inst.operands {
                    if let MO::VReg(v) = op
                        && v.id == merge.dup.id
                    {
                        *v = VReg::new(merge.keep.id, v.class);
                        hit = true;
                    }
                }
                if hit {
                    rewritten.insert(id);
                }
            }
        }
        func.block_mut(block).insts.retain(|id| !dead.contains(id));
        consumed.extend(merge.dup_insts.iter().copied());
        if let Some(provenance) = provenance.as_deref_mut() {
            for &id in &merge.dup_insts {
                provenance.record_merge(&[merge.keep_last, id], merge.keep_last, pass_id());
            }
        }
    }
    crate::retirement::retire_unlinked(func, &consumed);
    if let Some(provenance) = provenance {
        for id in rewritten {
            provenance.record_in_place_transform(id, pass_id());
        }
    }
    true
}

fn assert_same_provenance(actual: &ProvenanceMap, expected: &ProvenanceMap, arena_len: usize) {
    for index in 0..arena_len {
        let id = InstId(index as u32);
        match (actual.get_entry(id), expected.get_entry(id)) {
            (Some(actual), Some(expected)) => {
                assert_eq!(actual.trust_ir_origins, expected.trust_ir_origins);
                assert_eq!(actual.transforms, expected.transforms);
                assert_eq!(actual.status, expected.status);
            }
            (None, None) => {}
            _ => panic!("different active provenance at {id:?}"),
        }
        let origin = TrustIrInstId(index as u32 + 100);
        assert_eq!(
            actual.get_mach_insts(origin),
            expected.get_mach_insts(origin)
        );
    }
}

fn assert_batch_matches_sequential(mut original: MachFunction) -> MachFunction {
    let original_provenance = capture_history(&mut original);
    let mut actual = original.clone();
    let mut expected = original.clone();
    let merges = find_merges(&original);
    let changed = !merges.is_empty();
    // This is the discovery fact that makes one-lookup substitutions valid:
    // a canonical keep is never another accepted duplicate, even with many
    // interleaved equal runs in different blocks or width classes.
    let duplicates: HashSet<_> = merges.iter().map(|m| m.dup.id).collect();
    assert_eq!(duplicates.len(), merges.len(), "unique duplicate IDs");
    assert!(merges.iter().all(|m| !duplicates.contains(&m.keep.id)));
    assert_eq!(ConstChainDedup.run(&mut actual), changed);
    assert_eq!(sequential_apply(&mut expected, merges, None), changed);
    assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    assert_eq!(actual.lowering_provenance, original.lowering_provenance);
    assert_eq!(actual.insts.len(), original.insts.len());
    let mut with_history = original.clone();
    let mut expected_history = original.clone();
    let mut actual_provenance = original_provenance.clone();
    let mut expected_provenance = original_provenance;
    assert_eq!(
        ConstChainDedup.run_with_provenance(&mut with_history, &mut actual_provenance),
        changed
    );
    assert_eq!(
        sequential_apply(
            &mut expected_history,
            find_merges(&original),
            Some(&mut expected_provenance),
        ),
        changed
    );
    assert_eq!(format!("{with_history:?}"), format!("{actual:?}"));
    assert_eq!(format!("{with_history:?}"), format!("{expected_history:?}"));
    assert_same_provenance(
        &actual_provenance,
        &expected_provenance,
        original.insts.len(),
    );
    actual
}

#[test]
fn batch_many_interleaved_merges_preserves_values_width_views_and_history() {
    for groups in [1_u32, 5, 17] {
        let mut func = MachFunction::new("batch".into(), Signature::new(vec![], vec![]));
        let second = func.create_block();
        let mut next = 1_u32;
        let mut outputs = Vec::new();
        for block in [func.entry, second] {
            let mut carriers: Vec<Vec<VReg>> = vec![Vec::new(); groups as usize * 2];
            // Repeated runs are interleaved by value and width. Six carriers
            // per key must all resolve directly to the FIRST survivor.
            for _copy in 0..6 {
                for group in 0..groups {
                    for (width, class) in [RegClass::Gpr32, RegClass::Gpr64].into_iter().enumerate()
                    {
                        let v = VReg::new(next, class);
                        next += 1;
                        chain(&mut func, block, v, A ^ (u64::from(group) << 20));
                        carriers[group as usize * 2 + width].push(v);
                    }
                }
            }
            for values in &carriers {
                let class = values[0].class;
                let sum = VReg::new(next, class);
                let mixed = VReg::new(next + 1, class);
                let low = g32(next + 2);
                next += 3;
                push(
                    &mut func,
                    block,
                    rr(AArch64Opcode::AddRR, sum, values[0], values[1]),
                );
                push(
                    &mut func,
                    block,
                    MachInst::new(
                        AArch64Opcode::Madd,
                        vec![
                            MO::VReg(mixed),
                            MO::VReg(values[2]),
                            MO::VReg(values[3]),
                            MO::VReg(values[4]),
                        ],
                    ),
                );
                push(
                    &mut func,
                    block,
                    rr(
                        AArch64Opcode::EorRR,
                        low,
                        g32(values[1].id),
                        g32(values[5].id),
                    ),
                );
                outputs.extend([sum, mixed, low]);
            }
        }
        func.try_sync_vreg_counter().unwrap();
        assert_eq!(find_merges(&func).len(), groups as usize * 2 * 5 * 2);
        let mut want = HashMap::default();
        for &block in &func.block_order {
            eval_block(&func, block, &mut want);
        }
        let actual = assert_batch_matches_sequential(func);
        let mut got = HashMap::default();
        for &block in &actual.block_order {
            eval_block(&actual, block, &mut got);
        }
        for out in outputs {
            assert_eq!(got[&out.id], want[&out.id], "{out:?}");
        }
    }
}

#[test]
fn batch_mixed_refusals_hidden_owners_and_orphans_match_sequential() {
    use trust_cg_ir::ProofAnnotation;

    for shape in 0..5 {
        let (mut func, pre, body) = lcg_loop();
        let before_links = func.block(pre).insts.clone();
        let refused = before_links[8..12].to_vec();
        match shape {
            0 => func.inst_mut(refused[1]).proof = Some(ProofAnnotation::NoOverflow),
            1 => {
                let id = func.push_inst(MachInst::new(
                    AArch64Opcode::Movz,
                    vec![MO::VReg(g32(3)), MO::Imm(0)],
                ));
                func.block_mut(body).insts.insert(0, id);
            }
            2 | 3 => {
                let hidden = func.create_block();
                if shape == 2 {
                    func.append_inst(hidden, refused[0]);
                } else {
                    push(
                        &mut func,
                        hidden,
                        rr(AArch64Opcode::AddRR, g64(20), g64(3), g64(3)),
                    );
                }
                func.block_order.retain(|&b| b != hidden);
            }
            _ => {
                let shared = func.block(body).insts[1];
                func.block_mut(body).insts.push(shared);
            }
        }
        let orphan = func.push_inst(rr(AArch64Opcode::AddRR, g64(30), g64(31), g64(32)));
        let before = func.clone();
        let expected_count = if shape == 4 { 0 } else { 1 };
        assert_eq!(find_merges(&func).len(), expected_count);
        let actual = assert_batch_matches_sequential(func);
        for id in refused {
            // capture_history adds only a source location; all refusal
            // effects and operands must still be the original payload.
            let mut expected = before.inst(id).clone();
            expected.source_loc = actual.inst(id).source_loc;
            same_instruction(actual.inst(id), &expected);
        }
        let mut expected_orphan = before.inst(orphan).clone();
        expected_orphan.source_loc = actual.inst(orphan).source_loc;
        same_instruction(actual.inst(orphan), &expected_orphan);
    }
}
