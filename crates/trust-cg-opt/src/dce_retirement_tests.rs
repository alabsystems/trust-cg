// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Exact dead-NZCV retirement and original local-certificate custody.
//! These controls are not independent solver replay or final-byte evidence.

use super::*;
use crate::effects::writes_flags;
use crate::pass_manager::MachinePass;
use trust_cg_ir::inst::{MachInst, ProofAnnotation, SourceLoc};
use trust_cg_ir::llsc::{LlscOrdering, LlscRmwOp};
use trust_cg_ir::provenance::{LoweringProvenance, SourceInstDigest, SourceInstId, TrustIrInstId};
use trust_cg_ir::regs::{NZCV, PReg, RegClass, SP, VReg, W0, W1, X0, X1, X2, X9};
use trust_cg_ir::{BlockId, ProvenanceStatus, Signature};

fn vr(id: u32, bits: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(
        id,
        if bits == 32 {
            RegClass::Gpr32
        } else {
            RegClass::Gpr64
        },
    ))
}

fn inst(op: AArch64Opcode, operands: Vec<MachOperand>) -> MachInst {
    MachInst::new(op, operands)
}

fn ret() -> MachInst {
    inst(AArch64Opcode::Ret, vec![])
}

fn add(func: &mut MachFunction, block: BlockId, instruction: MachInst) -> InstId {
    let id = func.push_inst(instruction);
    func.append_inst(block, id);
    id
}

fn function(instructions: Vec<MachInst>) -> (MachFunction, Vec<InstId>) {
    let mut func = MachFunction::new("dce_retirement".into(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    let ids = instructions
        .into_iter()
        .map(|i| add(&mut func, entry, i))
        .collect();
    func.try_sync_vreg_counter()
        .expect("fixture VReg arena fits");
    (func, ids)
}

fn annotated(instruction: MachInst) -> MachInst {
    instruction.with_source_loc(SourceLoc {
        file: 3,
        line: 27,
        col: 2,
    })
}

fn history(index: u32) -> LoweringProvenance {
    LoweringProvenance::SourceInst {
        id: SourceInstId { block: 0, index },
        digest: SourceInstDigest::compute("Icmp", 2, 1),
        trust_ir_inst: Some(TrustIrInstId(index + 70)),
    }
}

fn assert_same(actual: &MachInst, expected: &MachInst) {
    assert_eq!(actual.opcode, expected.opcode);
    assert_eq!(actual.operands, expected.operands);
    assert_eq!(actual.flags, expected.flags);
    assert_eq!(actual.implicit_defs, expected.implicit_defs);
    assert_eq!(actual.implicit_uses, expected.implicit_uses);
    assert_eq!(actual.proof, expected.proof);
    assert_eq!(actual.source_loc, expected.source_loc);
}

fn assert_retired(func: &MachFunction, id: InstId) {
    let instruction = func.inst(id);
    assert_eq!(instruction.opcode, AArch64Opcode::Nop);
    assert_eq!(instruction.flags, InstFlags::IS_PSEUDO);
    assert!(instruction.operands.is_empty());
    assert!(instruction.implicit_defs.is_empty());
    assert!(instruction.implicit_uses.is_empty());
    assert!(instruction.proof.is_none());
    assert!(instruction.source_loc.is_none());
    assert!(func.blocks.iter().all(|block| !block.insts.contains(&id)));
}

/// Capture the original checker input before the pass can mutate its arena.
fn original_certificate(func: &MachFunction, id: InstId) -> DceCertificate {
    let (block, position) = func
        .blocks
        .iter()
        .enumerate()
        .find_map(|(block, body)| {
            body.insts
                .iter()
                .position(|candidate| *candidate == id)
                .map(|position| (block, position))
        })
        .expect("original live writer");
    let facts = NzcvLiveness::compute(func)
        .dead_flags_write(func, block, position)
        .expect("original writer has dead flags");
    make_dce_certificate(
        id,
        func.inst(id),
        &collect_used_vregs(func),
        &DceCertifiedOptions::default(),
        Some(facts),
    )
}

fn assert_certificate_snapshot(actual: &DceCertificate, expected: &DceCertificate) {
    assert_eq!(actual, expected);
    assert_eq!(actual.result, DceCertificateResult::Verified);
    assert_eq!(actual.contract, DceContract::DeadNzcvWriteUnobservable);
    assert_ne!(actual.source_opcode, "Nop");
    assert_eq!(
        actual.obligation_hash,
        dce_obligation_hash(
            InstId(actual.source_inst_id),
            &actual.source_opcode,
            &actual.source_operands,
            &actual.source_location,
            &actual.use_def,
            &actual.side_effects,
            &actual.visibility,
            actual.nzcv.as_ref(),
        )
    );
}

fn writer_shapes() -> Vec<MachInst> {
    use AArch64Opcode::*;
    let mut shapes = Vec::new();
    for bits in [32, 64] {
        shapes.push(inst(CmpRR, vec![vr(0, bits), vr(1, bits)]));
        shapes.push(inst(CmpRI, vec![vr(0, bits), MachOperand::Imm(7)]));
        shapes.push(inst(Tst, vec![vr(0, bits), vr(1, bits)]));
        shapes.push(inst(Tst, vec![vr(0, bits), MachOperand::Imm(1)]));
    }
    for (rr, ri, a, b) in [(CMPWrr, CMPWri, W0, W1), (CMPXrr, CMPXri, X0, X1)] {
        shapes.push(inst(rr, vec![MachOperand::PReg(a), MachOperand::PReg(b)]));
        shapes.push(inst(ri, vec![MachOperand::PReg(a), MachOperand::Imm(4095)]));
    }
    shapes
}

#[test]
fn all_integer_flag_writer_families_retire_exact_ids_with_original_certificates() {
    for writer in writer_shapes() {
        let (mut func, ids) = function(vec![annotated(writer), ret()]);
        let dead = ids[0];
        func.set_inst_lowering_provenance(dead, history(1));
        let before = func.clone();
        let expected = original_certificate(&before, dead);
        assert_eq!(expected.source_location.as_deref(), Some("file:3:27:2"));
        let run = DeadCodeElimination.run_certified(&mut func);
        assert!(
            run.changed && run.is_certified(),
            "{}: {run:?}",
            expected.source_opcode
        );
        assert_retired(&func, dead);
        assert_eq!(func.insts.len(), before.insts.len());
        assert_eq!(func.block(func.entry).insts, [ids[1]]);
        assert_same(func.inst(ids[1]), before.inst(ids[1]));
        assert_eq!(
            func.inst_lowering_provenance(dead),
            before.inst_lowering_provenance(dead)
        );
        assert_eq!(run.certificates.len(), 1);
        assert_certificate_snapshot(&run.certificates[0], &expected);
        let once = format!("{func:?}");
        let repeated = DeadCodeElimination.run_certified(&mut func);
        assert!(
            !repeated.changed && repeated.certificates.is_empty() && repeated.failures.is_empty()
        );
        assert_eq!(format!("{func:?}"), once);
    }
}

#[test]
fn chained_next_writer_custody_survives_both_writers_becoming_tombstones() {
    let (mut func, ids) = function(vec![
        annotated(inst(AArch64Opcode::CmpRR, vec![vr(0, 64), vr(1, 64)])),
        annotated(inst(
            AArch64Opcode::CmpRI,
            vec![vr(2, 64), MachOperand::Imm(19)],
        )),
        inst(AArch64Opcode::CmpRR, vec![vr(2, 64), vr(3, 64)]),
        inst(AArch64Opcode::CSet, vec![vr(4, 64), MachOperand::Imm(0)]),
        inst(
            AArch64Opcode::StrRI,
            vec![vr(4, 64), MachOperand::PReg(SP), MachOperand::Imm(8)],
        ),
        ret(),
    ]);
    for &id in &ids[..2] {
        func.set_inst_lowering_provenance(id, history(id.0));
    }
    let before = func.clone();
    let expected: Vec<_> = ids[..2]
        .iter()
        .map(|&id| original_certificate(&before, id))
        .collect();
    assert_eq!(
        expected[0].nzcv.as_ref().unwrap().exit,
        DeadFlagsExit::NextWriter { inst_id: ids[1].0 }
    );
    assert_eq!(
        expected[1].nzcv.as_ref().unwrap().exit,
        DeadFlagsExit::NextWriter { inst_id: ids[2].0 }
    );
    let mut provenance = ProvenanceMap::new();
    for &id in &ids {
        provenance.record_lowering(TrustIrInstId(id.0 + 70), &[id], PassId::new("isel"));
    }
    let run = DeadCodeElimination.run_certified_with_provenance(&mut func, &mut provenance);
    assert!(run.is_certified());
    assert_eq!(func.block(func.entry).insts, ids[2..]);
    for (&id, expected) in ids[..2].iter().zip(&expected) {
        assert_retired(&func, id);
        assert_eq!(
            func.inst_lowering_provenance(id),
            before.inst_lowering_provenance(id)
        );
        let certificate = run
            .certificates
            .iter()
            .find(|cert| cert.source_inst_id == id.0)
            .unwrap();
        assert_certificate_snapshot(certificate, expected);
        assert!(
            matches!(&provenance.get_entry(id).unwrap().status, ProvenanceStatus::OptimizedAway { pass, .. } if pass.name() == "dce")
        );
    }
    for &id in &ids[2..] {
        assert_same(func.inst(id), before.inst(id));
        assert!(provenance.get_entry(id).unwrap().is_active());
    }
    let record = dce_certified_pass_record(&func.name, &run);
    assert_eq!(record.summary, serde_json::to_value(&run).unwrap());
    assert_eq!(
        record.obligation_hash,
        dce_run_obligation_hash(&func.name, &run)
    );
}

#[test]
fn normal_and_certified_modes_have_identical_retirement_and_stable_ids() {
    for writer in writer_shapes() {
        let (original, ids) = function(vec![annotated(writer), ret()]);
        let mut normal = original.clone();
        let mut certified = original.clone();
        assert!(DeadCodeElimination.run(&mut normal));
        let run = DeadCodeElimination.run_certified(&mut certified);
        assert!(run.changed && run.is_certified());
        assert_eq!(format!("{normal:?}"), format!("{certified:?}"));
        assert_retired(&normal, ids[0]);
        assert_retired(&certified, ids[0]);
        assert!(!DeadCodeElimination.run(&mut normal));
    }
}

#[test]
fn malformed_writer_shapes_implicit_operands_and_extra_effects_are_not_retired() {
    for mutation in 0..20 {
        let (mut func, ids) = function(vec![
            annotated(inst(AArch64Opcode::CmpRR, vec![vr(0, 64), vr(1, 64)])),
            ret(),
        ]);
        let bad = func.inst_mut(ids[0]);
        match mutation {
            0 => bad.operands.push(MachOperand::Imm(0)),
            1 => bad.operands.pop().map(|_| ()).unwrap(),
            2 => bad.operands[1] = MachOperand::Imm(0),
            3 => bad.operands[1] = vr(1, 32),
            4 => bad.operands[1] = MachOperand::VReg(VReg::new(1, RegClass::Fpr64)),
            5 => bad.operands[1] = MachOperand::VReg(VReg::new(1, RegClass::System)),
            6 => bad.operands[1] = vr(u32::MAX, 64),
            7 => bad.operands[1] = MachOperand::PReg(PReg::new(u16::MAX)),
            8 => bad.operands[0] = MachOperand::PReg(SP),
            9 => bad.flags = InstFlags::EMPTY,
            10 => bad.flags.insert(InstFlags::READS_MEMORY),
            11 => bad.flags.insert(InstFlags::WRITES_MEMORY),
            12 => bad.flags.insert(InstFlags::IS_CALL),
            13 => bad.flags.insert(InstFlags::IS_BRANCH),
            14 => bad.flags.insert(InstFlags::IS_PSEUDO),
            15 => bad.flags.insert(InstFlags::IS_RETURN),
            16 => bad.flags.insert(InstFlags::SPILL_SLOT_ACCESS),
            17 => bad.implicit_defs = &[X9],
            18 => bad.implicit_uses = &[NZCV],
            19 => bad.proof = Some(ProofAnnotation::Pure),
            _ => unreachable!(),
        }
        let original = func.clone();
        for certified in [false, true] {
            let mut tested = original.clone();
            if certified {
                let run = DeadCodeElimination.run_certified(&mut tested);
                assert!(
                    run.certificates
                        .iter()
                        .all(|cert| cert.source_inst_id != ids[0].0)
                );
            } else {
                DeadCodeElimination.run(&mut tested);
            }
            assert!(
                tested.block(tested.entry).insts.contains(&ids[0]),
                "mutation{mutation}/certified{certified}"
            );
            assert_same(tested.inst(ids[0]), original.inst(ids[0]));
        }
    }
    for (op, operands) in [
        (AArch64Opcode::CMPWrr, vec![vr(0, 64), vr(1, 64)]),
        (AArch64Opcode::CMPXri, vec![vr(0, 32), MachOperand::Imm(1)]),
        (AArch64Opcode::CmpRI, vec![vr(0, 64), MachOperand::Imm(-1)]),
        (
            AArch64Opcode::CmpRI,
            vec![vr(0, 64), MachOperand::Imm(4096)],
        ),
        (
            AArch64Opcode::CmpRI,
            vec![vr(0, 64), MachOperand::Imm(1), MachOperand::Imm(12)],
        ),
        (AArch64Opcode::Tst, vec![vr(0, 64), MachOperand::Imm(0)]),
        (AArch64Opcode::Tst, vec![vr(0, 64), MachOperand::Imm(-1)]),
    ] {
        let (original, ids) = function(vec![inst(op, operands), ret()]);
        for certified in [false, true] {
            let mut func = original.clone();
            if certified {
                let run = DeadCodeElimination.run_certified(&mut func);
                assert!(
                    run.certificates
                        .iter()
                        .all(|cert| cert.source_inst_id != ids[0].0)
                );
            } else {
                DeadCodeElimination.run(&mut func);
            }
            assert!(func.block(func.entry).insts.contains(&ids[0]));
            assert_same(func.inst(ids[0]), original.inst(ids[0]));
        }
    }
}

fn live_reader(opcode: AArch64Opcode) -> MachInst {
    let operands = match opcode {
        AArch64Opcode::CSet => vec![vr(4, 64), MachOperand::Imm(0)],
        AArch64Opcode::Csel => vec![vr(4, 64), vr(0, 64), vr(1, 64), MachOperand::Imm(0)],
        AArch64Opcode::Adc => vec![vr(4, 64), vr(0, 64), vr(1, 64)],
        AArch64Opcode::BCond => vec![MachOperand::Imm(0), MachOperand::Block(BlockId(0))],
        _ => unreachable!(),
    };
    inst(opcode, operands)
}

#[test]
fn actual_flag_readers_keep_the_prior_writer_and_its_original_arena_slot() {
    for reader in [
        AArch64Opcode::CSet,
        AArch64Opcode::Csel,
        AArch64Opcode::Adc,
        AArch64Opcode::BCond,
    ] {
        let (original, ids) = function(vec![
            annotated(inst(AArch64Opcode::CmpRR, vec![vr(0, 64), vr(1, 64)])),
            live_reader(reader),
            inst(
                AArch64Opcode::StrRI,
                vec![vr(4, 64), MachOperand::PReg(SP), MachOperand::Imm(8)],
            ),
            ret(),
        ]);
        for certified in [false, true] {
            let mut func = original.clone();
            if certified {
                let run = DeadCodeElimination.run_certified(&mut func);
                assert!(
                    run.certificates
                        .iter()
                        .all(|cert| cert.source_inst_id != ids[0].0)
                );
            } else {
                DeadCodeElimination.run(&mut func);
            }
            assert!(func.block(func.entry).insts.contains(&ids[0]));
            assert_same(func.inst(ids[0]), original.inst(ids[0]));
        }
    }
}

#[test]
fn implicit_nzcv_read_and_real_llsc_pseudo_are_not_definite_flag_kills() {
    let barriers = [
        inst(AArch64Opcode::CmpRR, vec![vr(2, 64), vr(3, 64)]).with_implicit_uses(&[NZCV]),
        inst(
            AArch64Opcode::LlscRmw64,
            vec![
                vr(6, 64),
                vr(7, 64),
                vr(8, 32),
                vr(1, 64),
                MachOperand::PReg(X2),
                MachOperand::Imm(LlscRmwOp::Add.to_imm()),
                MachOperand::Imm(LlscOrdering::RELAXED.to_imm()),
            ],
        ),
    ];
    for barrier in barriers {
        assert!(
            writes_flags(barrier.opcode),
            "the regression requires the old Kill path"
        );
        let (original, ids) = function(vec![
            annotated(inst(AArch64Opcode::CmpRR, vec![vr(0, 64), vr(1, 64)])),
            barrier,
            live_reader(AArch64Opcode::CSet),
            inst(
                AArch64Opcode::StrRI,
                vec![vr(4, 64), MachOperand::PReg(SP), MachOperand::Imm(8)],
            ),
            ret(),
        ]);
        for certified in [false, true] {
            let mut func = original.clone();
            if certified {
                let run = DeadCodeElimination.run_certified(&mut func);
                assert!(
                    run.certificates
                        .iter()
                        .all(|cert| cert.source_inst_id != ids[0].0)
                );
            } else {
                DeadCodeElimination.run(&mut func);
            }
            assert!(func.block(func.entry).insts.contains(&ids[0]));
            assert_same(func.inst(ids[0]), original.inst(ids[0]));
            assert_same(func.inst(ids[1]), original.inst(ids[1]));
        }
    }
}

#[test]
fn cfg_dead_writer_retires_but_a_successor_reader_preserves_it() {
    for successor_reads in [false, true] {
        let (mut func, ids) = function(vec![annotated(inst(
            AArch64Opcode::CmpRR,
            vec![vr(0, 64), vr(1, 64)],
        ))]);
        let entry = func.entry;
        let exit = func.create_block();
        add(
            &mut func,
            entry,
            inst(AArch64Opcode::B, vec![MachOperand::Block(exit)]),
        );
        if successor_reads {
            add(&mut func, exit, live_reader(AArch64Opcode::CSet));
            add(
                &mut func,
                exit,
                inst(
                    AArch64Opcode::StrRI,
                    vec![vr(4, 64), MachOperand::PReg(SP), MachOperand::Imm(8)],
                ),
            );
        }
        add(&mut func, exit, ret());
        func.add_edge(entry, exit);
        func.try_sync_vreg_counter().unwrap();
        let original = func.clone();
        let expected = (!successor_reads).then(|| original_certificate(&original, ids[0]));
        for certified in [false, true] {
            let mut func = original.clone();
            if certified {
                let run = DeadCodeElimination.run_certified(&mut func);
                if let Some(expected) = &expected {
                    let actual = run
                        .certificates
                        .iter()
                        .find(|cert| cert.source_inst_id == ids[0].0)
                        .unwrap();
                    assert_certificate_snapshot(actual, expected);
                    assert_eq!(
                        actual.nzcv.as_ref().unwrap().exit,
                        DeadFlagsExit::CfgDead {
                            blocks: vec![exit.0]
                        }
                    );
                } else {
                    assert!(
                        run.certificates
                            .iter()
                            .all(|cert| cert.source_inst_id != ids[0].0)
                    );
                }
            } else {
                DeadCodeElimination.run(&mut func);
            }
            if successor_reads {
                assert!(func.block(entry).insts.contains(&ids[0]));
                assert_same(func.inst(ids[0]), original.inst(ids[0]));
            } else {
                assert_retired(&func, ids[0]);
            }
        }
    }
}

#[test]
fn removed_id_still_referenced_by_another_block_is_not_neutered() {
    let (mut func, ids) = function(vec![
        annotated(inst(AArch64Opcode::CmpRR, vec![vr(0, 64), vr(1, 64)])),
        ret(),
    ]);
    let inactive = func.create_block();
    func.append_inst(inactive, ids[0]);
    add(&mut func, inactive, ret());
    func.block_order = vec![func.entry];
    let original = func.clone();
    for certified in [false, true] {
        let mut func = original.clone();
        if certified {
            DeadCodeElimination.run_certified(&mut func);
        } else {
            DeadCodeElimination.run(&mut func);
        }
        assert!(func.block(func.entry).insts.contains(&ids[0]));
        assert!(func.block(inactive).insts.contains(&ids[0]));
        assert_same(func.inst(ids[0]), original.inst(ids[0]));
        assert_eq!(func.insts.len(), original.insts.len());
    }
}

#[test]
fn active_shared_writer_id_with_one_live_use_is_not_removed_from_either_block() {
    let (mut func, ids) = function(vec![
        annotated(inst(AArch64Opcode::CmpRR, vec![vr(0, 64), vr(1, 64)])),
        ret(),
    ]);
    let live = func.create_block();
    func.append_inst(live, ids[0]);
    add(&mut func, live, live_reader(AArch64Opcode::CSet));
    add(
        &mut func,
        live,
        inst(
            AArch64Opcode::StrRI,
            vec![vr(4, 64), MachOperand::PReg(SP), MachOperand::Imm(8)],
        ),
    );
    add(&mut func, live, ret());
    func.try_sync_vreg_counter().unwrap();
    assert!(func.block_order.contains(&live));
    let original = func.clone();
    for certified in [false, true] {
        let mut func = original.clone();
        if certified {
            let run = DeadCodeElimination.run_certified(&mut func);
            assert!(
                run.certificates
                    .iter()
                    .all(|cert| cert.source_inst_id != ids[0].0)
            );
        } else {
            DeadCodeElimination.run(&mut func);
        }
        assert!(func.block(func.entry).insts.contains(&ids[0]));
        assert!(func.block(live).insts.contains(&ids[0]));
        assert_same(func.inst(ids[0]), original.inst(ids[0]));
        assert_eq!(format!("{func:?}"), format!("{original:?}"));
    }
}
