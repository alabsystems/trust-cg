// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use trust_cg_ir::aarch64_regs::{X0, X1, X2};
use trust_cg_ir::regs::NZCV;
use trust_cg_ir::{BlockId, InstFlags, Signature};

fn writer() -> MachInst {
    MachInst::new(
        AArch64Opcode::CmpRR,
        vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
    )
}

fn reader() -> MachInst {
    MachInst::new(
        AArch64Opcode::CSet,
        vec![MachOperand::PReg(X2), MachOperand::Imm(0)],
    )
}

fn neutral() -> MachInst {
    MachInst::new(
        AArch64Opcode::MovR,
        vec![MachOperand::PReg(X2), MachOperand::PReg(X1)],
    )
}

fn ret() -> MachInst {
    MachInst::new(AArch64Opcode::Ret, vec![])
}

fn function() -> MachFunction {
    MachFunction::new("nzcv_liveness".into(), Signature::new(vec![], vec![]))
}

fn append(func: &mut MachFunction, block: BlockId, inst: MachInst) -> InstId {
    let id = func.push_inst(inst);
    func.append_inst(block, id);
    id
}

fn tail(insts: Vec<MachInst>) -> MachFunction {
    let mut func = function();
    let entry = func.entry;
    append(&mut func, entry, MachInst::new(AArch64Opcode::Nop, vec![]));
    for inst in insts {
        append(&mut func, entry, inst);
    }
    func
}

fn on_entry(func: &MachFunction, block: BlockId) -> bool {
    FunctionVerifier::nzcv_dead_on_entry(func, block, &mut std::collections::HashSet::new())
}

#[test]
fn implicit_and_read_write_accesses_precede_any_kill() {
    let mut read_write = writer().with_implicit_uses(&[NZCV]);
    read_write.implicit_defs = &[NZCV];
    for inst in [
        neutral().with_implicit_uses(&[NZCV]),
        writer().with_implicit_uses(&[NZCV]),
        read_write,
        MachInst::new(AArch64Opcode::Adcs, vec![]),
        MachInst::new(AArch64Opcode::Sbcs, vec![]),
    ] {
        assert_eq!(
            FunctionVerifier::nzcv_liveness_effect(&inst),
            NzcvLivenessEffect::Reads,
            "{inst:?}"
        );
        let func = tail(vec![inst, writer(), ret()]);
        assert_eq!(
            FunctionVerifier::nzcv_dead_after(&func, func.entry, 0),
            Some(false)
        );
        assert!(!on_entry(&func, func.entry));
    }
}

#[test]
fn opaque_implicit_and_pseudo_effects_cannot_kill_incoming_flags() {
    let mut annotated_writer = writer();
    annotated_writer.flags = annotated_writer.flags.union(InstFlags::IS_PSEUDO);
    for inst in [
        neutral().with_implicit_defs(&[NZCV]),
        writer().with_implicit_defs(&[NZCV]),
        annotated_writer,
        MachInst::new(AArch64Opcode::LlscRmw64, vec![]),
        MachInst::new(AArch64Opcode::LlscCmpSwap32, vec![]),
        MachInst::new(AArch64Opcode::Retain, vec![]),
        MachInst::new(
            AArch64Opcode::Mrs,
            vec![MachOperand::PReg(X0), MachOperand::Imm(0xDA10)],
        ),
        MachInst::new(AArch64Opcode::TailCall, vec![MachOperand::Imm(0)]),
    ] {
        assert_eq!(
            FunctionVerifier::nzcv_liveness_effect(&inst),
            NzcvLivenessEffect::Unknown,
            "{inst:?}"
        );
        let func = tail(vec![inst, writer(), ret()]);
        assert_eq!(
            FunctionVerifier::nzcv_dead_after(&func, func.entry, 0),
            None
        );
        assert!(!on_entry(&func, func.entry));
    }
}

#[test]
fn ordinary_writers_exits_and_padding_remain_admitted_but_calls_are_neutral() {
    let call = MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Imm(0)]);
    assert_eq!(
        FunctionVerifier::nzcv_liveness_effect(&call),
        NzcvLivenessEffect::Neutral
    );
    for insts in [
        vec![writer(), reader(), ret()],
        vec![neutral(), ret()],
        vec![MachInst::new(AArch64Opcode::AlignNop, vec![]), ret()],
        vec![call.clone(), writer(), reader(), ret()],
        vec![MachInst::new(AArch64Opcode::Brk, vec![])],
    ] {
        let func = tail(insts);
        assert_eq!(
            FunctionVerifier::nzcv_dead_after(&func, func.entry, 0),
            Some(true)
        );
        assert!(on_entry(&func, func.entry));
    }
    for inst in [call.clone(), call.with_implicit_uses(&[NZCV])] {
        let func = tail(vec![inst, reader(), ret()]);
        assert_eq!(
            FunctionVerifier::nzcv_dead_after(&func, func.entry, 0),
            Some(false)
        );
        assert!(!on_entry(&func, func.entry));
    }
}

fn branch_with_late_fallthrough_writer(clear_flags: bool, annotated: bool) -> MachFunction {
    let mut func = function();
    let entry = func.entry;
    let taken = func.create_block();
    let fallthrough = func.create_block();
    append(&mut func, entry, MachInst::new(AArch64Opcode::Nop, vec![]));
    let mut branch = if annotated {
        let mut inst = neutral();
        inst.flags = inst.flags.union(InstFlags::IS_BRANCH);
        inst
    } else {
        MachInst::new(
            AArch64Opcode::Cbz,
            vec![MachOperand::PReg(X0), MachOperand::Block(taken)],
        )
    };
    if clear_flags {
        // Opcode defaults still expose this control boundary.
        branch.flags = InstFlags::EMPTY;
    }
    append(&mut func, entry, branch);
    append(&mut func, entry, writer());
    append(
        &mut func,
        entry,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(fallthrough)]),
    );
    func.block_mut(entry).succs = vec![taken, fallthrough];
    append(&mut func, taken, reader());
    append(&mut func, taken, ret());
    append(&mut func, fallthrough, ret());
    func
}

#[test]
fn taken_successor_read_survives_a_later_fallthrough_writer() {
    for (clear_flags, annotated) in [(false, false), (true, false)] {
        let mut func = branch_with_late_fallthrough_writer(clear_flags, annotated);
        assert_eq!(
            FunctionVerifier::nzcv_dead_after(&func, func.entry, 0),
            None
        );
        assert!(!on_entry(&func, func.entry));
        let taken = func.block(func.entry).succs[0];
        let first = func.block(taken).insts[0];
        func.insts[first.0 as usize] = writer();
        assert_eq!(
            FunctionVerifier::nzcv_dead_after(&func, func.entry, 0),
            Some(true)
        );
        assert!(on_entry(&func, func.entry));
    }
    let func = branch_with_late_fallthrough_writer(false, true);
    assert_eq!(
        FunctionVerifier::nzcv_dead_after(&func, func.entry, 0),
        None
    );
    assert!(!on_entry(&func, func.entry));
    let mut call_annotated = branch_with_late_fallthrough_writer(false, false);
    let branch = call_annotated.block(call_annotated.entry).insts[1];
    let inst = &mut call_annotated.insts[branch.0 as usize];
    inst.flags = inst.flags.union(InstFlags::IS_CALL);
    assert_eq!(
        FunctionVerifier::nzcv_dead_after(&call_annotated, call_annotated.entry, 0),
        None
    );
    assert!(!on_entry(&call_annotated, call_annotated.entry));
}

#[test]
fn conditional_fallthrough_read_is_not_hidden_by_dead_successors() {
    let mut func = function();
    let entry = func.entry;
    let next = func.create_block();
    append(&mut func, entry, MachInst::new(AArch64Opcode::Nop, vec![]));
    append(
        &mut func,
        entry,
        MachInst::new(
            AArch64Opcode::Cbz,
            vec![MachOperand::PReg(X0), MachOperand::Block(next)],
        ),
    );
    let observation = append(&mut func, entry, reader());
    append(
        &mut func,
        entry,
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(next)]),
    );
    func.block_mut(entry).succs = vec![next];
    append(&mut func, next, ret());
    assert_eq!(
        FunctionVerifier::nzcv_dead_after(&func, entry, 0),
        Some(false)
    );
    assert!(!on_entry(&func, entry));
    func.insts[observation.0 as usize] = writer();
    assert_eq!(
        FunctionVerifier::nzcv_dead_after(&func, entry, 0),
        Some(true)
    );
    assert!(on_entry(&func, entry));
}

#[test]
fn successors_share_the_same_implicit_read_and_opaque_contract() {
    for (inst, expected) in [
        (neutral().with_implicit_uses(&[NZCV]), false),
        (writer().with_implicit_uses(&[NZCV]), false),
        (writer().with_implicit_defs(&[NZCV]), false),
        (MachInst::new(AArch64Opcode::LlscRmw64, vec![]), false),
        (MachInst::new(AArch64Opcode::AlignNop, vec![]), true),
        (neutral(), true),
    ] {
        let mut func = tail(vec![]);
        let next = func.create_block();
        func.block_mut(func.entry).succs = vec![next];
        append(&mut func, next, inst);
        append(&mut func, next, writer());
        append(&mut func, next, ret());
        assert_eq!(on_entry(&func, next), expected);
        assert_eq!(
            FunctionVerifier::nzcv_dead_after(&func, func.entry, 0),
            expected.then_some(true)
        );
    }
}

#[test]
fn iterative_diamonds_shared_successors_and_cycles_keep_all_read_paths() {
    let mut func = tail(vec![]);
    let left = func.create_block();
    let right = func.create_block();
    let join = func.create_block();
    func.block_mut(func.entry).succs = vec![left, right];
    func.block_mut(left).succs = vec![join];
    func.block_mut(right).succs = vec![join];
    func.block_mut(join).succs = vec![left];
    assert!(on_entry(&func, func.entry));
    append(&mut func, right, reader());
    assert!(!on_entry(&func, func.entry));
    func.block_mut(right).insts.clear();
    append(&mut func, join, writer());
    assert!(on_entry(&func, func.entry));
    func.block_mut(join).insts.clear();
    append(&mut func, join, neutral().with_implicit_uses(&[NZCV]));
    assert!(!on_entry(&func, func.entry));
}

#[test]
fn iterative_walk_refuses_depth_and_pending_work_beyond_its_bound() {
    for blocks in [NZCV_LIVENESS_BLOCK_LIMIT, NZCV_LIVENESS_BLOCK_LIMIT + 1] {
        let mut func = function();
        let mut previous = func.entry;
        for _ in 1..blocks {
            let next = func.create_block();
            func.block_mut(previous).succs = vec![next];
            previous = next;
        }
        append(&mut func, previous, ret());
        assert_eq!(
            on_entry(&func, func.entry),
            blocks == NZCV_LIVENESS_BLOCK_LIMIT
        );
    }
    let mut wide = function();
    let mut successors = Vec::new();
    for _ in 0..=NZCV_LIVENESS_BLOCK_LIMIT {
        let next = wide.create_block();
        append(&mut wide, next, ret());
        successors.push(next);
    }
    wide.block_mut(wide.entry).succs = successors;
    assert!(!on_entry(&wide, wide.entry));
}

#[test]
fn malformed_positions_references_and_non_exiting_leaves_refuse() {
    let mut func = tail(vec![ret()]);
    assert_eq!(
        FunctionVerifier::nzcv_dead_after(&func, func.entry, usize::MAX),
        None
    );
    assert_eq!(
        FunctionVerifier::nzcv_dead_after(&func, BlockId(u32::MAX), 0),
        None
    );
    assert!(!on_entry(&func, BlockId(u32::MAX)));
    func.block_mut(func.entry).insts[1] = InstId(u32::MAX);
    assert_eq!(
        FunctionVerifier::nzcv_dead_after(&func, func.entry, 0),
        None
    );
    assert!(!on_entry(&func, func.entry));
    func.block_mut(func.entry).insts.truncate(1);
    assert_eq!(
        FunctionVerifier::nzcv_dead_after(&func, func.entry, 0),
        None
    );
    assert!(!on_entry(&func, func.entry));
    func.block_mut(func.entry).succs = vec![BlockId(u32::MAX)];
    assert_eq!(
        FunctionVerifier::nzcv_dead_after(&func, func.entry, 0),
        None
    );
    assert!(!on_entry(&func, func.entry));
}

#[test]
fn recorded_expansion_rows_fail_or_refuse_before_any_proof_replay() {
    use crate::aarch64_trap_expansion::TRAP_EXPANSION_IS_NOT_CREDIT;
    for (effect, read) in [
        (neutral().with_implicit_uses(&[NZCV]), true),
        (writer().with_implicit_uses(&[NZCV]), true),
        (writer().with_implicit_defs(&[NZCV]), false),
        (MachInst::new(AArch64Opcode::LlscRmw64, vec![]), false),
    ] {
        let mut func = function();
        let entry = func.entry;
        let carrier = MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::Imm(10),
            ],
        );
        let ids = [
            MachInst::new(
                AArch64Opcode::CmpRI,
                vec![MachOperand::PReg(X0), MachOperand::Imm(10)],
            ),
            MachInst::new(
                AArch64Opcode::BCond,
                vec![MachOperand::Imm(3), MachOperand::Imm(2)],
            ),
            MachInst::new(AArch64Opcode::Brk, vec![]),
        ]
        .into_iter()
        .map(|inst| append(&mut func, entry, inst))
        .collect();
        func.trap_expansions.push(trust_cg_ir::TrapExpansionRecord {
            carrier,
            insts: ids,
        });
        append(&mut func, entry, effect);
        append(&mut func, entry, writer());
        append(&mut func, entry, ret());
        let report = verify_function(&func);
        let row = &report.instructions[2].result;
        if read {
            assert!(
                matches!(row, InstructionVerificationResult::Failed { detail, .. }
                    if detail.contains("NZCV")),
                "{row:?}"
            );
        } else {
            assert!(
                matches!(row, InstructionVerificationResult::Unverified { reason }
                    if reason.contains("NZCV is not provably dead")),
                "{row:?}"
            );
        }
        assert!(!report.emitted_opcode_inventory().is_promotable());
        assert!(
            !matches!(row, InstructionVerificationResult::Unverified { reason }
            if reason.starts_with(TRAP_EXPANSION_IS_NOT_CREDIT))
        );
    }
}
