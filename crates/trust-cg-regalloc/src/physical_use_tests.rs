// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Explicit ABI reads have the same reaching-value lifetime as implicit reads.

use super::*;

fn inst(defs: Vec<MachOperand>, uses: Vec<MachOperand>) -> MachInst {
    MachInst {
        opcode: phi_elim::IR_COPY_OPCODE,
        defs,
        uses,
        implicit_defs: Vec::new(),
        implicit_uses: Vec::new(),
        flags: InstFlags::default(),
        tied_operands: Vec::new(),
    }
}

fn call_results(split: bool, read: PReg) -> MachFunction {
    let state = VReg::new(0, RegClass::Gpr64);
    let status = VReg::new(1, RegClass::Gpr64);
    let mut call = inst(Vec::new(), Vec::new());
    call.opcode = 0x1234;
    call.flags = InstFlags::IS_CALL;
    call.implicit_defs = vec![PReg::new(0), PReg::new(1)];
    let insts = vec![
        call,
        inst(
            vec![MachOperand::VReg(state)],
            vec![MachOperand::PReg(PReg::new(0))],
        ),
        inst(Vec::new(), vec![MachOperand::VReg(state)]),
        inst(
            vec![MachOperand::VReg(status)],
            vec![MachOperand::PReg(read)],
        ),
        inst(Vec::new(), vec![MachOperand::VReg(status)]),
    ];
    let block = |indices: &[u32], preds: Vec<BlockId>, succs: Vec<BlockId>| MachBlock {
        insts: indices.iter().copied().map(InstId).collect(),
        preds,
        succs,
        loop_depth: 0,
    };
    let blocks = if split {
        vec![
            block(&[0, 1, 2], Vec::new(), vec![BlockId(1)]),
            block(&[3, 4], vec![BlockId(0)], Vec::new()),
        ]
    } else {
        vec![block(&[0, 1, 2, 3, 4], Vec::new(), Vec::new())]
    };
    MachFunction {
        name: "explicit_call_result_lifetime".into(),
        insts,
        block_order: (0..blocks.len() as u32).map(BlockId).collect(),
        blocks,
        entry_block: BlockId(0),
        next_vreg: 2,
        next_stack_slot: 0,
        stack_slots: BTreeMap::new(),
    }
}

#[test]
fn explicit_result_read_reserves_call_to_read_including_cross_block_aliases() {
    for split in [false, true] {
        for read in [PReg::new(1), PReg::new(33)] {
            // X1 and W1.
            let func = call_results(split, read);
            let live = compute_live_intervals(&func);
            let reserved = implicit_def_reservations(&func, &live.inst_numbering);
            for point in 0..=3 {
                assert!(
                    reserved[&read].contains(&point),
                    "{split}/{read:?}/{point}: {reserved:?}"
                );
            }
            assert!(!reserved[&read].contains(&4), "dead after the actual read");
            assert_eq!(
                reserved,
                implicit_def_reservations_reference(&func, &live.inst_numbering)
            );
        }
    }
}

#[test]
fn explicit_result_read_rejects_early_result_in_unread_lane() {
    let func = call_results(false, PReg::new(1));
    let state = VReg::new(0, RegClass::Gpr64);
    let status = VReg::new(1, RegClass::Gpr64);
    let corrupt = AllocationResult {
        allocation: BTreeMap::from([(state, PReg::new(1)), (status, PReg::new(2))]),
        spills: Vec::new(),
    };
    let report = regalloc_validator::validate_allocation(&func, &func, &corrupt);
    assert!(
        report.errors.iter().any(|error| matches!(error,
            regalloc_validator::ValidationError::PhysRegInterference {
                vreg, preg, reserved, point: 1,
            } if *vreg == state && *preg == PReg::new(1) && *reserved == PReg::new(1)
        )),
        "early X0→X1 destroys unread status: {report:?}"
    );
    let valid = AllocationResult {
        allocation: BTreeMap::from([(state, PReg::new(2)), (status, PReg::new(3))]),
        spills: Vec::new(),
    };
    assert!(regalloc_validator::validate_allocation(&func, &func, &valid).is_valid());
}

#[test]
fn explicit_result_read_allocators_preserve_copy_identity_without_clobber() {
    for config in [
        AllocConfig::default_aarch64(),
        AllocConfig::greedy_aarch64(),
    ] {
        let mut func = call_results(false, PReg::new(1));
        let result = allocate(&mut func, &config).expect("validated allocation");
        assert_ne!(
            result.allocation.get(&VReg::new(0, RegClass::Gpr64)),
            Some(&PReg::new(1))
        );
        assert_eq!(
            result.allocation.get(&VReg::new(1, RegClass::Gpr64)),
            Some(&PReg::new(1)),
            "the own-read copy-point exemption remains available"
        );
    }
}

#[test]
fn explicit_result_read_redefinition_kills_old_value_but_read_modify_write_uses_it() {
    let mut func = call_results(false, PReg::new(1));
    func.insts[2] = inst(vec![MachOperand::PReg(PReg::new(33))], Vec::new());
    let live = compute_live_intervals(&func);
    let reserved = implicit_def_reservations(&func, &live.inst_numbering);
    assert!(
        !reserved[&PReg::new(1)].contains(&1),
        "W1 redefinition kills old X1"
    );
    for implicit in [false, true] {
        func.insts[2].uses.clear();
        func.insts[2].implicit_uses.clear();
        if implicit {
            func.insts[2].implicit_uses.push(PReg::new(1));
        } else {
            func.insts[2].uses.push(MachOperand::PReg(PReg::new(1)));
        }
        let reserved = implicit_def_reservations(&func, &live.inst_numbering);
        assert!(
            reserved[&PReg::new(1)].contains(&1),
            "same-instruction read precedes alias def, implicit={implicit}"
        );
    }
}

#[test]
fn explicit_result_read_diamond_reserves_only_paths_with_reaching_values() {
    let mut func = call_results(false, PReg::new(1));
    let call = func.insts[0].clone();
    let read = func.insts[3].clone();
    let consume = func.insts[4].clone();
    func.insts = vec![
        call,
        inst(Vec::new(), Vec::new()),
        inst(Vec::new(), Vec::new()),
        inst(Vec::new(), Vec::new()),
        inst(vec![MachOperand::PReg(PReg::new(33))], Vec::new()),
        inst(Vec::new(), Vec::new()),
        read,
        consume,
    ];
    let block = |ids: &[u32], preds: &[u32], succs: &[u32]| MachBlock {
        insts: ids.iter().copied().map(InstId).collect(),
        preds: preds.iter().copied().map(BlockId).collect(),
        succs: succs.iter().copied().map(BlockId).collect(),
        loop_depth: 0,
    };
    func.blocks = vec![
        block(&[0], &[], &[1, 2]),
        block(&[1, 2], &[0], &[3]),
        block(&[3, 4, 5], &[0], &[3]),
        block(&[6, 7], &[1, 2], &[]),
    ];
    func.block_order = (0..4).map(BlockId).collect();
    let live = compute_live_intervals(&func);
    let reserved = implicit_def_reservations(&func, &live.inst_numbering);
    let points = &reserved[&PReg::new(1)];
    for i in [0, 1, 2, 4, 5, 6] {
        assert!(
            points.contains(&live.inst_numbering[&InstId(i)]),
            "{i}: {points:?}"
        );
    }
    for i in [3, 7] {
        assert!(
            !points.contains(&live.inst_numbering[&InstId(i)]),
            "{i}: {points:?}"
        );
    }
}

#[test]
fn explicit_result_read_loop_backedge_keeps_reaching_lane_live() {
    let mut func = call_results(true, PReg::new(1));
    // The result read is only on exit; an intervening self-loop may not use X1
    // for a scratch value, no matter how many iterations precede that read.
    func.blocks.insert(
        1,
        MachBlock {
            insts: vec![InstId(1), InstId(2)],
            preds: vec![BlockId(0), BlockId(1)],
            succs: vec![BlockId(1), BlockId(2)],
            loop_depth: 1,
        },
    );
    func.blocks[0].insts = vec![InstId(0)];
    func.blocks[2].preds = vec![BlockId(1)];
    func.block_order.push(BlockId(2));
    let live = compute_live_intervals(&func);
    let reserved = implicit_def_reservations(&func, &live.inst_numbering);
    for id in [InstId(1), InstId(2)] {
        assert!(reserved[&PReg::new(1)].contains(&live.inst_numbering[&id]));
    }
}

/// A valid allocation for [`call_results`]: neither vreg touches X0/X1.
fn call_results_valid_allocation() -> AllocationResult {
    AllocationResult {
        allocation: BTreeMap::from([
            (VReg::new(0, RegClass::Gpr64), PReg::new(2)),
            (VReg::new(1, RegClass::Gpr64), PReg::new(3)),
        ]),
        spills: Vec::new(),
    }
}

fn physical_liveness_unreserved(report: &regalloc_validator::ValidationReport) -> Vec<(PReg, u32)> {
    report
        .errors
        .iter()
        .filter_map(|error| match error {
            regalloc_validator::ValidationError::PhysicalLivenessUnreserved {
                preg, point, ..
            } => Some((*preg, *point)),
            _ => None,
        })
        .collect()
}

#[test]
fn independent_physical_liveness_accepts_correct_reservations() {
    for split in [false, true] {
        for read in [PReg::new(1), PReg::new(33)] {
            let func = call_results(split, read);
            let report = regalloc_validator::validate_allocation(
                &func,
                &func,
                &call_results_valid_allocation(),
            );
            assert!(report.is_valid(), "{split}/{read:?}: {report:?}");
        }
    }
}

#[test]
fn independent_physical_liveness_catches_reserve_dropping_successor_live_in() {
    use crate::physical_liveness::fault::{ReserveFault, inject};
    // X1 (the second call result) is read only in the successor block, so the
    // producing block's tail must stay reserved.
    let func = call_results(true, PReg::new(1));
    let live = compute_live_intervals(&func);
    let _fault = inject(ReserveFault::DropSuccessorLiveIn);
    let corrupted = implicit_def_reservations(&func, &live.inst_numbering);
    assert!(
        !corrupted[&PReg::new(1)].contains(&live.inst_numbering[&InstId(1)]),
        "the injected fault must actually corrupt reserve(): {corrupted:?}"
    );
    let report =
        regalloc_validator::validate_allocation(&func, &func, &call_results_valid_allocation());
    assert_eq!(
        physical_liveness_unreserved(&report),
        vec![(PReg::new(1), live.inst_numbering[&InstId(1)])],
        "{report:?}"
    );
}

#[test]
fn independent_physical_liveness_catches_reserve_ignoring_implicit_sinks() {
    use crate::physical_liveness::fault::{ReserveFault, inject};
    // Return-lane shape: X0 is defined, an unrelated instruction follows, and
    // only the return's implicit use reads X0.
    let def = inst(vec![MachOperand::PReg(PReg::new(0))], Vec::new());
    let other = inst(vec![MachOperand::PReg(PReg::new(9))], Vec::new());
    let mut ret = inst(Vec::new(), Vec::new());
    ret.flags = InstFlags::IS_RETURN;
    ret.implicit_uses = vec![PReg::new(0)];
    let func = MachFunction {
        name: "return_lane_implicit_sink".into(),
        insts: vec![def, other, ret],
        blocks: vec![MachBlock {
            insts: vec![InstId(0), InstId(1), InstId(2)],
            preds: Vec::new(),
            succs: Vec::new(),
            loop_depth: 0,
        }],
        block_order: vec![BlockId(0)],
        entry_block: BlockId(0),
        next_vreg: 0,
        next_stack_slot: 0,
        stack_slots: BTreeMap::new(),
    };
    let empty = AllocationResult {
        allocation: BTreeMap::new(),
        spills: Vec::new(),
    };
    let live = compute_live_intervals(&func);
    let clean = regalloc_validator::validate_allocation(&func, &func, &empty);
    assert!(physical_liveness_unreserved(&clean).is_empty(), "{clean:?}");

    let _fault = inject(ReserveFault::IgnoreImplicitUses);
    let report = regalloc_validator::validate_allocation(&func, &func, &empty);
    assert_eq!(
        physical_liveness_unreserved(&report),
        vec![(PReg::new(0), live.inst_numbering[&InstId(1)])],
        "{report:?}"
    );
}
