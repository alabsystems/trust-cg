//! Shared assertions for optional-rewrite publication boundaries.
//! These exercise construction, not native execution or formal equivalence.

use trust_cg_ir::{
    AArch64Opcode, BlockId, InstId, MachFunction, MachInst, MachOperand, RegClass, VReg,
};

/// Corrupt a recognized plan's input to exercise refusal, not frontend reachability.
pub(crate) fn corrupt(func: &mut MachFunction, pre: InstId, guard: BlockId, kind: usize) {
    match kind {
        0 => func.next_vreg = u32::MAX,
        1 => func.next_vreg = u32::MAX - 4,
        2 => func.noalias_params.push(u32::MAX),
        3 => func.inst_mut(pre).operands.clear(),
        4 => {
            for block in &mut func.blocks {
                block.insts.retain(|id| *id != pre);
            }
        }
        5 => func.block_order.retain(|id| *id != guard),
        _ => unreachable!("unknown test corruption"),
    }
}

pub(crate) fn assert_refusal(
    func: &mut MachFunction,
    apply: impl FnOnce(&mut MachFunction) -> bool,
) {
    let before = format!("{func:?}");
    assert!(!apply(func), "armed candidate must decline");
    assert_eq!(
        format!("{func:?}"),
        before,
        "refusal must preserve the whole function"
    );
}

pub(crate) fn every_reservation(
    label: &str,
    fixture: &MachFunction,
    apply: impl Fn(&mut MachFunction) -> bool,
) {
    let mut ordinary = fixture.clone();
    assert!(apply(&mut ordinary), "positive {label}");
    let count = ordinary.next_vreg.checked_sub(fixture.next_vreg).unwrap();
    assert!(count > 4, "must exercise late construction");
    for available in 0..count {
        let mut func = fixture.clone();
        func.next_vreg = u32::MAX - available;
        assert_refusal(&mut func, &apply);
    }

    // The exact final available range must still work; normalize only freshly
    // allocated register IDs and compare every other function field unchanged.
    let first = u32::MAX - count;
    let mut boundary = fixture.clone();
    boundary.next_vreg = first;
    assert!(apply(&mut boundary), "last representable range: {label}");
    assert_eq!(boundary.next_vreg, u32::MAX);
    for inst in &mut boundary.insts {
        for operand in &mut inst.operands {
            if let MachOperand::VReg(v) = operand
                && v.id >= first
            {
                v.id = fixture.next_vreg + (v.id - first);
            }
        }
    }
    boundary.next_vreg = ordinary.next_vreg;
    assert_eq!(format!("{boundary:?}"), format!("{ordinary:?}"), "{label}");
    println!("CANDIDATE_RESERVATIONS {label}: {count}");
}

pub(crate) fn sparse_ids(fixture: &MachFunction, apply: impl FnOnce(&mut MachFunction) -> bool) {
    let mut func = fixture.clone();
    func.push_inst(MachInst::new(
        AArch64Opcode::Movz,
        vec![
            MachOperand::VReg(VReg::new(1_000_000_000, RegClass::Gpr64)),
            MachOperand::Imm(0),
        ],
    ));
    func.noalias_params.push(1_000_000_007);
    func.next_vreg = 0;
    let first_new = func.insts.len();
    assert!(apply(&mut func));
    assert!(func.next_vreg > 1_000_000_007);
    for inst in &func.insts[first_new..] {
        for operand in &inst.operands {
            if let MachOperand::VReg(v) = operand {
                assert!(v.id < 1_000_000_000 || v.id > 1_000_000_007);
            }
        }
    }
}
