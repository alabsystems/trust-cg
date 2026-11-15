// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Bridges implicit NZCV operands to opcode-modeled flag dependencies.
//! These are dependency-graph controls, not independent native proof replay.

use super::*;
use trust_cg_ir::Signature;
use trust_cg_ir::llsc::{LlscOrdering, LlscRmwOp};
use trust_cg_ir::regs::NZCV;

fn vr(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}

fn cmp(a: u32, b: u32) -> MachInst {
    MachInst::new(AArch64Opcode::CmpRR, vec![vr(a), vr(b)])
}

fn cset(dst: u32) -> MachInst {
    MachInst::new(AArch64Opcode::CSet, vec![vr(dst), MachOperand::Imm(0)])
}

fn fixture(instructions: Vec<MachInst>) -> MachFunction {
    let mut func = MachFunction::new("scheduler_nzcv".into(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    for instruction in instructions {
        let id = func.push_inst(instruction);
        func.append_inst(entry, id);
    }
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(entry, ret);
    func.try_sync_vreg_counter()
        .expect("fixture VReg arena fits");
    func
}

fn graphs(func: &MachFunction) -> [ScheduleDAG; 2] {
    [
        build_dag(func, func.entry),
        build_scheduling_dag_for_insts(func, &func.block(func.entry).insts),
    ]
}

fn assert_edge(dag: &ScheduleDAG, from: usize, to: usize) {
    assert!(
        dag.nodes[to].deps.contains(&from),
        "missing NZCV edge {from}->{to}"
    );
    assert!(
        dag.nodes[from].rev_deps.contains(&to),
        "missing reverse NZCV edge {from}->{to}"
    );
}

fn assert_no_edge(dag: &ScheduleDAG, from: usize, to: usize) {
    assert!(!dag.nodes[to].deps.contains(&from));
    assert!(!dag.nodes[from].rev_deps.contains(&to));
}

#[test]
fn implicit_nzcv_use_is_ordered_between_opcode_writers_without_data_overlap() {
    let plain = MachInst::new(AArch64Opcode::MovR, vec![vr(2), vr(3)]);
    let control = fixture(vec![cmp(0, 1), plain.clone(), cmp(4, 5), cset(6)]);
    for dag in graphs(&control) {
        // The registers are disjoint: no data, PReg or side-effect edge may
        // silently supply the bridge this test requires from NZCV metadata.
        assert_no_edge(&dag, 0, 1);
        assert_no_edge(&dag, 1, 2);
        assert_edge(&dag, 0, 2);
        assert_edge(&dag, 2, 3);
    }
    let func = fixture(vec![
        cmp(0, 1),
        plain.with_implicit_uses(&[NZCV]),
        cmp(4, 5),
        cset(6),
    ]);
    assert_eq!(func.inst(InstId(1)).implicit_uses, &[NZCV]);
    for dag in graphs(&func) {
        assert_edge(&dag, 0, 1);
        assert_edge(&dag, 1, 2);
        assert_edge(&dag, 2, 3);
    }
}

#[test]
fn implicit_nzcv_def_bridges_opcode_writer_and_reader_without_data_overlap() {
    let plain = MachInst::new(AArch64Opcode::MovR, vec![vr(2), vr(3)]);
    let control = fixture(vec![cmp(0, 1), plain.clone(), cset(4)]);
    for dag in graphs(&control) {
        assert_no_edge(&dag, 0, 1);
        assert_no_edge(&dag, 1, 2);
        assert_edge(&dag, 0, 2);
    }
    let func = fixture(vec![cmp(0, 1), plain.with_implicit_defs(&[NZCV]), cset(4)]);
    assert_eq!(func.inst(InstId(1)).implicit_defs, &[NZCV]);
    for dag in graphs(&func) {
        assert_edge(&dag, 0, 1);
        assert_edge(&dag, 1, 2);
    }
}

#[test]
fn real_llsc_pseudo_remains_a_may_clobber_after_an_opcode_flag_reader() {
    let llsc = MachInst::new(
        AArch64Opcode::LlscRmw64,
        vec![
            vr(6),
            vr(7),
            MachOperand::VReg(VReg::new(8, RegClass::Gpr32)),
            vr(9),
            vr(10),
            MachOperand::Imm(LlscRmwOp::Add.to_imm()),
            MachOperand::Imm(LlscOrdering::RELAXED.to_imm()),
        ],
    );
    // Surviving carriers must reach the encoder and refuse, not be skipped.
    assert!(!llsc.flags.contains(InstFlags::IS_PSEUDO));
    assert!(crate::effects::writes_flags(llsc.opcode));
    assert!(crate::effects::may_clobber_nzcv(&llsc));
    let func = fixture(vec![cmp(0, 1), cset(2), llsc, cmp(11, 12), cset(13)]);
    for dag in graphs(&func) {
        assert_edge(&dag, 0, 1);
        assert_edge(&dag, 1, 2);
        assert_edge(&dag, 2, 3);
        assert_edge(&dag, 3, 4);
    }
}
