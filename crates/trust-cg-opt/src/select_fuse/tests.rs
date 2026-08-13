// trust-cg-opt - Select/flag fusion tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use super::*;
use crate::pass_manager::MachinePass;
use trust_cg_ir::{
    AArch64Opcode, BlockId, CondCode, MachFunction, MachInst, MachOperand, RegClass, Signature,
};

fn g64(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
}
fn g32(id: u32) -> MachOperand {
    MachOperand::VReg(VReg::new(id, RegClass::Gpr32))
}
fn imm(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}
fn cc(c: CondCode) -> MachOperand {
    MachOperand::Imm(c.encoding() as i64)
}

fn make_func(insts: Vec<MachInst>) -> MachFunction {
    let mut func = MachFunction::new(
        "test_select_fuse".to_string(),
        Signature::new(vec![], vec![]),
    );
    let block = func.entry;
    for inst in insts {
        let id = func.push_inst(inst);
        func.append_inst(block, id);
    }
    func
}

fn opcodes(func: &MachFunction) -> Vec<AArch64Opcode> {
    func.block(func.entry)
        .insts
        .iter()
        .map(|&id| func.inst(id).opcode)
        .collect()
}

fn csel_conds(func: &MachFunction) -> Vec<i64> {
    func.block(func.entry)
        .insts
        .iter()
        .filter_map(|&id| {
            let inst = func.inst(id);
            (inst.opcode == AArch64Opcode::Csel).then(|| inst.operands[3].as_imm().unwrap())
        })
        .collect()
}

/// The bsearch inner-loop shape the isel emits: one compare, one CSET, a
/// select-arm ADD between the CSET and the re-tests, and TWO independent
/// re-test + CSEL pairs on the same boolean.
fn bsearch_shape() -> Vec<MachInst> {
    vec![
        MachInst::new(AArch64Opcode::CmpRR, vec![g32(0), g32(1)]),
        MachInst::new(AArch64Opcode::CSet, vec![g64(2), cc(CondCode::LT)]),
        MachInst::new(AArch64Opcode::AddRR, vec![g32(3), g32(0), g32(1)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![g64(2), imm(0)]),
        MachInst::new(
            AArch64Opcode::Csel,
            vec![g32(4), g32(3), g32(0), cc(CondCode::NE)],
        ),
        MachInst::new(AArch64Opcode::CmpRI, vec![g64(2), imm(0)]),
        MachInst::new(
            AArch64Opcode::Csel,
            vec![g32(5), g32(1), g32(3), cc(CondCode::NE)],
        ),
    ]
}

#[test]
fn fuses_bsearch_shape_to_direct_csels_and_deletes_cset() {
    let mut func = make_func(bsearch_shape());
    let mut pass = SelectFlagFuse;
    assert!(pass.run(&mut func));

    let ops = opcodes(&func);
    assert!(!ops.contains(&AArch64Opcode::CmpRI), "re-tests deleted");
    assert!(
        !ops.contains(&AArch64Opcode::CSet),
        "fully-consumed CSET deleted"
    );
    assert_eq!(
        ops,
        vec![
            AArch64Opcode::CmpRR,
            AArch64Opcode::AddRR,
            AArch64Opcode::Csel,
            AArch64Opcode::Csel,
        ]
    );
    assert_eq!(
        csel_conds(&func),
        vec![
            CondCode::LT.encoding() as i64,
            CondCode::LT.encoding() as i64
        ]
    );
}

#[test]
fn eq_csel_fuses_to_inverted_condition() {
    let mut insts = bsearch_shape();
    insts[4].operands[3] = cc(CondCode::EQ);
    let mut func = make_func(insts);
    let mut pass = SelectFlagFuse;
    assert!(pass.run(&mut func));
    assert_eq!(
        csel_conds(&func),
        vec![
            CondCode::GE.encoding() as i64,
            CondCode::LT.encoding() as i64
        ]
    );
}

#[test]
fn multi_use_boolean_keeps_cset() {
    let mut insts = bsearch_shape();
    // An extra non-re-test use of the boolean.
    insts.push(MachInst::new(
        AArch64Opcode::OrrRR,
        vec![g64(6), g64(2), g64(2)],
    ));
    let mut func = make_func(insts);
    let mut pass = SelectFlagFuse;
    assert!(pass.run(&mut func));

    let ops = opcodes(&func);
    assert!(
        ops.contains(&AArch64Opcode::CSet),
        "live boolean keeps CSET"
    );
    assert!(!ops.contains(&AArch64Opcode::CmpRI));
    assert_eq!(
        csel_conds(&func),
        vec![
            CondCode::LT.encoding() as i64,
            CondCode::LT.encoding() as i64
        ]
    );
}

#[test]
fn csel_run_shares_one_retest() {
    // i128-style: one CMP #0 followed by TWO CSELs.
    let insts = vec![
        MachInst::new(AArch64Opcode::CmpRR, vec![g64(0), g64(1)]),
        MachInst::new(AArch64Opcode::CSet, vec![g64(2), cc(CondCode::GT)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![g64(2), imm(0)]),
        MachInst::new(
            AArch64Opcode::Csel,
            vec![g64(3), g64(0), g64(1), cc(CondCode::NE)],
        ),
        MachInst::new(
            AArch64Opcode::Csel,
            vec![g64(4), g64(1), g64(0), cc(CondCode::NE)],
        ),
    ];
    let mut func = make_func(insts);
    let mut pass = SelectFlagFuse;
    assert!(pass.run(&mut func));
    assert_eq!(
        csel_conds(&func),
        vec![
            CondCode::GT.encoding() as i64,
            CondCode::GT.encoding() as i64
        ]
    );
    assert!(!opcodes(&func).contains(&AArch64Opcode::CSet));
}

#[test]
fn aborts_when_unhandled_flag_reader_follows_deletion() {
    // A BCond after the fused pair would observe changed flags → the whole
    // plan must be dropped (fail-closed).
    let mut func = {
        let mut f = MachFunction::new("t".to_string(), Signature::new(vec![], vec![]));
        let b0 = f.entry;
        let b1 = f.create_block();
        let insts = vec![
            MachInst::new(AArch64Opcode::CmpRR, vec![g32(0), g32(1)]),
            MachInst::new(AArch64Opcode::CSet, vec![g64(2), cc(CondCode::LT)]),
            MachInst::new(AArch64Opcode::CmpRI, vec![g64(2), imm(0)]),
            MachInst::new(
                AArch64Opcode::Csel,
                vec![g32(4), g32(3), g32(0), cc(CondCode::NE)],
            ),
            MachInst::new(
                AArch64Opcode::BCond,
                vec![cc(CondCode::NE), MachOperand::Block(b1)],
            ),
        ];
        for inst in insts {
            let id = f.push_inst(inst);
            f.append_inst(b0, id);
        }
        f.add_edge(b0, b1);
        f
    };
    let mut pass = SelectFlagFuse;
    assert!(
        !pass.run(&mut func),
        "flag reader after deletion must abort"
    );
    assert!(opcodes(&func).contains(&AArch64Opcode::CmpRI));
    assert!(opcodes(&func).contains(&AArch64Opcode::CSet));
}

#[test]
fn no_fuse_when_flag_writer_between_cset_and_retest() {
    // A second compare between the CSET and the re-test: the CSET-observed
    // flags are gone, so nothing may fuse.
    let insts = vec![
        MachInst::new(AArch64Opcode::CmpRR, vec![g32(0), g32(1)]),
        MachInst::new(AArch64Opcode::CSet, vec![g64(2), cc(CondCode::LT)]),
        MachInst::new(AArch64Opcode::CmpRR, vec![g32(3), g32(1)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![g64(2), imm(0)]),
        MachInst::new(
            AArch64Opcode::Csel,
            vec![g32(4), g32(3), g32(0), cc(CondCode::NE)],
        ),
    ];
    let mut func = make_func(insts);
    let mut pass = SelectFlagFuse;
    assert!(!pass.run(&mut func));
    assert!(opcodes(&func).contains(&AArch64Opcode::CmpRI));
}

#[test]
fn no_fuse_when_boolean_redefined_before_retest() {
    let insts = vec![
        MachInst::new(AArch64Opcode::CmpRR, vec![g32(0), g32(1)]),
        MachInst::new(AArch64Opcode::CSet, vec![g64(2), cc(CondCode::LT)]),
        // Redefine the boolean.
        MachInst::new(AArch64Opcode::AddRR, vec![g64(2), g64(5), g64(6)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![g64(2), imm(0)]),
        MachInst::new(
            AArch64Opcode::Csel,
            vec![g32(4), g32(3), g32(0), cc(CondCode::NE)],
        ),
    ];
    let mut func = make_func(insts);
    let mut pass = SelectFlagFuse;
    assert!(!pass.run(&mut func));
}

#[test]
fn mixed_csel_run_with_unhandled_condition_aborts() {
    // CMP #0; CSEL(NE); CSEL(GT): the GT CSEL reads the re-test flags but
    // cannot be retargeted → the whole plan aborts.
    let insts = vec![
        MachInst::new(AArch64Opcode::CmpRR, vec![g32(0), g32(1)]),
        MachInst::new(AArch64Opcode::CSet, vec![g64(2), cc(CondCode::LT)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![g64(2), imm(0)]),
        MachInst::new(
            AArch64Opcode::Csel,
            vec![g32(4), g32(3), g32(0), cc(CondCode::NE)],
        ),
        MachInst::new(
            AArch64Opcode::Csel,
            vec![g32(5), g32(3), g32(0), cc(CondCode::GT)],
        ),
    ];
    let mut func = make_func(insts);
    let mut pass = SelectFlagFuse;
    assert!(!pass.run(&mut func));
    assert!(opcodes(&func).contains(&AArch64Opcode::CmpRI));
    assert_eq!(
        csel_conds(&func),
        vec![
            CondCode::NE.encoding() as i64,
            CondCode::GT.encoding() as i64
        ]
    );
}

#[test]
fn fcmp_sourced_cset_fuses() {
    // Float compares materialize the same CSET shape; the fusion is
    // condition-source agnostic.
    let insts = vec![
        MachInst::new(AArch64Opcode::Fcmp, vec![g64(10), g64(11)]),
        MachInst::new(AArch64Opcode::CSet, vec![g64(2), cc(CondCode::MI)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![g64(2), imm(0)]),
        MachInst::new(
            AArch64Opcode::Csel,
            vec![g32(4), g32(3), g32(0), cc(CondCode::NE)],
        ),
    ];
    let mut func = make_func(insts);
    let mut pass = SelectFlagFuse;
    assert!(pass.run(&mut func));
    assert_eq!(csel_conds(&func), vec![CondCode::MI.encoding() as i64]);
}

#[test]
fn idempotent() {
    let mut func = make_func(bsearch_shape());
    let mut pass = SelectFlagFuse;
    assert!(pass.run(&mut func));
    assert!(!pass.run(&mut func));
}

#[test]
fn provenance_merge_and_deletion_recorded() {
    use trust_cg_ir::{PassId, ProvenanceMap, ProvenanceStatus, TrustIrInstId};
    let mut func = make_func(bsearch_shape());
    let ids = func.block(BlockId(0)).insts.clone();
    let cset_id = ids[1];
    let cmp1_id = ids[3];
    let csel1_id = ids[4];

    let mut provenance = ProvenanceMap::new();
    provenance.record_lowering(TrustIrInstId(10), &[cset_id], PassId::new("isel"));
    provenance.record_lowering(TrustIrInstId(11), &[cmp1_id], PassId::new("isel"));
    provenance.record_lowering(TrustIrInstId(12), &[csel1_id], PassId::new("isel"));

    let mut pass = SelectFlagFuse;
    assert!(pass.run_with_provenance(&mut func, &mut provenance));

    let entry = provenance.get_entry(csel1_id).expect("fused csel entry");
    assert!(entry.trust_ir_origins.contains(&TrustIrInstId(11)));
    assert!(entry.trust_ir_origins.contains(&TrustIrInstId(12)));

    let cset_entry = provenance
        .get_entry(cset_id)
        .expect("deleted cset provenance");
    assert!(matches!(
        cset_entry.status,
        ProvenanceStatus::OptimizedAway { .. }
    ));
}
