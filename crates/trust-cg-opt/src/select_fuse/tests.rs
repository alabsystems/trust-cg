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

/// One block holding `insts` and no terminator (the caller adds its tail).
fn make_open_func(insts: Vec<MachInst>) -> MachFunction {
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

/// One block holding `insts`, ended by `RET`: NZCV is dead at its exit.
fn make_func(insts: Vec<MachInst>) -> MachFunction {
    let mut func = make_open_func(insts);
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(func.entry, ret);
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
            AArch64Opcode::Ret,
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

/// The loaded-bool shape the AArch64 selector emits (`LDRB; TST #0xFF; CSET
/// NE`), with `barrier` between the CSET and the select's `CMP b, #0` re-test.
fn loaded_bool_select_across(barrier: MachInst) -> Vec<MachInst> {
    vec![
        MachInst::new(AArch64Opcode::Tst, vec![g64(3), imm(0xff)]),
        MachInst::new(AArch64Opcode::CSet, vec![g64(2), cc(CondCode::NE)]),
        barrier,
        MachInst::new(AArch64Opcode::CmpRI, vec![g64(2), imm(0)]),
        MachInst::new(
            AArch64Opcode::Csel,
            vec![g64(5), g64(0), g64(1), cc(CondCode::NE)],
        ),
    ]
}

/// A call, an indirect call or a trap carrier (expanded after this pass into
/// its own compare and branch) leaves NZCV undefined. A re-test past one is
/// not fused to the CSET's flags: the CSEL would read whatever the callee or
/// the guard left.
#[test]
fn a_call_or_trap_carrier_between_cset_and_retest_blocks_the_fuse() {
    for barrier in [
        MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("g".to_string())],
        ),
        MachInst::new(AArch64Opcode::Blr, vec![g64(9)]),
        MachInst::new(AArch64Opcode::TrapOverflowExact, vec![]),
        MachInst::new(AArch64Opcode::TrapBoundsCheckExact, vec![]),
    ] {
        let opcode = barrier.opcode;
        let mut func = make_func(loaded_bool_select_across(barrier));
        let before = opcodes(&func);
        assert!(!SelectFlagFuse.run(&mut func), "{opcode:?}");
        assert_eq!(opcodes(&func), before, "{opcode:?}");
        assert_eq!(
            csel_conds(&func),
            vec![CondCode::NE.encoding() as i64],
            "{opcode:?}"
        );
    }
}

/// A re-test fused BEFORE a call is still fused: the call only ends the scan.
#[test]
fn a_retest_before_a_call_still_fuses() {
    let mut func = make_func(vec![
        MachInst::new(AArch64Opcode::CmpRR, vec![g64(0), g64(1)]),
        MachInst::new(AArch64Opcode::CSet, vec![g64(2), cc(CondCode::LT)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![g64(2), imm(0)]),
        MachInst::new(
            AArch64Opcode::Csel,
            vec![g64(5), g64(0), g64(1), cc(CondCode::NE)],
        ),
        MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol("g".to_string())],
        ),
    ]);
    assert!(SelectFlagFuse.run(&mut func));
    assert_eq!(
        opcodes(&func),
        vec![
            AArch64Opcode::CmpRR,
            AArch64Opcode::Csel,
            AArch64Opcode::Bl,
            AArch64Opcode::Ret
        ]
    );
    assert_eq!(csel_conds(&func), vec![CondCode::LT.encoding() as i64]);
}

/// An instruction that both reads and writes NZCV (`ADCS` reads C) after a
/// planned deletion would read the CSET's flags instead of the deleted
/// re-test's, so the plan is abandoned.
#[test]
fn a_flag_reading_writer_after_a_planned_deletion_aborts() {
    let mut func = make_func(vec![
        MachInst::new(AArch64Opcode::CmpRR, vec![g64(0), g64(1)]),
        MachInst::new(AArch64Opcode::CSet, vec![g64(2), cc(CondCode::LT)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![g64(2), imm(0)]),
        MachInst::new(
            AArch64Opcode::Csel,
            vec![g64(5), g64(0), g64(1), cc(CondCode::NE)],
        ),
        MachInst::new(AArch64Opcode::Adcs, vec![g64(6), g64(0), g64(1)]),
    ]);
    let before = opcodes(&func);
    assert!(!SelectFlagFuse.run(&mut func));
    assert_eq!(opcodes(&func), before);
}

/// Block A: `CMP x,y; CSET b,LT; CMP b,#0; CSEL r,p,q,NE; <tail>`, and a
/// successor BB (A its only predecessor) whose `CSEL v,s,t,NE` begins with
/// `bb_head`. A's other successor only returns. Returns (func, bb).
fn cross_block_select(tail: Vec<MachInst>, bb_head: Vec<MachInst>) -> (MachFunction, BlockId) {
    let mut func = make_open_func(vec![
        MachInst::new(AArch64Opcode::CmpRR, vec![g64(0), g64(1)]),
        MachInst::new(AArch64Opcode::CSet, vec![g64(2), cc(CondCode::LT)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![g64(2), imm(0)]),
        MachInst::new(
            AArch64Opcode::Csel,
            vec![g64(3), g64(4), g64(5), cc(CondCode::NE)],
        ),
    ]);
    let a = func.entry;
    let bb = func.create_block();
    let ret = func.create_block();
    for inst in tail {
        let id = func.push_inst(inst);
        func.append_inst(a, id);
    }
    let body = bb_head.into_iter().chain([
        MachInst::new(
            AArch64Opcode::Csel,
            vec![g64(6), g64(7), g64(8), cc(CondCode::NE)],
        ),
        MachInst::new(AArch64Opcode::Ret, vec![]),
    ]);
    for inst in body {
        let id = func.push_inst(inst);
        func.append_inst(bb, id);
    }
    let id = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(ret, id);
    func.add_edge(a, ret);
    func.add_edge(a, bb);
    (func, bb)
}

/// The tail cmp-branch-fusion leaves in A: `CBZ z, RET; B BB`.
fn cbz_tail(ret: BlockId, bb: BlockId) -> Vec<MachInst> {
    vec![
        MachInst::new(AArch64Opcode::Cbz, vec![g64(9), MachOperand::Block(ret)]),
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(bb)]),
    ]
}

/// cmp-branch-fusion's cross-block elimination leaves a successor reading
/// its single predecessor's live-out NZCV. A re-test whose flags reach such
/// a successor is not deleted: BB's CSEL would read `CMP x,y` instead of
/// `CMP b,#0`.
#[test]
fn a_retest_whose_flags_a_successor_reads_is_kept() {
    let (mut func, _) = cross_block_select(cbz_tail(BlockId(2), BlockId(1)), vec![]);
    let before = opcodes(&func);
    assert!(!SelectFlagFuse.run(&mut func));
    assert_eq!(opcodes(&func), before);
}

/// The same shape with BB writing its own flags first still fuses A.
#[test]
fn a_retest_still_fuses_when_every_successor_writes_flags_first() {
    let (mut func, _) = cross_block_select(
        cbz_tail(BlockId(2), BlockId(1)),
        vec![MachInst::new(AArch64Opcode::CmpRI, vec![g64(2), imm(0)])],
    );
    assert!(SelectFlagFuse.run(&mut func));
    assert!(!opcodes(&func).contains(&AArch64Opcode::CmpRI));
    assert_eq!(csel_conds(&func)[0], CondCode::LT.encoding() as i64);
}

/// The pass order the O2/O3 pipelines run: cmp-branch-fusion turns A's
/// `CMP z,#0; B.EQ` into `CBZ` and deletes BB's identical `CMP b,#0`, so BB
/// reads A's live-out flags; select-fuse must then keep A's `CMP b,#0`.
#[test]
fn select_fuse_after_cross_block_compare_elimination_keeps_the_shared_retest() {
    let (mut func, bb) = cross_block_select(
        vec![
            MachInst::new(AArch64Opcode::CmpRI, vec![g64(9), imm(0)]),
            MachInst::new(
                AArch64Opcode::BCond,
                vec![cc(CondCode::EQ), MachOperand::Block(BlockId(2))],
            ),
            MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(BlockId(1))]),
        ],
        vec![MachInst::new(AArch64Opcode::CmpRI, vec![g64(2), imm(0)])],
    );
    let fused =
        crate::env_lock::with_env_overrides_removed(&["TCG_NO_CROSS_BLOCK_CMP_ELIM"], || {
            crate::cmp_branch_fusion::CmpBranchFusion.run(&mut func)
        });
    assert!(fused);
    assert!(
        !func
            .block(bb)
            .insts
            .iter()
            .any(|&id| func.inst(id).opcode == AArch64Opcode::CmpRI),
        "precondition: BB's re-test was eliminated across the block boundary"
    );
    SelectFlagFuse.run(&mut func);
    let a = func.block(func.entry).insts.clone();
    let last_writer = a
        .iter()
        .rev()
        .map(|&id| func.inst(id))
        .find(|inst| crate::effects::writes_flags(inst.opcode))
        .expect("A keeps a flag writer");
    assert!(
        is_cmp_zero_of(last_writer, VReg::new(2, RegClass::Gpr64)),
        "BB's CSEL must still read `CMP b, #0`, got {:?}",
        last_writer.opcode
    );
}

// A backedge must preserve flags read at the origin's head.
fn select_loop_with_origin_reader(head_kills_first: bool) -> (MachFunction, BlockId) {
    let mut func = make_open_func(vec![MachInst::new(
        AArch64Opcode::CmpRI,
        vec![g64(0), imm(0)],
    )]);
    let entry = func.entry;
    let header = func.create_block();
    let exit = func.create_block();
    let branch = func.push_inst(MachInst::new(
        AArch64Opcode::B,
        vec![MachOperand::Block(header)],
    ));
    func.append_inst(entry, branch);
    func.add_edge(entry, header);
    let mut body = vec![
        // The incoming NZCV is observable before any local flag writer.
        MachInst::new(
            AArch64Opcode::Csel,
            vec![g64(6), g64(4), g64(5), cc(CondCode::NE)],
        ),
        MachInst::new(AArch64Opcode::StrRI, vec![g64(6), g64(10), imm(0)]),
        MachInst::new(AArch64Opcode::CmpRR, vec![g64(0), g64(1)]),
        MachInst::new(AArch64Opcode::CSet, vec![g64(2), cc(CondCode::LT)]),
        MachInst::new(AArch64Opcode::CmpRI, vec![g64(2), imm(0)]),
        MachInst::new(
            AArch64Opcode::Csel,
            vec![g64(3), g64(4), g64(5), cc(CondCode::NE)],
        ),
        MachInst::new(AArch64Opcode::StrRI, vec![g64(3), g64(10), imm(8)]),
        // Counter-based tail does not read/write NZCV; both edges reachable.
        MachInst::new(AArch64Opcode::SubRI, vec![g64(9), g64(9), imm(1)]),
        MachInst::new(AArch64Opcode::Cbz, vec![g64(9), MachOperand::Block(exit)]),
        MachInst::new(AArch64Opcode::B, vec![MachOperand::Block(header)]),
    ];
    if head_kills_first {
        body.insert(0, MachInst::new(AArch64Opcode::CmpRI, vec![g64(0), imm(0)]));
    }
    for inst in body {
        let id = func.push_inst(inst);
        func.append_inst(header, id);
    }
    func.add_edge(header, exit);
    func.add_edge(header, header);
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    func.append_inst(exit, ret);
    (func, header)
}

#[test]
fn a_retest_whose_flags_reach_its_origin_head_reader_is_kept() {
    let (mut func, header) = select_loop_with_origin_reader(false);
    let before = func.block(header).insts.clone();
    assert!(!SelectFlagFuse.run(&mut func));
    assert_eq!(func.block(header).insts, before);
}

#[test]
fn a_retest_still_fuses_when_its_origin_head_kills_before_reading() {
    let (mut func, header) = select_loop_with_origin_reader(true);
    assert!(SelectFlagFuse.run(&mut func));
    let insts: Vec<_> = func
        .block(header)
        .insts
        .iter()
        .map(|&id| func.inst(id))
        .collect();
    assert!(
        !insts
            .iter()
            .any(|inst| is_cmp_zero_of(inst, VReg::new(2, RegClass::Gpr64)))
    );
    assert!(!insts.iter().any(|inst| inst.opcode == AArch64Opcode::CSet));
    let conditions: Vec<_> = insts
        .iter()
        .filter(|inst| inst.opcode == AArch64Opcode::Csel)
        .map(|inst| inst.operands[3].as_imm().unwrap())
        .collect();
    assert_eq!(
        conditions,
        vec![
            CondCode::NE.encoding() as i64,
            CondCode::LT.encoding() as i64
        ]
    );
}

#[test]
fn shared_nzcv_walk_checks_origin_head_on_a_backedge() {
    // The exact shared effects API called by both select and cmp-branch.
    for (head_kills_first, expected_dead) in [(false, false), (true, true)] {
        let (func, header) = select_loop_with_origin_reader(head_kills_first);
        let tail = func.block(header).insts.len() - 1;
        assert_eq!(
            crate::effects::nzcv_dead_after_branch(
                &func,
                header,
                tail,
                &crate::fast_hash::FxHashSet::default()
            ),
            expected_dead,
            "head_kills_first={head_kills_first}"
        );
    }
}
