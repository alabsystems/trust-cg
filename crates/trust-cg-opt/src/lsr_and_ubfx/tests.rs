use super::*;
use trust_cg_ir::{
    BlockId, PassId, ProofAnnotation, ProvenanceMap, Signature, SourceLoc, TrustIrInstId,
};

fn reg(id: u32, class: RegClass) -> MachOperand {
    MachOperand::VReg(VReg::new(id, class))
}

fn imm(value: i64) -> MachOperand {
    MachOperand::Imm(value)
}

fn func_with(insts: Vec<MachInst>) -> (MachFunction, BlockId) {
    let mut func = MachFunction::new("lsr_and_ubfx_test".into(), Signature::new(vec![], vec![]));
    let entry = func.entry;
    for inst in insts {
        let id = func.push_inst(inst);
        func.append_inst(entry, id);
    }
    (func, entry)
}

fn sequence(class: RegClass, shift: i64, mask: i64) -> (MachFunction, BlockId) {
    func_with(vec![
        MachInst::new(
            AArch64Opcode::LsrRI,
            vec![reg(2, class), reg(0, class), imm(shift)],
        ),
        MachInst::new(
            AArch64Opcode::AndRI,
            vec![reg(3, class), reg(2, class), imm(mask)],
        ),
        MachInst::new(AArch64Opcode::CmpRR, vec![reg(3, class), reg(1, class)]),
    ])
}

fn ubfm(func: &MachFunction) -> Option<&MachInst> {
    func.block_order.iter().find_map(|&block| {
        func.block(block).insts.iter().find_map(|&id| {
            let inst = func.inst(id);
            (inst.opcode == AArch64Opcode::Ubfm).then_some(inst)
        })
    })
}

#[test]
fn fuses_w_and_x_forms_with_exact_immr_imms() {
    for (class, shift, mask, expected_imms) in [
        (RegClass::Gpr32, 4, 0xf, 7),
        (RegClass::Gpr64, 8, 0xf, 11),
        (RegClass::Gpr64, 0, 1, 0),
        (RegClass::Gpr64, 63, 1, 63),
    ] {
        let (mut func, entry) = sequence(class, shift, mask);
        assert!(LsrAndUbfx.run(&mut func));
        assert_eq!(
            func.inst(func.block(entry).insts[0]).opcode,
            AArch64Opcode::Nop
        );
        let fused = ubfm(&func).expect("expected UBFM");
        assert_eq!(fused.operands[0], reg(3, class));
        assert_eq!(fused.operands[1], reg(0, class));
        assert_eq!(fused.operands[2], imm(shift));
        assert_eq!(fused.operands[3], imm(expected_imms));
        assert!(!LsrAndUbfx.run(&mut func), "the pass must be idempotent");
    }
}

#[test]
fn preserves_consumer_proof_and_source_location() {
    let class = RegClass::Gpr64;
    let (mut func, entry) = func_with(vec![
        MachInst::new(
            AArch64Opcode::LsrRI,
            vec![reg(2, class), reg(0, class), imm(8)],
        ),
        MachInst::new(
            AArch64Opcode::AndRI,
            vec![reg(3, class), reg(2, class), imm(0xf)],
        )
        .with_proof(ProofAnnotation::Pure)
        .with_source_loc(SourceLoc {
            file: 4,
            line: 12,
            col: 9,
        }),
        MachInst::new(AArch64Opcode::CmpRR, vec![reg(3, class), reg(1, class)]),
    ]);
    assert!(LsrAndUbfx.run(&mut func));
    let fused = func.inst(func.block(entry).insts[1]);
    assert_eq!(fused.proof, Some(ProofAnnotation::Pure));
    let loc = fused.source_loc.expect("source location must survive");
    assert_eq!((loc.file, loc.line, loc.col), (4, 12, 9));
}

#[test]
fn rejects_non_low_masks_and_fields_past_register_end() {
    for (class, shift, mask) in [
        (RegClass::Gpr64, 4, 0),
        (RegClass::Gpr64, 4, 0b1011),
        (RegClass::Gpr64, 4, 0xf0),
        (RegClass::Gpr64, 60, 0xff),
        (RegClass::Gpr64, -1, 0xf),
        (RegClass::Gpr32, 31, 0x3),
    ] {
        let (mut func, _) = sequence(class, shift, mask);
        assert!(
            !LsrAndUbfx.run(&mut func),
            "unexpected fusion for k={shift}, mask={mask:#x}"
        );
        assert!(ubfm(&func).is_none());
    }
}

#[test]
fn rejects_mixed_width_and_redefinitions() {
    let (mut mixed, _) = func_with(vec![
        MachInst::new(
            AArch64Opcode::LsrRI,
            vec![reg(2, RegClass::Gpr64), reg(0, RegClass::Gpr64), imm(8)],
        ),
        MachInst::new(
            AArch64Opcode::AndRI,
            vec![reg(3, RegClass::Gpr32), reg(2, RegClass::Gpr64), imm(0xf)],
        ),
    ]);
    assert!(!LsrAndUbfx.run(&mut mixed));

    let class = RegClass::Gpr64;
    let (mut source_redefined, _) = func_with(vec![
        MachInst::new(
            AArch64Opcode::LsrRI,
            vec![reg(2, class), reg(0, class), imm(8)],
        ),
        MachInst::new(
            AArch64Opcode::AddRI,
            vec![reg(0, class), reg(0, class), imm(1)],
        ),
        MachInst::new(
            AArch64Opcode::AndRI,
            vec![reg(3, class), reg(2, class), imm(0xf)],
        ),
    ]);
    assert!(!LsrAndUbfx.run(&mut source_redefined));

    let (mut temp_redefined, _) = func_with(vec![
        MachInst::new(
            AArch64Opcode::LsrRI,
            vec![reg(2, class), reg(0, class), imm(8)],
        ),
        MachInst::new(
            AArch64Opcode::AddRI,
            vec![reg(2, class), reg(1, class), imm(1)],
        ),
        MachInst::new(
            AArch64Opcode::AndRI,
            vec![reg(3, class), reg(2, class), imm(0xf)],
        ),
    ]);
    assert!(!LsrAndUbfx.run(&mut temp_redefined));
}

#[test]
fn tied_def_use_is_counted_as_an_extra_reader() {
    let class = RegClass::Gpr64;
    let (mut func, _) = func_with(vec![
        MachInst::new(
            AArch64Opcode::LsrRI,
            vec![reg(2, class), reg(0, class), imm(8)],
        ),
        MachInst::new(
            AArch64Opcode::AndRI,
            vec![reg(3, class), reg(2, class), imm(0xf)],
        ),
        // MOVK reads and writes operand zero. A naive skip-operand-zero scan
        // would miss this reader and incorrectly delete the LSR.
        MachInst::new(
            AArch64Opcode::Movk,
            vec![reg(2, class), imm(0x1234), imm(0)],
        ),
        MachInst::new(AArch64Opcode::CmpRR, vec![reg(3, class), reg(2, class)]),
    ]);
    assert!(!LsrAndUbfx.run(&mut func));
    assert!(ubfm(&func).is_none());
}

#[test]
fn records_both_origins_on_the_merged_instruction() {
    let (mut func, entry) = sequence(RegClass::Gpr64, 8, 0xf);
    let ids = func.block(entry).insts.clone();
    let mut provenance = ProvenanceMap::new();
    provenance.record_lowering(TrustIrInstId(10), &[ids[0]], PassId::new("isel"));
    provenance.record_lowering(TrustIrInstId(11), &[ids[1]], PassId::new("isel"));

    assert!(LsrAndUbfx.run_with_provenance(&mut func, &mut provenance));
    let fused = provenance.get_entry(ids[1]).expect("fused provenance");
    assert!(fused.trust_ir_origins.contains(&TrustIrInstId(10)));
    assert!(fused.trust_ir_origins.contains(&TrustIrInstId(11)));
    assert!(
        provenance.get_entry(ids[0]).is_none(),
        "record_merge transfers the consumed producer entry to the survivor"
    );
}

#[test]
fn low_run_width_uses_the_selected_register_view() {
    assert_eq!(low_run_width(0xf, 64), Some(4));
    assert_eq!(low_run_width(1, 64), Some(1));
    assert_eq!(low_run_width(-1, 64), Some(64));
    assert_eq!(low_run_width(-1, 32), Some(32));
    assert_eq!(low_run_width(0, 64), None);
    assert_eq!(low_run_width(0b1011, 64), None);
    assert_eq!(low_run_width(0xf0, 64), None);
}
