use std::collections::HashMap;

use trust_cg_codegen::riscv::pipeline::{
    RiscVISelFunction, RiscVISelInst, RiscVISelOperand, RiscVProofGuardElimination,
};
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::riscv_ops::RiscVOpcode;
use trust_cg_ir::{
    DischargeStatus, DischargedEvidenceTable, GuardKind, GuardOperandRef, fingerprint_for_kind,
};
use trust_cg_lower::function::Signature;
use trust_cg_lower::instructions::Block;

#[test]
fn public_riscv_gate_api_cannot_turn_forged_evidence_into_authority() {
    let mut func = RiscVISelFunction::new(
        "forged_riscv".to_string(),
        Signature {
            params: vec![],
            returns: vec![],
        },
    );
    let entry = Block(0);
    func.ensure_block(entry);
    func.next_vreg = 2;
    func.push_inst(
        entry,
        RiscVISelInst::new(
            RiscVOpcode::TrapBoundsCheckExact,
            vec![
                RiscVISelOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                RiscVISelOperand::VReg(VReg::new(1, RegClass::Gpr64)),
                RiscVISelOperand::Imm(8),
            ],
        ),
    );

    let fp = fingerprint_for_kind(
        GuardKind::BoundsCheck,
        &[
            GuardOperandRef::Reg(0),
            GuardOperandRef::Reg(1),
            GuardOperandRef::Imm(8),
        ],
    );
    let mut evidence = DischargedEvidenceTable::new();
    evidence.insert(23, DischargeStatus::Certified, Some(0xD00D));
    let mut bindings = HashMap::new();
    bindings.insert(fp, (23, Some(0xD00D)));
    let mut pass = RiscVProofGuardElimination::new();
    pass.enable_kernel_gate(evidence, bindings);

    assert!(!pass.run_on_function(&mut func));
    assert_eq!(
        func.blocks[&entry]
            .insts
            .iter()
            .filter(|inst| inst.opcode == RiscVOpcode::TrapBoundsCheckExact)
            .count(),
        1
    );
    assert_eq!(pass.stats().guards_eliminated, 0);
}
