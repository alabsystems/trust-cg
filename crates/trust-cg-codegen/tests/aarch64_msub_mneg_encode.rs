use trust_cg_codegen::aarch64::encode_instruction;
use trust_cg_ir::regs::{X0, X1, X2, X9};
use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand};

fn preg(reg: trust_cg_ir::regs::PReg) -> MachOperand {
    MachOperand::PReg(reg)
}

#[test]
fn three_operand_msub_encodes_mneg_with_xzr_addend() {
    let inst = MachInst::new(AArch64Opcode::Msub, vec![preg(X0), preg(X1), preg(X2)]);

    let encoded = encode_instruction(&inst).expect("three-operand MSUB should encode");
    let expected = (1u32 << 31) | (0b11011 << 24) | (2 << 16) | (1 << 15) | (31 << 10) | (1 << 5);

    assert_eq!(encoded, expected);
}

#[test]
fn four_operand_msub_preserves_explicit_addend_register() {
    let inst = MachInst::new(
        AArch64Opcode::Msub,
        vec![preg(X0), preg(X1), preg(X2), preg(X9)],
    );

    let encoded = encode_instruction(&inst).expect("four-operand MSUB should encode");
    let expected = (1u32 << 31) | (0b11011 << 24) | (2 << 16) | (1 << 15) | (9 << 10) | (1 << 5);

    assert_eq!(encoded, expected);
}
