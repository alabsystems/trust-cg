// trust-cg-codegen/tests/x86_64_imm8_encoding.rs
// Targeted x86-64 code-size tests for ALU immediate encoding.

use trust_cg_codegen::x86_64::{X86Encoder, X86InstOperands};
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs::{R8, RAX};

fn encode(opcode: X86Opcode, ops: &X86InstOperands) -> Vec<u8> {
    let mut enc = X86Encoder::new();
    enc.encode_instruction(opcode, ops).unwrap();
    enc.finish()
}

#[test]
fn alu_ri_uses_imm8_form_when_sign_extended_value_matches() {
    let cases = [
        (X86Opcode::AddRI, RAX, 1, vec![0x48, 0x83, 0xC0, 0x01]),
        (X86Opcode::SubRI, RAX, 32, vec![0x48, 0x83, 0xE8, 0x20]),
        (X86Opcode::AndRI, RAX, -1, vec![0x48, 0x83, 0xE0, 0xFF]),
        (X86Opcode::OrRI, R8, 7, vec![0x49, 0x83, 0xC8, 0x07]),
        (X86Opcode::XorRI, RAX, -128, vec![0x48, 0x83, 0xF0, 0x80]),
        (X86Opcode::CmpRI, RAX, 127, vec![0x48, 0x83, 0xF8, 0x7F]),
    ];

    for (opcode, dst, imm, expected) in cases {
        assert_eq!(encode(opcode, &X86InstOperands::ri(dst, imm)), expected);
    }
}

#[test]
fn alu_ri_keeps_imm32_when_imm8_sign_extension_would_change_value() {
    assert_eq!(
        encode(X86Opcode::AddRI, &X86InstOperands::ri(RAX, 128)),
        vec![0x48, 0x81, 0xC0, 0x80, 0x00, 0x00, 0x00]
    );
    assert_eq!(
        encode(X86Opcode::AndRI, &X86InstOperands::ri(RAX, 255)),
        vec![0x48, 0x81, 0xE0, 0xFF, 0x00, 0x00, 0x00]
    );
    assert_eq!(
        encode(X86Opcode::CmpRI, &X86InstOperands::ri(RAX, -129)),
        vec![0x48, 0x81, 0xF8, 0x7F, 0xFF, 0xFF, 0xFF]
    );
}
