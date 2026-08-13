// trust-cg-codegen/tests/x86_64_sse2_lane_encoding.rs
// Byte-exact x86-64 SSE2 lane/mask encoder tests.

use trust_cg_codegen::x86_64::{X86Encoder, X86InstOperands};
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs::{
    EAX, ECX, EDX, R8D, R9, R9D, R14, R14D, R15D, RAX, RCX, XMM0, XMM1, XMM2, XMM8, XMM9, XMM14,
    XMM15,
};

fn assert_bytes(name: &str, opcode: X86Opcode, ops: X86InstOperands, expected: &[u8]) {
    let mut enc = X86Encoder::new();
    enc.encode_instruction(opcode, &ops).unwrap();
    let bytes = enc.finish();
    assert_eq!(bytes.as_slice(), expected, "{name}");
}

#[test]
fn movd_gpr32_xmm_transfers_pin_rex_r_and_b_bits() {
    use X86Opcode::*;

    for (name, opcode, ops, expected) in [
        (
            "movd xmm0, eax",
            MovdToXmm,
            X86InstOperands::rr(XMM0, EAX),
            &[0x66, 0x0F, 0x6E, 0xC0][..],
        ),
        (
            "movd xmm8, ecx",
            MovdToXmm,
            X86InstOperands::rr(XMM8, ECX),
            &[0x66, 0x44, 0x0F, 0x6E, 0xC1],
        ),
        (
            "movd xmm2, r9d",
            MovdToXmm,
            X86InstOperands::rr(XMM2, R9D),
            &[0x66, 0x41, 0x0F, 0x6E, 0xD1],
        ),
        (
            "movd xmm15, r14d",
            MovdToXmm,
            X86InstOperands::rr(XMM15, R14D),
            &[0x66, 0x45, 0x0F, 0x6E, 0xFE],
        ),
        (
            "movd eax, xmm0",
            MovdFromXmm,
            X86InstOperands::rr(EAX, XMM0),
            &[0x66, 0x0F, 0x7E, 0xC0],
        ),
        (
            "movd ecx, xmm8",
            MovdFromXmm,
            X86InstOperands::rr(ECX, XMM8),
            &[0x66, 0x44, 0x0F, 0x7E, 0xC1],
        ),
        (
            "movd r9d, xmm2",
            MovdFromXmm,
            X86InstOperands::rr(R9D, XMM2),
            &[0x66, 0x41, 0x0F, 0x7E, 0xD1],
        ),
        (
            "movd r14d, xmm15",
            MovdFromXmm,
            X86InstOperands::rr(R14D, XMM15),
            &[0x66, 0x45, 0x0F, 0x7E, 0xFE],
        ),
    ] {
        assert_bytes(name, opcode, ops, expected);
    }
}

#[test]
fn movq_gpr64_xmm_transfers_pin_rex_w_r_and_b_bits() {
    use X86Opcode::*;

    for (name, opcode, ops, expected) in [
        (
            "movq xmm0, rax",
            MovqToXmm,
            X86InstOperands::rr(XMM0, RAX),
            &[0x66, 0x48, 0x0F, 0x6E, 0xC0][..],
        ),
        (
            "movq xmm8, rcx",
            MovqToXmm,
            X86InstOperands::rr(XMM8, RCX),
            &[0x66, 0x4C, 0x0F, 0x6E, 0xC1],
        ),
        (
            "movq xmm2, r9",
            MovqToXmm,
            X86InstOperands::rr(XMM2, R9),
            &[0x66, 0x49, 0x0F, 0x6E, 0xD1],
        ),
        (
            "movq xmm15, r14",
            MovqToXmm,
            X86InstOperands::rr(XMM15, R14),
            &[0x66, 0x4D, 0x0F, 0x6E, 0xFE],
        ),
        (
            "movq rax, xmm0",
            MovqFromXmm,
            X86InstOperands::rr(RAX, XMM0),
            &[0x66, 0x48, 0x0F, 0x7E, 0xC0],
        ),
        (
            "movq rcx, xmm8",
            MovqFromXmm,
            X86InstOperands::rr(RCX, XMM8),
            &[0x66, 0x4C, 0x0F, 0x7E, 0xC1],
        ),
        (
            "movq r9, xmm2",
            MovqFromXmm,
            X86InstOperands::rr(R9, XMM2),
            &[0x66, 0x49, 0x0F, 0x7E, 0xD1],
        ),
        (
            "movq r14, xmm15",
            MovqFromXmm,
            X86InstOperands::rr(R14, XMM15),
            &[0x66, 0x4D, 0x0F, 0x7E, 0xFE],
        ),
    ] {
        assert_bytes(name, opcode, ops, expected);
    }
}

#[test]
fn xmm_lane_shuffle_and_unpack_ops_pin_high_xmm_rex_bits() {
    for (mnemonic, opcode, opcode_byte) in [
        ("pxor", X86Opcode::Pxor, 0xEF),
        ("punpckldq", X86Opcode::Punpckldq, 0x62),
        ("punpcklqdq", X86Opcode::Punpcklqdq, 0x6C),
    ] {
        assert_bytes(
            &format!("{mnemonic} xmm0, xmm1"),
            opcode,
            X86InstOperands::rr(XMM0, XMM1),
            &[0x66, 0x0F, opcode_byte, 0xC1],
        );
        assert_bytes(
            &format!("{mnemonic} xmm8, xmm1"),
            opcode,
            X86InstOperands::rr(XMM8, XMM1),
            &[0x66, 0x44, 0x0F, opcode_byte, 0xC1],
        );
        assert_bytes(
            &format!("{mnemonic} xmm2, xmm9"),
            opcode,
            X86InstOperands::rr(XMM2, XMM9),
            &[0x66, 0x41, 0x0F, opcode_byte, 0xD1],
        );
        assert_bytes(
            &format!("{mnemonic} xmm15, xmm14"),
            opcode,
            X86InstOperands::rr(XMM15, XMM14),
            &[0x66, 0x45, 0x0F, opcode_byte, 0xFE],
        );
    }

    for (name, ops, expected) in [
        (
            "pshufd xmm0, xmm1, 0x1b",
            X86InstOperands::rri(XMM0, XMM1, 0x1B),
            &[0x66, 0x0F, 0x70, 0xC1, 0x1B][..],
        ),
        (
            "pshufd xmm8, xmm1, 0x4e",
            X86InstOperands::rri(XMM8, XMM1, 0x4E),
            &[0x66, 0x44, 0x0F, 0x70, 0xC1, 0x4E],
        ),
        (
            "pshufd xmm2, xmm9, 0xe4",
            X86InstOperands::rri(XMM2, XMM9, 0xE4),
            &[0x66, 0x41, 0x0F, 0x70, 0xD1, 0xE4],
        ),
        (
            "pshufd xmm15, xmm14, 0x00",
            X86InstOperands::rri(XMM15, XMM14, 0),
            &[0x66, 0x45, 0x0F, 0x70, 0xFE, 0x00],
        ),
    ] {
        assert_bytes(name, X86Opcode::Pshufd, ops, expected);
    }
}

#[test]
fn pmovmskb_gpr32_xmm_mask_extract_pins_rex_r_and_b_bits() {
    for (name, ops, expected) in [
        (
            "pmovmskb eax, xmm1",
            X86InstOperands::rr(EAX, XMM1),
            &[0x66, 0x0F, 0xD7, 0xC1][..],
        ),
        (
            "pmovmskb r8d, xmm1",
            X86InstOperands::rr(R8D, XMM1),
            &[0x66, 0x44, 0x0F, 0xD7, 0xC1],
        ),
        (
            "pmovmskb edx, xmm9",
            X86InstOperands::rr(EDX, XMM9),
            &[0x66, 0x41, 0x0F, 0xD7, 0xD1],
        ),
        (
            "pmovmskb r15d, xmm14",
            X86InstOperands::rr(R15D, XMM14),
            &[0x66, 0x45, 0x0F, 0xD7, 0xFE],
        ),
    ] {
        assert_bytes(name, X86Opcode::Pmovmskb, ops, expected);
    }
}
