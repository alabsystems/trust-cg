// trust-cg-codegen - Extended-register addressing exact-byte pins
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Exact-byte pins for every LdrRO/StrRO extended-register variant the
// ext-addr fold emits (plus the UXTW forms for completeness), verified
// against the system assembler:
//
//   clang -c roenc.s -arch arm64 && objdump -d roenc.o     (2026-07-09)
//
// The packed 4th operand is `(option << 1) | S` with option: 010=UXTW,
// 011=LSL, 110=SXTW; S=1 shifts the index by the access size's log2.
//
// The prior FPR-collision P0 class (an FPR operand encoded through a
// GPR-only path reads/writes the wrong register bank) makes the FPR pins
// load-bearing: LDR S/D must set the V bit (0xBC.../0xFC...), never the
// integer 0xB8.../0xF8... forms.

use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_ir::regs::{
    D0, D7, PReg, S0, S31, W0, W1, W3, W26, W28, X1, X2, X3, X9, X10, X11, X27, X29, X30,
};
use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand};

fn preg(r: PReg) -> MachOperand {
    MachOperand::PReg(r)
}
fn imm(v: i64) -> MachOperand {
    MachOperand::Imm(v)
}

const SXTW_S1: i64 = (0b110 << 1) | 1;
const SXTW_S0: i64 = 0b110 << 1;
const UXTW_S1: i64 = (0b010 << 1) | 1;
const UXTW_S0: i64 = 0b010 << 1;
const LSL_S1: i64 = (0b011 << 1) | 1;
const LSL_S0: i64 = 0b011 << 1;

fn assert_pin(opcode: AArch64Opcode, ops: Vec<MachOperand>, expected: u32, asm: &str) {
    let inst = MachInst::new(opcode, ops);
    let enc = encode_instruction(&inst).unwrap_or_else(|e| panic!("{asm}: encode failed: {e:?}"));
    assert_eq!(
        enc, expected,
        "{asm}: got {enc:#010x}, want {expected:#010x}"
    );
}

#[test]
fn pin_ldr_w_sxtw_shifted() {
    // ldr w1, [x2, w3, sxtw #2] = b863d841
    assert_pin(
        AArch64Opcode::LdrRO,
        vec![preg(W1), preg(X2), preg(W3), imm(SXTW_S1)],
        0xb863d841,
        "ldr w1, [x2, w3, sxtw #2]",
    );
}

#[test]
fn pin_ldr_w_sxtw_unshifted() {
    // ldr w1, [x2, w3, sxtw] = b863c841
    assert_pin(
        AArch64Opcode::LdrRO,
        vec![preg(W1), preg(X2), preg(W3), imm(SXTW_S0)],
        0xb863c841,
        "ldr w1, [x2, w3, sxtw]",
    );
}

#[test]
fn pin_ldr_w_uxtw_shifted() {
    // ldr w1, [x2, w3, uxtw #2] = b8635841
    assert_pin(
        AArch64Opcode::LdrRO,
        vec![preg(W1), preg(X2), preg(W3), imm(UXTW_S1)],
        0xb8635841,
        "ldr w1, [x2, w3, uxtw #2]",
    );
}

#[test]
fn pin_ldr_w_uxtw_unshifted() {
    // ldr w1, [x2, w3, uxtw] = b8634841
    assert_pin(
        AArch64Opcode::LdrRO,
        vec![preg(W1), preg(X2), preg(W3), imm(UXTW_S0)],
        0xb8634841,
        "ldr w1, [x2, w3, uxtw]",
    );
}

#[test]
fn pin_ldr_w_high_regs() {
    // ldr w28, [x27, w26, sxtw #2] = b87adb7c
    assert_pin(
        AArch64Opcode::LdrRO,
        vec![preg(W28), preg(X27), preg(W26), imm(SXTW_S1)],
        0xb87adb7c,
        "ldr w28, [x27, w26, sxtw #2]",
    );
}

#[test]
fn pin_ldr_w_lsl_shifted() {
    // ldr w0, [x1, x2, lsl #2] = b8627820
    assert_pin(
        AArch64Opcode::LdrRO,
        vec![preg(W0), preg(X1), preg(X2), imm(LSL_S1)],
        0xb8627820,
        "ldr w0, [x1, x2, lsl #2]",
    );
}

#[test]
fn pin_ldr_w_plain_register_offset() {
    // ldr w0, [x1, x2] = b8626820 — the pre-existing 3-operand form.
    assert_pin(
        AArch64Opcode::LdrRO,
        vec![preg(W0), preg(X1), preg(X2)],
        0xb8626820,
        "ldr w0, [x1, x2]",
    );
}

#[test]
fn pin_ldr_x_sxtw_shifted() {
    // ldr x1, [x2, w3, sxtw #3] = f863d841
    assert_pin(
        AArch64Opcode::LdrRO,
        vec![preg(X1), preg(X2), preg(W3), imm(SXTW_S1)],
        0xf863d841,
        "ldr x1, [x2, w3, sxtw #3]",
    );
}

#[test]
fn pin_ldr_x_sxtw_unshifted() {
    // ldr x1, [x2, w3, sxtw] = f863c841
    assert_pin(
        AArch64Opcode::LdrRO,
        vec![preg(X1), preg(X2), preg(W3), imm(SXTW_S0)],
        0xf863c841,
        "ldr x1, [x2, w3, sxtw]",
    );
}

#[test]
fn pin_ldr_x_uxtw_shifted() {
    // ldr x1, [x2, w3, uxtw #3] = f8635841
    assert_pin(
        AArch64Opcode::LdrRO,
        vec![preg(X1), preg(X2), preg(W3), imm(UXTW_S1)],
        0xf8635841,
        "ldr x1, [x2, w3, uxtw #3]",
    );
}

#[test]
fn pin_ldr_x_lsl_shifted() {
    // ldr x9, [x10, x11, lsl #3] = f86b7949
    assert_pin(
        AArch64Opcode::LdrRO,
        vec![preg(X9), preg(X10), preg(X11), imm(LSL_S1)],
        0xf86b7949,
        "ldr x9, [x10, x11, lsl #3]",
    );
}

#[test]
fn pin_ldr_x_high_regs() {
    // ldr x30, [x29, w28, sxtw #3] = f87cdbbe
    assert_pin(
        AArch64Opcode::LdrRO,
        vec![preg(X30), preg(X29), preg(W28), imm(SXTW_S1)],
        0xf87cdbbe,
        "ldr x30, [x29, w28, sxtw #3]",
    );
}

#[test]
fn pin_str_w_sxtw_shifted() {
    // str w1, [x2, w3, sxtw #2] = b823d841
    assert_pin(
        AArch64Opcode::StrRO,
        vec![preg(W1), preg(X2), preg(W3), imm(SXTW_S1)],
        0xb823d841,
        "str w1, [x2, w3, sxtw #2]",
    );
}

#[test]
fn pin_str_w_sxtw_unshifted() {
    // str w1, [x2, w3, sxtw] = b823c841
    assert_pin(
        AArch64Opcode::StrRO,
        vec![preg(W1), preg(X2), preg(W3), imm(SXTW_S0)],
        0xb823c841,
        "str w1, [x2, w3, sxtw]",
    );
}

#[test]
fn pin_str_w_uxtw_shifted() {
    // str w1, [x2, w3, uxtw #2] = b8235841
    assert_pin(
        AArch64Opcode::StrRO,
        vec![preg(W1), preg(X2), preg(W3), imm(UXTW_S1)],
        0xb8235841,
        "str w1, [x2, w3, uxtw #2]",
    );
}

#[test]
fn pin_str_w_high_regs() {
    // str w28, [x27, w26, sxtw #2] = b83adb7c
    assert_pin(
        AArch64Opcode::StrRO,
        vec![preg(W28), preg(X27), preg(W26), imm(SXTW_S1)],
        0xb83adb7c,
        "str w28, [x27, w26, sxtw #2]",
    );
}

#[test]
fn pin_str_w_lsl_shifted() {
    // str w0, [x1, x2, lsl #2] = b8227820
    assert_pin(
        AArch64Opcode::StrRO,
        vec![preg(W0), preg(X1), preg(X2), imm(LSL_S1)],
        0xb8227820,
        "str w0, [x1, x2, lsl #2]",
    );
}

#[test]
fn pin_str_x_sxtw_shifted() {
    // str x1, [x2, w3, sxtw #3] = f823d841
    assert_pin(
        AArch64Opcode::StrRO,
        vec![preg(X1), preg(X2), preg(W3), imm(SXTW_S1)],
        0xf823d841,
        "str x1, [x2, w3, sxtw #3]",
    );
}

#[test]
fn pin_str_x_lsl_shifted() {
    // str x9, [x10, x11, lsl #3] = f82b7949
    assert_pin(
        AArch64Opcode::StrRO,
        vec![preg(X9), preg(X10), preg(X11), imm(LSL_S1)],
        0xf82b7949,
        "str x9, [x10, x11, lsl #3]",
    );
}

#[test]
fn pin_ldr_s_sxtw_shifted() {
    // ldr s0, [x2, w3, sxtw #2] = bc63d840 — V bit set (FPR form).
    assert_pin(
        AArch64Opcode::LdrRO,
        vec![preg(S0), preg(X2), preg(W3), imm(SXTW_S1)],
        0xbc63d840,
        "ldr s0, [x2, w3, sxtw #2]",
    );
}

#[test]
fn pin_ldr_s_high_regs() {
    // ldr s31, [x27, w26, sxtw #2] = bc7adb7f
    assert_pin(
        AArch64Opcode::LdrRO,
        vec![preg(S31), preg(X27), preg(W26), imm(SXTW_S1)],
        0xbc7adb7f,
        "ldr s31, [x27, w26, sxtw #2]",
    );
}

#[test]
fn pin_ldr_d_sxtw_shifted() {
    // ldr d0, [x2, w3, sxtw #3] = fc63d840
    assert_pin(
        AArch64Opcode::LdrRO,
        vec![preg(D0), preg(X2), preg(W3), imm(SXTW_S1)],
        0xfc63d840,
        "ldr d0, [x2, w3, sxtw #3]",
    );
}

#[test]
fn pin_ldr_d_lsl_shifted() {
    // ldr d7, [x9, x11, lsl #3] = fc6b7927
    assert_pin(
        AArch64Opcode::LdrRO,
        vec![preg(D7), preg(X9), preg(X11), imm(LSL_S1)],
        0xfc6b7927,
        "ldr d7, [x9, x11, lsl #3]",
    );
}

#[test]
fn pin_str_s_sxtw_shifted() {
    // str s0, [x2, w3, sxtw #2] = bc23d840
    assert_pin(
        AArch64Opcode::StrRO,
        vec![preg(S0), preg(X2), preg(W3), imm(SXTW_S1)],
        0xbc23d840,
        "str s0, [x2, w3, sxtw #2]",
    );
}

#[test]
fn pin_str_d_sxtw_shifted() {
    // str d0, [x2, w3, sxtw #3] = fc23d840
    assert_pin(
        AArch64Opcode::StrRO,
        vec![preg(D0), preg(X2), preg(W3), imm(SXTW_S1)],
        0xfc23d840,
        "str d0, [x2, w3, sxtw #3]",
    );
}

// ===========================================================================
// Narrow register-offset loads (LDRB / LDRH) — the ext_addr byte/half gather
// fold. Verified against the system assembler:
//
//   clang -c roenc_narrow.s -arch arm64 && objdump -d roenc_narrow.o (2026-07-11)
//
// Byte accesses use S=0 (log2(1)=0, so a shift is a no-op — the canonical
// form). Halfword accesses use S=1 to shift the index by log2(2)=1. The
// access WIDTH is fixed by the OPCODE (size=00 byte / 01 half), NOT the
// transfer class (always a W register): the encoded 0x38.../0x78... prefixes
// are load-bearing — an integer full-width 0xB8... would read 4 bytes.

#[test]
fn pin_ldrb_w_sxtw() {
    // ldrb w1, [x2, w3, sxtw] = 3863c841
    assert_pin(
        AArch64Opcode::LdrbRO,
        vec![preg(W1), preg(X2), preg(W3), imm(SXTW_S0)],
        0x3863c841,
        "ldrb w1, [x2, w3, sxtw]",
    );
}

#[test]
fn pin_ldrb_w_uxtw() {
    // ldrb w1, [x2, w3, uxtw] = 38634841
    assert_pin(
        AArch64Opcode::LdrbRO,
        vec![preg(W1), preg(X2), preg(W3), imm(UXTW_S0)],
        0x38634841,
        "ldrb w1, [x2, w3, uxtw]",
    );
}

#[test]
fn pin_ldrb_w_high_regs_sxtw() {
    // ldrb w28, [x27, w26, sxtw] = 387acb7c
    assert_pin(
        AArch64Opcode::LdrbRO,
        vec![preg(W28), preg(X27), preg(W26), imm(SXTW_S0)],
        0x387acb7c,
        "ldrb w28, [x27, w26, sxtw]",
    );
}

#[test]
fn pin_ldrb_w_high_regs_uxtw() {
    // ldrb w28, [x27, w26, uxtw] = 387a4b7c
    assert_pin(
        AArch64Opcode::LdrbRO,
        vec![preg(W28), preg(X27), preg(W26), imm(UXTW_S0)],
        0x387a4b7c,
        "ldrb w28, [x27, w26, uxtw]",
    );
}

#[test]
fn pin_ldrb_w_lsl_plain() {
    // ldrb w1, [x2, x3] = 38636841 — LSL, S=0 (64-bit index, no extend).
    assert_pin(
        AArch64Opcode::LdrbRO,
        vec![preg(W1), preg(X2), preg(X3), imm(LSL_S0)],
        0x38636841,
        "ldrb w1, [x2, x3]",
    );
}

#[test]
fn pin_ldrh_w_sxtw_shifted() {
    // ldrh w1, [x2, w3, sxtw #1] = 7863d841
    assert_pin(
        AArch64Opcode::LdrhRO,
        vec![preg(W1), preg(X2), preg(W3), imm(SXTW_S1)],
        0x7863d841,
        "ldrh w1, [x2, w3, sxtw #1]",
    );
}

#[test]
fn pin_ldrh_w_uxtw_shifted() {
    // ldrh w1, [x2, w3, uxtw #1] = 78635841
    assert_pin(
        AArch64Opcode::LdrhRO,
        vec![preg(W1), preg(X2), preg(W3), imm(UXTW_S1)],
        0x78635841,
        "ldrh w1, [x2, w3, uxtw #1]",
    );
}

#[test]
fn pin_ldrh_w_sxtw_unshifted() {
    // ldrh w1, [x2, w3, sxtw] = 7863c841 — S=0 (byte-step index into a
    // halfword array is unusual, but the encoding must be exact).
    assert_pin(
        AArch64Opcode::LdrhRO,
        vec![preg(W1), preg(X2), preg(W3), imm(SXTW_S0)],
        0x7863c841,
        "ldrh w1, [x2, w3, sxtw]",
    );
}

#[test]
fn pin_ldrh_w_high_regs_sxtw_shifted() {
    // ldrh w28, [x27, w26, sxtw #1] = 787adb7c
    assert_pin(
        AArch64Opcode::LdrhRO,
        vec![preg(W28), preg(X27), preg(W26), imm(SXTW_S1)],
        0x787adb7c,
        "ldrh w28, [x27, w26, sxtw #1]",
    );
}

#[test]
fn pin_ldrh_w_lsl_shifted() {
    // ldrh w0, [x1, x2, lsl #1] = 78627820
    assert_pin(
        AArch64Opcode::LdrhRO,
        vec![preg(W0), preg(X1), preg(X2), imm(LSL_S1)],
        0x78627820,
        "ldrh w0, [x1, x2, lsl #1]",
    );
}
