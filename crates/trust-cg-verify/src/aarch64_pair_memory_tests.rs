// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use trust_cg_ir::regs::PReg;

fn reg(encoding: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(encoding))
}

fn inst(opcode: Op, operands: Vec<MachOperand>) -> MachInst {
    MachInst::new(opcode, operands)
}

// Independent literal instruction diagrams, not encoder output or the checked
// descriptor's own interpretation. Existing codegen tests retain the exhaustive
// register-field/alias/hole corpus; this table pins the new public view.
fn rows() -> [(Op, u16, PairMemoryFormat, PairMemoryMode, bool, u32); 22] {
    use PairMemoryFormat::*;
    use PairMemoryMode::*;
    [
        (Op::StpRI, 32, W32, SignedOffset, false, 0x2900_0000),
        (Op::StpRI, 0, X64, SignedOffset, false, 0xa900_0000),
        (Op::StpRI, 128, S32, SignedOffset, false, 0x2d00_0000),
        (Op::StpRI, 96, D64, SignedOffset, false, 0x6d00_0000),
        (Op::StpRI, 64, Q128, SignedOffset, false, 0xad00_0000),
        (Op::LdpRI, 32, W32, SignedOffset, true, 0x2940_0000),
        (Op::LdpRI, 0, X64, SignedOffset, true, 0xa940_0000),
        (Op::LdpRI, 128, S32, SignedOffset, true, 0x2d40_0000),
        (Op::LdpRI, 96, D64, SignedOffset, true, 0x6d40_0000),
        (Op::LdpRI, 64, Q128, SignedOffset, true, 0xad40_0000),
        (Op::StpPreIndex, 32, W32, PreIndex, false, 0x2980_0000),
        (Op::StpPreIndex, 0, X64, PreIndex, false, 0xa980_0000),
        (Op::StpPreIndex, 128, S32, PreIndex, false, 0x2d80_0000),
        (Op::StpPreIndex, 96, D64, PreIndex, false, 0x6d80_0000),
        (Op::StpPreIndex, 64, Q128, PreIndex, false, 0xad80_0000),
        (Op::LdpPostIndex, 32, W32, PostIndex, true, 0x28c0_0000),
        (Op::LdpPostIndex, 0, X64, PostIndex, true, 0xa8c0_0000),
        (Op::LdpPostIndex, 128, S32, PostIndex, true, 0x2cc0_0000),
        (Op::LdpPostIndex, 96, D64, PostIndex, true, 0x6cc0_0000),
        (Op::LdpPostIndex, 64, Q128, PostIndex, true, 0xacc0_0000),
        (Op::NeonLdpQPost, 64, Q128, PostIndex, true, 0xacc0_0000),
        (Op::NeonStpQPost, 64, Q128, PostIndex, false, 0xac80_0000),
    ]
}

fn word(base: u32, scaled: i64, rt: u8, rt2: u8, rn: u8) -> u32 {
    base | (((scaled as u32) & 127) << 15)
        | (u32::from(rt2) << 10)
        | (u32::from(rn) << 5)
        | u32::from(rt)
}

#[test]
fn checked_pair_views_all_22_forms_and_every_signed_offset() {
    let mut count = 0;
    for (opcode, bank, format, mode, load, base) in rows() {
        // The width expectation is independent of element_bytes().
        let width = match format {
            PairMemoryFormat::W32 | PairMemoryFormat::S32 => 4,
            PairMemoryFormat::X64 | PairMemoryFormat::D64 => 8,
            PairMemoryFormat::Q128 => 16,
        };
        for scaled in -64..=63 {
            let instruction = inst(
                opcode,
                vec![
                    reg(bank),
                    reg(bank + 1),
                    reg(2),
                    MachOperand::Imm(scaled * width),
                ],
            );
            let bits = word(base, scaled, 0, 1, 2);
            let checked = check_pair_encoding(&instruction, &bits.to_le_bytes()).unwrap();
            assert!(std::ptr::eq(checked.instruction(), &instruction));
            assert_eq!(checked.word(), bits);
            assert_eq!(checked.format(), format);
            assert_eq!(i64::from(checked.format().element_bytes()), width);
            assert_eq!(checked.mode(), mode);
            assert_eq!(checked.is_load(), load);
            assert_eq!(checked.transfer_fields(), [0, 1]);
            assert_eq!(checked.base(), PairMemoryBase::Register(2));
            assert_eq!(checked.byte_offset(), scaled * width);
            count += 1;
        }
        let omitted = inst(opcode, vec![reg(bank), reg(bank + 1), reg(2)]);
        let checked = check_pair_encoding(&omitted, &word(base, 0, 0, 1, 2).to_le_bytes()).unwrap();
        assert_eq!(checked.byte_offset(), 0);
        assert_eq!(checked.format(), format);
        assert_eq!(checked.mode(), mode);
        count += 1;
    }
    assert_eq!(count, 22 * 129);
}

#[test]
fn checked_pair_distinguishes_sp_zero_and_simd_field_31() {
    let mut count = 0;
    for base in [reg(31), MachOperand::Special(SpecialReg::SP)] {
        for (first, second, format, bits) in [
            (reg(160), reg(0), PairMemoryFormat::X64, 0xa900_03ff),
            (
                MachOperand::Special(SpecialReg::XZR),
                reg(0),
                PairMemoryFormat::X64,
                0xa900_03ff,
            ),
            (reg(161), reg(32), PairMemoryFormat::W32, 0x2900_03ff),
            (
                MachOperand::Special(SpecialReg::WZR),
                reg(32),
                PairMemoryFormat::W32,
                0x2900_03ff,
            ),
            (reg(95), reg(64), PairMemoryFormat::Q128, 0xad00_03ff),
            (reg(127), reg(96), PairMemoryFormat::D64, 0x6d00_03ff),
            (reg(159), reg(128), PairMemoryFormat::S32, 0x2d00_03ff),
        ] {
            let instruction = inst(Op::StpRI, vec![first, second, base.clone()]);
            let checked = check_pair_encoding(&instruction, &u32::to_le_bytes(bits)).unwrap();
            assert_eq!(checked.base(), PairMemoryBase::Sp);
            assert_eq!(checked.transfer_fields(), [31, 0]);
            assert_eq!(checked.format(), format);
            count += 1;
        }
    }
    // Identical numerical fields in distinct physical banks do not overlap.
    let fp = inst(
        Op::StpPreIndex,
        vec![reg(96), reg(97), reg(0), MachOperand::Imm(-16)],
    );
    let checked = check_pair_encoding(&fp, &word(0x6d80_0000, -2, 0, 1, 0).to_le_bytes()).unwrap();
    assert_eq!(checked.base(), PairMemoryBase::Register(0));
    assert_eq!(checked.format(), PairMemoryFormat::D64);
    assert_eq!(count, 14);
}

#[test]
fn checked_pair_frame_literals_reject_every_changed_bit() {
    for (opcode, offset, bits, mode) in [
        (
            Op::StpPreIndex,
            -16,
            0xa9bf_7bfdu32,
            PairMemoryMode::PreIndex,
        ),
        (
            Op::LdpPostIndex,
            16,
            0xa8c1_7bfdu32,
            PairMemoryMode::PostIndex,
        ),
    ] {
        let instruction = inst(
            opcode,
            vec![reg(29), reg(30), reg(31), MachOperand::Imm(offset)],
        );
        let checked = check_pair_encoding(&instruction, &bits.to_le_bytes()).unwrap();
        assert_eq!(checked.word(), bits);
        assert_eq!(checked.mode(), mode);
        assert_eq!(checked.transfer_fields(), [29, 30]);
        assert_eq!(checked.base(), PairMemoryBase::Sp);
        assert_eq!(checked.byte_offset(), offset);
        for bit in 0..32 {
            assert!(
                check_pair_encoding(&instruction, &(bits ^ (1 << bit)).to_le_bytes()).is_err(),
                "changed bit {bit}"
            );
        }
    }
}

#[test]
fn checked_pair_preserves_named_operand_refusals_and_order() {
    let cases = [
        (
            Op::StpRI,
            vec![reg(0), reg(1)],
            "pair memory requires exactly two transfers, X/SP base and optional immediate",
        ),
        (
            Op::StpRI,
            vec![reg(31), reg(1), reg(32)],
            "pair memory base must be canonical X/SP",
        ),
        (
            Op::StpRI,
            vec![reg(31), reg(1), reg(2)],
            "pair memory requires canonical W/X/ZR or S/D/Q transfers",
        ),
        (
            Op::StpRI,
            vec![reg(0), reg(33), reg(2)],
            "pair memory transfers must have matching widths and banks",
        ),
        (
            Op::NeonStpQPost,
            vec![reg(0), reg(1), reg(2)],
            "NEON Q-pair alias requires two Q registers",
        ),
        (
            Op::StpRI,
            vec![reg(0), reg(1), reg(2), MachOperand::Imm(1)],
            "pair memory offset must be an aligned signed scaled imm7",
        ),
        (
            Op::LdpRI,
            vec![reg(160), MachOperand::Special(SpecialReg::XZR), reg(2)],
            "load pair duplicate destinations are unpredictable, including field31",
        ),
        (
            Op::StpPreIndex,
            vec![reg(0), reg(1), reg(1)],
            "GPR pair writeback transfer/base overlap is unpredictable",
        ),
    ];
    for (opcode, operands, expected) in cases {
        // Invalid bytes must not replace the earlier canonical-operand reason.
        let instruction = inst(opcode, operands);
        assert_eq!(
            check_pair_encoding(&instruction, &[0; 4])
                .unwrap_err()
                .to_string(),
            expected
        );
    }
    for offset in [i64::MIN, i64::MAX, -520, 512] {
        let instruction = inst(
            Op::StpRI,
            vec![reg(0), reg(1), reg(2), MachOperand::Imm(offset)],
        );
        assert_eq!(
            check_pair_encoding(&instruction, &[0; 4])
                .unwrap_err()
                .to_string(),
            "pair memory offset must be an aligned signed scaled imm7"
        );
    }
}

#[test]
fn checked_pair_preserves_named_word_field_refusals() {
    let instruction = inst(Op::StpRI, vec![reg(0), reg(1), reg(2)]);
    let bits = 0xa900_0440u32;
    check_pair_encoding(&instruction, &bits.to_le_bytes()).unwrap();
    for (mutant, expected) in [
        (
            bits ^ (1 << 31),
            "pair opc: decoded 0 but the intent requires 2",
        ),
        (
            bits ^ (1 << 26),
            "pair V: decoded 1 but the intent requires 0",
        ),
        (
            bits ^ (1 << 23),
            "pair mode: decoded 3 but the intent requires 2",
        ),
        (
            bits ^ (1 << 22),
            "pair L: decoded true but the intent requires false",
        ),
        (
            bits ^ (1 << 15),
            "pair signed imm7: decoded 1 but the intent requires 0",
        ),
        (bits ^ 1, "pair Rt: decoded 1 but the intent requires 0"),
        (
            bits ^ (1 << 10),
            "pair Rt2: decoded 0 but the intent requires 1",
        ),
        (
            bits ^ (1 << 5),
            "pair Rn: decoded 3 but the intent requires 2",
        ),
    ] {
        assert_eq!(
            check_pair_encoding(&instruction, &mutant.to_le_bytes())
                .unwrap_err()
                .to_string(),
            expected
        );
    }
    for mutant in [
        0,
        bits & !(3 << 23),
        (bits & !(3 << 30)) | (1 << 30),
        bits | (1 << 30) | (1 << 26),
    ] {
        assert_eq!(
            check_pair_encoding(&instruction, &mutant.to_le_bytes())
                .unwrap_err()
                .to_string(),
            "pair intent does not decode as modeled pair memory"
        );
    }
}

#[test]
fn checked_pair_rejects_wrong_length_and_non_pair_opcode() {
    let instruction = inst(Op::StpRI, vec![reg(0), reg(1), reg(2)]);
    for len in [0, 1, 2, 3, 5, 8] {
        assert_eq!(
            check_pair_encoding(&instruction, &vec![0; len])
                .unwrap_err()
                .to_string(),
            format!("instruction byte range is {len} bytes; AArch64 instructions are exactly 4")
        );
    }
    let other = inst(Op::AddRR, vec![reg(0), reg(1), reg(2)]);
    assert_eq!(
        check_pair_encoding(&other, &0xa900_0440u32.to_le_bytes())
            .unwrap_err()
            .to_string(),
        "instruction is not a modeled pair memory opcode"
    );
}
