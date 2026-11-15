// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Additional ordinary scalar classes for the shared independent A64 decoder.
//!
//! The decoder reads actual instruction fields, never an encoder or source
//! opcode. Denotation extends the parent's existing architectural state model,
//! including full-X W-write clearing and each class's SP/ZR rules. Flag-writing
//! rows report `writes_nzcv`; they do NOT supply flags or preserve prior NZCV.
//! There are no proof registrations, lowering receipts or memory/ABI claims.
//!
//! Reference: Arm A64 ISA v2021-06, ADD (shifted register) pp19–20,
//! AND (immediate) pp29–30, MOVK/MOVN/MOVZ pp330–335:
//! <https://documentation-service.arm.com/static/60df18dc0320e92fa40b7e59>.

use super::{
    A64DecodeRefusal, A64DenoteRefusal, A64Dest, A64Effect, A64ValueWord, all_ones, bv, field,
    gpr_dest_zr, read_gpr_zr, shift_reg, zext,
};
use crate::aarch64_instruction_word_proofs::{DecodedWord, decode_word};
use trust_cg_ir::MachOperand;

/// Only these three classes are selected here. Neighbouring classes retain
/// the parent's existing decoder/refusal rather than a permissive fallback.
pub(super) fn decode(word: u32) -> Option<Result<A64ValueWord, A64DecodeRefusal>> {
    let unallocated = |reason| A64DecodeRefusal::Unallocated { word, reason };
    let sf = field(word, 31, 31);
    let rd = field(word, 4, 0);
    if field(word, 28, 23) == 0b100100 {
        let n = field(word, 22, 22);
        let immr = field(word, 21, 16);
        let imms = field(word, 15, 10);
        if decode_logical_imm(n, immr, imms, 32 << sf).is_none() {
            return Some(Err(unallocated("reserved logical-immediate fields")));
        }
        return Some(Ok(A64ValueWord::LogicalImmediate {
            sf,
            opc: field(word, 30, 29),
            n,
            immr,
            imms,
            rn: field(word, 9, 5),
            rd,
        }));
    }
    let decoded = decode_word(word);
    if let Some(DecodedWord::MoveWide {
        sf,
        opc,
        hw,
        imm16,
        rd,
    }) = decoded
    {
        if opc == 0b01 {
            return Some(Err(unallocated("move-wide opc == 01")));
        }
        if sf == 0 && hw >= 2 {
            return Some(Err(unallocated("32-bit move-wide with upper halfword")));
        }
        return Some(Ok(A64ValueWord::MoveWide {
            sf,
            opc,
            hw,
            imm16,
            rd,
        }));
    }
    if let Some(DecodedWord::AddSubShifted {
        sf,
        op,
        s,
        shift,
        rm,
        imm6,
        rn,
        rd,
    }) = decoded
    {
        if shift == 0b11 {
            return Some(Err(unallocated("add/sub shifted-register shift == 11")));
        }
        if sf == 0 && imm6 >= 32 {
            return Some(Err(unallocated("32-bit add/sub shift amount above 31")));
        }
        return Some(Ok(A64ValueWord::AddSubShiftedReg {
            sf,
            op,
            s,
            shift,
            rm,
            imm6,
            rn,
            rd,
        }));
    }
    None
}

pub(super) fn denote(word: &A64ValueWord) -> Result<A64Effect, A64DenoteRefusal> {
    let invalid = || A64DenoteRefusal::UnmodeledInstruction("invalid decoded scalar fields");
    match *word {
        A64ValueWord::LogicalImmediate {
            sf,
            opc,
            n,
            immr,
            imms,
            rn,
            rd,
        } => {
            if sf > 1 || opc > 3 || rn > 31 || rd > 31 {
                return Err(invalid());
            }
            let width = 32 << sf;
            let mask = decode_logical_imm(n, immr, imms, width).ok_or_else(invalid)?;
            let left = read_gpr_zr(rn, width);
            let right = bv(mask, width);
            let result = match opc {
                0b01 => left.bvor(right),
                0b10 => left.bvxor(right),
                _ => left.bvand(right),
            };
            // Non-setting logical-immediate rows may write SP. Their Rn=31
            // always reads ZR; ANDS Rd=31 discards the write instead.
            let dest = if rd == 31 && opc != 0b11 {
                A64Dest::Sp
            } else {
                gpr_dest_zr(rd)
            };
            Ok(A64Effect {
                dest,
                value: zext(result, 64),
                writes_nzcv: opc == 0b11,
            })
        }
        A64ValueWord::MoveWide {
            sf,
            opc,
            hw,
            imm16,
            rd,
        } => {
            if sf > 1
                || !matches!(opc, 0b00 | 0b10 | 0b11)
                || hw >= 2 << sf
                || imm16 > 0xffff
                || rd > 31
            {
                return Err(invalid());
            }
            let width = 32 << sf;
            let position = 16 * hw;
            let field = bv(u64::from(imm16) << position, width);
            let result = match opc {
                0b00 => field.bvxor(all_ones(width)),
                0b10 => field,
                _ => read_gpr_zr(rd, width)
                    .bvand(bv(!(0xffff_u64 << position), width))
                    .bvor(field),
            };
            Ok(A64Effect {
                dest: gpr_dest_zr(rd),
                value: zext(result, 64),
                writes_nzcv: false,
            })
        }
        A64ValueWord::AddSubShiftedReg {
            sf,
            op,
            s,
            shift,
            rm,
            imm6,
            rn,
            rd,
        } => {
            if sf > 1
                || op > 1
                || s > 1
                || shift > 2
                || imm6 >= 32 << sf
                || rn > 31
                || rm > 31
                || rd > 31
            {
                return Err(invalid());
            }
            let width = 32 << sf;
            let left = read_gpr_zr(rn, width);
            let right = shift_reg(read_gpr_zr(rm, width), shift, imm6, width);
            let result = if op == 0 {
                left.bvadd(right)
            } else {
                left.bvsub(right)
            };
            Ok(A64Effect {
                dest: gpr_dest_zr(rd),
                value: zext(result, 64),
                writes_nzcv: s == 1,
            })
        }
        _ => Err(invalid()),
    }
}

/// Shared machine-intent field validation, formerly local to CEGIS. This does
/// not decode a word; actual-word endpoints must read the word's own fields.
pub(crate) fn move_wide_fields(operands: &[MachOperand], width: u32) -> Option<(u64, u32)> {
    if !matches!(width, 32 | 64) {
        return None;
    }
    let (imm, shift) = match operands {
        [_, MachOperand::Imm(imm)] => (*imm, 0),
        [_, MachOperand::Imm(imm), MachOperand::Imm(shift)] => (*imm, *shift),
        _ => return None,
    };
    if !(0..=0xffff).contains(&imm) || shift < 0 || shift % 16 != 0 {
        return None;
    }
    let hw = u32::try_from(shift / 16).ok()?;
    (hw < width / 16).then_some((imm as u64, hw))
}

/// The `wmask` from Arm DecodeBitMasks(N, imms, immr, TRUE, datasize), formerly
/// local to CEGIS. All inputs are validated; masking cannot hide bad fields.
pub(crate) fn decode_logical_imm(n: u32, immr: u32, imms: u32, datasize: u32) -> Option<u64> {
    if !matches!(datasize, 32 | 64) || n > 1 || immr > 63 || imms > 63 || (datasize == 32 && n != 0)
    {
        return None;
    }
    let combined = (n << 6) | (!imms & 0x3f);
    if combined == 0 {
        return None;
    }
    let len = 31 - combined.leading_zeros();
    if len < 1 {
        return None;
    }
    let element_width = 1u32 << len;
    if element_width > datasize {
        return None;
    }
    let levels = element_width - 1;
    if imms & levels == levels {
        return None;
    }
    let s = imms & levels;
    let r = immr & levels;
    let ones = |bits: u32| {
        if bits == 64 {
            u64::MAX
        } else {
            (1u64 << bits) - 1
        }
    };
    let element = ones(s + 1);
    let rotated = if r == 0 {
        element
    } else {
        ((element >> r) | (element << (element_width - r))) & ones(element_width)
    };
    let mut mask = 0;
    let mut position = 0;
    while position < datasize {
        mask |= rotated << position;
        position += element_width;
    }
    Some(mask & ones(datasize))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aarch64_value_decode_proofs::{
        FieldOverrides, decode_a64_value_word, denote_a64_value_word,
    };
    use crate::smt::EvalEnv;

    fn effect(word: u32) -> A64Effect {
        denote_a64_value_word(
            &decode_a64_value_word(word).unwrap(),
            &FieldOverrides::default(),
        )
        .unwrap()
    }

    fn value(word: u32, x0: u64, x1: u64, x2: u64) -> u64 {
        let mut env = EvalEnv::default();
        env.insert("x0".into(), x0);
        env.insert("x1".into(), x1);
        env.insert("x2".into(), x2);
        effect(word).value.try_eval(&env).unwrap().as_u64()
    }

    #[test]
    fn scalar_decoder_fields_and_reserved_neighbours() {
        assert_eq!(
            decode_a64_value_word(0x9240_0c20),
            Ok(A64ValueWord::LogicalImmediate {
                sf: 1,
                opc: 0,
                n: 1,
                immr: 0,
                imms: 3,
                rn: 1,
                rd: 0,
            })
        );
        assert_eq!(
            decode_a64_value_word(0xf2c2_4680),
            Ok(A64ValueWord::MoveWide {
                sf: 1,
                opc: 3,
                hw: 2,
                imm16: 0x1234,
                rd: 0,
            })
        );
        assert_eq!(
            decode_a64_value_word(0xcb82_fc20),
            Ok(A64ValueWord::AddSubShiftedReg {
                sf: 1,
                op: 1,
                s: 0,
                shift: 2,
                rm: 2,
                imm6: 63,
                rn: 1,
                rd: 0,
            })
        );
        for word in [
            0x1240_0020, // W logical immediate with N=1.
            0x9200_fc20, // Reserved all-ones logical element.
            0x9200_f820, // Logical element width below two.
            0xb280_0000, // Move-wide opc=01.
            0x52c0_0000, // W move-wide hw=2.
            0x72e0_0000, // W MOVK hw=3.
            0x8bc2_0020, // Shifted ADD with reserved ROR.
            0x0b02_8020, // W shifted ADD by 32.
        ] {
            assert!(
                matches!(
                    decode_a64_value_word(word),
                    Err(A64DecodeRefusal::Unallocated { .. })
                ),
                "{word:#010x}"
            );
        }
        // Bit21 switches ADD to its separate extended-register class. It must
        // not be interpreted as this shifted-register family.
        assert!(matches!(
            decode_a64_value_word(0x8b22_0020),
            Err(A64DecodeRefusal::NotModeled { .. })
        ));
        for (n, r, s, width) in [(2, 0, 0, 64), (0, 64, 0, 64), (0, 0, 64, 64), (0, 0, 0, 16)] {
            assert_eq!(decode_logical_imm(n, r, s, width), None);
        }
    }

    #[test]
    fn logical_immediate_full_x_sp_zr_and_flags() {
        for sf in 0..=1 {
            let width = 32 << sf;
            for (n, r, s, mask) in [
                (sf, 0, 3, 15),
                (sf, 1, 0, 1u64 << (width - 1)),
                (0, 0, 60, 0x5555_5555_5555_5555),
            ] {
                for opc in 0..=3 {
                    let word = (sf << 31)
                        | (opc << 29)
                        | 0x1200_0000
                        | (n << 22)
                        | (r << 16)
                        | (s << 10)
                        | (1 << 5);
                    let width_mask = if sf == 0 { u32::MAX as u64 } else { u64::MAX };
                    for input in [0, u64::MAX, 0x8000_0001_0123_4567] {
                        let expected = match opc {
                            1 => input | mask,
                            2 => input ^ mask,
                            _ => input & mask,
                        } & width_mask;
                        assert_eq!(
                            value(word, 0, input, 0),
                            expected,
                            "{word:#010x}/{input:#x}"
                        );
                    }
                    let decoded = effect(word);
                    assert_eq!(decoded.dest, A64Dest::Gpr(0));
                    assert_eq!(decoded.writes_nzcv, opc == 3);
                    let zero_source = (word & !(31 << 5)) | (31 << 5);
                    assert_eq!(
                        value(zero_source, 0, u64::MAX, 0),
                        if matches!(opc, 1 | 2) {
                            mask & width_mask
                        } else {
                            0
                        }
                    );
                    assert_eq!(
                        effect(word | 31).dest,
                        if opc == 3 {
                            A64Dest::Discarded
                        } else {
                            A64Dest::Sp
                        }
                    );
                }
            }
        }
    }

    #[test]
    fn move_wide_preserves_only_selected_halfword_and_clears_w_high_bits() {
        for sf in 0..=1 {
            let width_mask = if sf == 0 { u32::MAX as u64 } else { u64::MAX };
            for opc in [0, 2, 3] {
                for hw in 0..(2 << sf) {
                    for imm in [0, 1, 0x8000, 0xffff] {
                        let word = (sf << 31) | (opc << 29) | 0x1280_0000 | (hw << 21) | (imm << 5);
                        for old in [0, u64::MAX, 0x0123_4567_89ab_cdef] {
                            let position = 16 * hw;
                            let field = u64::from(imm) << position;
                            let expected = match opc {
                                0 => !field,
                                2 => field,
                                _ => (old & !(0xffff_u64 << position)) | field,
                            } & width_mask;
                            assert_eq!(value(word, old, 0, 0), expected, "{word:#010x}/{old:#x}");
                        }
                        assert_eq!(effect(word).dest, A64Dest::Gpr(0));
                        assert!(!effect(word).writes_nzcv);
                        assert_eq!(effect(word | 31).dest, A64Dest::Discarded);
                    }
                }
            }
        }
        let mut env = EvalEnv::default();
        let base = value(0x5282_4680, u64::MAX, 0, 0); // MOVZ W0,#0x1234.
        env.insert("x0".into(), base);
        assert_eq!(
            effect(0xf2c2_4680).value.try_eval(&env).unwrap().as_u64(),
            0x1234_0000_1234
        );
        assert_eq!(
            move_wide_fields(&[MachOperand::Imm(0), MachOperand::Imm(1)], 16),
            None
        );
    }

    #[test]
    fn shifted_arithmetic_boundaries_and_zero_register_never_sp() {
        for sf in 0..=1 {
            let width = 32 << sf;
            let mask = if sf == 0 { u32::MAX as u64 } else { u64::MAX };
            for op in 0..=1 {
                for s in 0..=1 {
                    for shift in 0..=2 {
                        for amount in [0, 1, width - 1] {
                            let word = (sf << 31)
                                | (op << 30)
                                | (s << 29)
                                | 0x0b00_0000
                                | (shift << 22)
                                | (2 << 16)
                                | (amount << 10)
                                | (1 << 5);
                            for (left, right) in [
                                (0, 0),
                                (u64::MAX, 1),
                                (1, u64::MAX),
                                (0x8000_0001_0000_0001, 0x8000_0000_8000_0000),
                            ] {
                                let rhs = right & mask;
                                let shifted = match shift {
                                    0 => rhs << amount,
                                    1 => rhs >> amount,
                                    _ if sf == 0 => ((rhs as u32 as i32 >> amount) as u32) as u64,
                                    _ => (rhs as i64 >> amount) as u64,
                                } & mask;
                                let expected = if op == 0 {
                                    (left & mask).wrapping_add(shifted)
                                } else {
                                    (left & mask).wrapping_sub(shifted)
                                } & mask;
                                assert_eq!(value(word, 0, left, right), expected, "{word:#010x}");
                            }
                            assert_eq!(effect(word).writes_nzcv, s == 1);
                            assert_eq!(effect(word | 31).dest, A64Dest::Discarded);
                            let zero_source = (word & !(31 << 5)) | (31 << 5);
                            assert_eq!(value(zero_source, 0, u64::MAX, 0), 0);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn existing_bitfield_asr_denotation_is_reused_at_all_boundary_shifts() {
        for sf in 0..=1 {
            let width = 32 << sf;
            for amount in [0, 1, width - 1] {
                let word = (sf << 31)
                    | 0x1300_0000
                    | (sf << 22)
                    | (amount << 16)
                    | ((width - 1) << 10)
                    | (1 << 5);
                assert!(matches!(
                    decode_a64_value_word(word),
                    Ok(A64ValueWord::Bitfield { opc: 0, .. })
                ));
                for input in [0, u64::MAX, 0x8000_0000_8000_0000, 0x7fff_ffff_7fff_ffff] {
                    let expected = if sf == 0 {
                        ((input as u32 as i32 >> amount) as u32) as u64
                    } else {
                        (input as i64 >> amount) as u64
                    };
                    assert_eq!(value(word, 0, input, 0), expected);
                }
            }
        }
    }
}
