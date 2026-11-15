// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Optional NZCV denotation alongside the shared A64 value denotation.
//!
//! This composes the existing architectural arithmetic/logical flag encoders
//! with the decoded word's actual width and operands. No source comparison or
//! condition chooses a producer. Construction supplies no proof registration,
//! lowering receipt, Checked credit or claim about preservation of older flags.

use super::{
    A64DenoteRefusal, A64ValueWord, Field, FieldOverrides, all_ones, bv, decode_logical_imm,
    read_gpr_sp, read_gpr_zr, shift_reg, zext,
};
use crate::nzcv::{NzcvFlags, encode_adds, encode_subs, encode_tst};
use crate::smt::SmtSort;

/// Exact flags written by a modeled integer word, expressed over `x0` through
/// `x30` and `sp`, just like [`super::denote_a64_value_word`].
///
/// A flag-setting ADD/SUB immediate consumes the SAME `imm12` override as the
/// value denotation, but requires its architectural BV12 sort. Other overrides
/// are unused by these classes. Non-flag-setting classes return `None`; a
/// decoded MSR NZCV is an unsupported writer and returns an error, not `None`.
/// This API does not decide whether a caller's complete stream preserves flags.
pub fn denote_a64_value_flags(
    word: &A64ValueWord,
    fields: &FieldOverrides,
) -> Result<Option<NzcvFlags>, A64DenoteRefusal> {
    let invalid = || A64DenoteRefusal::UnmodeledInstruction("invalid decoded integer flag fields");
    let arithmetic = |op, left, right, width| {
        if op == 0 {
            encode_adds(left, right, width).1
        } else {
            encode_subs(left, right, width).1
        }
    };
    let flags = match *word {
        A64ValueWord::LogicalShiftedReg {
            sf,
            opc,
            shift,
            n,
            rm,
            imm6,
            rn,
            rd,
        } => {
            if sf > 1
                || opc > 3
                || shift > 3
                || n > 1
                || imm6 >= 32 << sf
                || rm > 31
                || rn > 31
                || rd > 31
            {
                return Err(invalid());
            }
            if opc != 0b11 {
                return Ok(None);
            }
            let width = 32 << sf;
            let mut right = shift_reg(read_gpr_zr(rm, width), shift, imm6, width);
            if n == 1 {
                right = right.bvxor(all_ones(width));
            }
            encode_tst(read_gpr_zr(rn, width), right, width)
        }
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
            if opc != 0b11 {
                return Ok(None);
            }
            encode_tst(read_gpr_zr(rn, width), bv(mask, width), width)
        }
        A64ValueWord::AddSubImm {
            sf,
            op,
            s,
            sh,
            imm12,
            rn,
            rd,
        } => {
            if sf > 1 || op > 1 || s > 1 || sh > 1 || imm12 > 4095 || rn > 31 || rd > 31 {
                return Err(invalid());
            }
            if s == 0 {
                return Ok(None);
            }
            if fields
                .imm12
                .as_ref()
                .is_some_and(|term| term.sort() != SmtSort::BitVec(12))
            {
                return Err(A64DenoteRefusal::UnmodeledInstruction(
                    "imm12 flag override must have BV12 sort",
                ));
            }
            let width = 32 << sf;
            let mut right = zext(Field::pick(imm12, &fields.imm12).term(12), width);
            if sh == 1 {
                right = right.bvshl(bv(12, width));
            }
            arithmetic(op, read_gpr_sp(rn, width), right, width)
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
                || rm > 31
                || rn > 31
                || rd > 31
            {
                return Err(invalid());
            }
            if s == 0 {
                return Ok(None);
            }
            let width = 32 << sf;
            let right = shift_reg(read_gpr_zr(rm, width), shift, imm6, width);
            arithmetic(op, read_gpr_zr(rn, width), right, width)
        }
        A64ValueWord::SysRegMove {
            l: 0,
            op0: 3,
            op1: 3,
            crn: 4,
            crm: 2,
            op2: 0,
            ..
        } => {
            return Err(A64DenoteRefusal::UnmodeledInstruction(
                "MSR NZCV is outside the integer flag denotation",
            ));
        }
        _ => return Ok(None),
    };
    Ok(Some(flags))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aarch64_value_decode_proofs::{decode_a64_value_word, denote_a64_value_word};
    use crate::smt::{EvalEnv, SmtExpr};

    fn env(x1: u64, x2: u64, sp: u64) -> EvalEnv {
        let mut env = EvalEnv::default();
        env.insert("x1".into(), x1);
        env.insert("x2".into(), x2);
        env.insert("sp".into(), sp);
        env
    }

    fn evaluated(flags: &NzcvFlags, env: &EvalEnv) -> [bool; 4] {
        [&flags.n, &flags.z, &flags.c, &flags.v].map(|term| term.try_eval(env).unwrap().as_bool())
    }

    fn word_flags(word: u32) -> NzcvFlags {
        let decoded = decode_a64_value_word(word).unwrap();
        assert!(
            denote_a64_value_word(&decoded, &FieldOverrides::default())
                .unwrap()
                .writes_nzcv
        );
        denote_a64_value_flags(&decoded, &FieldOverrides::default())
            .unwrap()
            .unwrap()
    }

    fn expected_arithmetic(width: u32, sub: bool, left: u64, right: u64) -> [bool; 4] {
        let mask = if width == 32 {
            u32::MAX as u64
        } else {
            u64::MAX
        };
        let sign = 1u64 << (width - 1);
        let left = left & mask;
        let right = right & mask;
        let result = if sub {
            left.wrapping_sub(right)
        } else {
            left.wrapping_add(right)
        } & mask;
        let carry = if sub {
            left >= right
        } else {
            u128::from(left) + u128::from(right) > u128::from(mask)
        };
        let signs_differ = (left ^ right) & sign != 0;
        let overflow =
            (if sub { signs_differ } else { !signs_differ }) && (left ^ result) & sign != 0;
        [result & sign != 0, result == 0, carry, overflow]
    }

    #[test]
    fn logical_flags_shift_inversion_and_immediate_clear_carry_and_overflow() {
        for sf in 0..=1 {
            let width = 32 << sf;
            let mask = if sf == 0 { u32::MAX as u64 } else { u64::MAX };
            for invert in 0..=1 {
                for shift in 0..=3 {
                    for amount in [0, width - 1] {
                        let word = (sf << 31)
                            | 0x6a00_0000
                            | (shift << 22)
                            | (invert << 21)
                            | (2 << 16)
                            | (amount << 10)
                            | (1 << 5);
                        let flags = word_flags(word);
                        for (left, right) in [
                            (0, u64::MAX),
                            (u64::MAX, 0),
                            (u64::MAX, u64::MAX),
                            (0x8000_0000_8000_0000, 1),
                        ] {
                            let rhs = right & mask;
                            let shifted = match shift {
                                0 => rhs << amount,
                                1 => rhs >> amount,
                                2 if sf == 0 => ((rhs as u32 as i32 >> amount) as u32) as u64,
                                2 => (rhs as i64 >> amount) as u64,
                                _ if amount == 0 => rhs,
                                _ => (rhs >> amount) | (rhs << (width - amount)),
                            } & mask;
                            let rhs = if invert == 1 {
                                !shifted & mask
                            } else {
                                shifted
                            };
                            let result = left & rhs & mask;
                            assert_eq!(
                                evaluated(&flags, &env(left, right, u64::MAX)),
                                [result >> (width - 1) != 0, result == 0, false, false]
                            );
                        }
                        let zero_rn = (word & !(31 << 5)) | (31 << 5);
                        assert_eq!(
                            evaluated(&word_flags(zero_rn), &env(u64::MAX, u64::MAX, u64::MAX)),
                            [false, true, false, false]
                        );
                    }
                }
            }
            for (n, r, s, immediate) in [(sf, 0, 3, 15), (sf, 1, 0, 1u64 << (width - 1))] {
                let word = (sf << 31) | 0x7200_0000 | (n << 22) | (r << 16) | (s << 10) | (1 << 5);
                for input in [0, u64::MAX, 0x8000_0000_8000_0000] {
                    let result = input & immediate & mask;
                    assert_eq!(
                        evaluated(&word_flags(word), &env(input, 0, 0)),
                        [result >> (width - 1) != 0, result == 0, false, false]
                    );
                }
            }
        }
    }

    #[test]
    fn add_sub_shifted_flags_match_independent_carry_overflow_boundaries() {
        for sf in 0..=1 {
            let width = 32 << sf;
            let mask = if sf == 0 { u32::MAX as u64 } else { u64::MAX };
            let sign = 1u64 << (width - 1);
            for op in 0..=1 {
                for shift in 0..=2 {
                    for amount in [0, 1, width - 1] {
                        let word = (sf << 31)
                            | (op << 30)
                            | 0x2b00_0000
                            | (shift << 22)
                            | (2 << 16)
                            | (amount << 10)
                            | (1 << 5)
                            | 31;
                        let flags = word_flags(word);
                        for (left, right) in [
                            (0, 0),
                            (0, 1),
                            (mask, 1),
                            (sign - 1, 1),
                            (sign, 1),
                            (sign, mask),
                            (sign, sign),
                        ] {
                            let rhs = right & mask;
                            let shifted = match shift {
                                0 => rhs << amount,
                                1 => rhs >> amount,
                                _ if sf == 0 => ((rhs as u32 as i32 >> amount) as u32) as u64,
                                _ => (rhs as i64 >> amount) as u64,
                            } & mask;
                            assert_eq!(
                                evaluated(&flags, &env(left | (!mask), right, 0)),
                                expected_arithmetic(width, op == 1, left, shifted),
                                "{word:#010x}/{left:#x}/{right:#x}"
                            );
                        }
                        let zero_rn = (word & !(31 << 5)) | (31 << 5);
                        assert_eq!(
                            evaluated(&word_flags(zero_rn), &env(mask, 0, mask)),
                            expected_arithmetic(width, op == 1, 0, 0)
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn add_sub_immediate_flags_read_actual_sp_and_shifted_imm12() {
        for sf in 0..=1 {
            let width = 32 << sf;
            let mask = if sf == 0 { u32::MAX as u64 } else { u64::MAX };
            let sign = 1u64 << (width - 1);
            for op in 0..=1 {
                for shift in 0..=1 {
                    for immediate in [0, 1, 4095] {
                        let word = (sf << 31)
                            | (op << 30)
                            | 0x3100_0000
                            | (shift << 22)
                            | (immediate << 10)
                            | (31 << 5)
                            | 31;
                        for input in [0, 1, mask, sign - 1, sign] {
                            let right = u64::from(immediate) << (12 * shift);
                            assert_eq!(
                                evaluated(&word_flags(word), &env(!input, 0, input | (!mask))),
                                expected_arithmetic(width, op == 1, input, right)
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn field_override_matches_value_denotation_and_refuses_wrong_sort() {
        let decoded = decode_a64_value_word(0xf140_043f).unwrap(); // SUBS XZR,X1,#1,LSL#12.
        let fields = FieldOverrides {
            imm12: Some(SmtExpr::var("immediate", 12)),
            ..Default::default()
        };
        let flags = denote_a64_value_flags(&decoded, &fields).unwrap().unwrap();
        let value = denote_a64_value_word(&decoded, &fields).unwrap().value;
        for (input, immediate) in [(0, 0), (0, 4095), (4096, 1), (1u64 << 63, 1)] {
            let mut environment = env(input, 0, 0);
            environment.insert("immediate".into(), immediate);
            let right = immediate << 12;
            assert_eq!(
                evaluated(&flags, &environment),
                expected_arithmetic(64, true, input, right)
            );
            assert_eq!(
                value.try_eval(&environment).unwrap().as_u64(),
                input.wrapping_sub(right)
            );
        }
        for wrong in [SmtExpr::bv_const(1, 64), SmtExpr::bool_const(true)] {
            let fields = FieldOverrides {
                imm12: Some(wrong),
                ..Default::default()
            };
            assert!(denote_a64_value_flags(&decoded, &fields).is_err());
        }
    }

    #[test]
    fn nonflag_words_supply_none_and_unmodeled_nzcv_writer_refuses() {
        for word in [
            0x8a02_0020,
            0xaa02_0020,
            0x9240_0c20,
            0x9100_0420,
            0x8b02_0020,
            0xd280_0020,
            0x9343_fc20,
        ] {
            let decoded = decode_a64_value_word(word).unwrap();
            assert!(
                !denote_a64_value_word(&decoded, &FieldOverrides::default())
                    .unwrap()
                    .writes_nzcv
            );
            assert!(
                denote_a64_value_flags(&decoded, &FieldOverrides::default())
                    .unwrap()
                    .is_none()
            );
        }
        let writer = A64ValueWord::SysRegMove {
            l: 0,
            op0: 3,
            op1: 3,
            crn: 4,
            crm: 2,
            op2: 0,
            rt: 1,
        };
        assert!(
            denote_a64_value_word(&writer, &FieldOverrides::default())
                .unwrap()
                .writes_nzcv
        );
        assert!(denote_a64_value_flags(&writer, &FieldOverrides::default()).is_err());
        for malformed in [
            A64ValueWord::LogicalShiftedReg {
                sf: 0,
                opc: 3,
                shift: 0,
                n: 0,
                rm: 2,
                imm6: 32,
                rn: 1,
                rd: 0,
            },
            A64ValueWord::LogicalImmediate {
                sf: 0,
                opc: 3,
                n: 1,
                immr: 0,
                imms: 0,
                rn: 1,
                rd: 0,
            },
            A64ValueWord::AddSubImm {
                sf: 1,
                op: 0,
                s: 1,
                sh: 2,
                imm12: 1,
                rn: 1,
                rd: 0,
            },
            A64ValueWord::AddSubShiftedReg {
                sf: 1,
                op: 1,
                s: 1,
                shift: 3,
                rm: 2,
                imm6: 0,
                rn: 1,
                rd: 0,
            },
        ] {
            assert!(denote_a64_value_flags(&malformed, &FieldOverrides::default()).is_err());
        }
    }
}
