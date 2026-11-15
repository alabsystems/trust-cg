// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Independent fields of ordinary direct A64 control words.
//!
//! Displacements are signed WORD offsets relative to the branch instruction's
//! PC, not its fallthrough. This supplies no CFG, ABI, proof or publication
//! authority; callers separately choose their supported control profile.

use crate::aarch64_instruction_word_proofs::{DecodedWord, decode_word};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum A64ControlWord {
    Branch {
        displacement: i64,
    },
    ConditionalBranch {
        condition: u8,
        displacement: i64,
    },
    CompareBranch {
        register: u8,
        bits: u32,
        nonzero: bool,
        displacement: i64,
    },
    Return {
        register: u8,
    },
}

fn signed(field: u32, bits: u32) -> i64 {
    let shift = 64 - bits;
    (i64::from(field) << shift) >> shift
}

/// Decode actual fields, refusing BL, BC.cond, reserved B.cond bit 4 and
/// neighbouring instruction classes. B.cond condition 14/15 is retained;
/// a caller's profile may refuse it, but neither is invented as a complement.
pub fn decode_a64_control_word(word: u32) -> Option<A64ControlWord> {
    match decode_word(word) {
        Some(DecodedWord::BranchImm { op: 0, imm26 }) => {
            return Some(A64ControlWord::Branch {
                displacement: signed(imm26, 26),
            });
        }
        Some(DecodedWord::CondBranch {
            o1: 0,
            imm19,
            o0: 0,
            cond,
        }) => {
            return Some(A64ControlWord::ConditionalBranch {
                condition: cond as u8,
                displacement: signed(imm19, 19),
            });
        }
        _ => {}
    }
    // Exact CBZ/CBNZ fixed bits; sf and op select W/X and zero/nonzero.
    if word & 0x7e00_0000 == 0x3400_0000 {
        return Some(A64ControlWord::CompareBranch {
            register: (word & 31) as u8,
            bits: if word >> 31 == 0 { 32 } else { 64 },
            nonzero: word & (1 << 24) != 0,
            displacement: signed((word >> 5) & 0x7_ffff, 19),
        });
    }
    // Only Rn[9:5] varies. BR, BLR, authenticated returns and fixed-bit
    // neighbours must not acquire ordinary RET semantics.
    if word & 0xffff_fc1f == 0xd65f_0000 {
        return Some(A64ControlWord::Return {
            register: ((word >> 5) & 31) as u8,
        });
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn direct_branch_signed_word_boundaries_and_call_refusal() {
        for (field, displacement) in [
            (0, 0),
            (1, 1),
            (0x01ff_ffff, (1 << 25) - 1),
            (0x0200_0000, -(1 << 25)),
            (0x03ff_ffff, -1),
        ] {
            assert_eq!(
                decode_a64_control_word(0x1400_0000 | field),
                Some(A64ControlWord::Branch { displacement })
            );
            assert!(decode_a64_control_word(0x9400_0000 | field).is_none());
        }
    }

    #[test]
    fn conditional_branch_exact_reserved_bits_and_all_condition_fields() {
        for condition in 0..16 {
            for (field, displacement) in [
                (0, 0),
                (1, 1),
                (0x3_ffff, (1 << 18) - 1),
                (0x4_0000, -(1 << 18)),
                (0x7_ffff, -1),
            ] {
                let word = 0x5400_0000 | (field << 5) | condition;
                assert_eq!(
                    decode_a64_control_word(word),
                    Some(A64ControlWord::ConditionalBranch {
                        condition: condition as u8,
                        displacement,
                    })
                );
                assert!(decode_a64_control_word(word | 16).is_none());
                assert!(decode_a64_control_word(word | (1 << 24)).is_none());
            }
        }
    }

    #[test]
    fn compare_branches_keep_actual_width_zr_and_signed_offsets() {
        for width64 in [false, true] {
            for nonzero in [false, true] {
                for register in [0, 17, 30, 31] {
                    for (field, displacement) in [
                        (0, 0),
                        (1, 1),
                        (0x3_ffff, (1 << 18) - 1),
                        (0x4_0000, -(1 << 18)),
                        (0x7_ffff, -1),
                    ] {
                        let word = 0x3400_0000
                            | (u32::from(width64) << 31)
                            | (u32::from(nonzero) << 24)
                            | (field << 5)
                            | register;
                        assert_eq!(
                            decode_a64_control_word(word),
                            Some(A64ControlWord::CompareBranch {
                                register: register as u8,
                                bits: if width64 { 64 } else { 32 },
                                nonzero,
                                displacement,
                            })
                        );
                        assert!(decode_a64_control_word(word ^ (1 << 25)).is_none());
                    }
                }
            }
        }
    }

    #[test]
    fn returns_preserve_actual_register_but_reject_fixed_bit_neighbours() {
        for register in 0..32 {
            let word = 0xd65f_0000 | (register << 5);
            assert_eq!(
                decode_a64_control_word(word),
                Some(A64ControlWord::Return {
                    register: register as u8,
                })
            );
            for bit in (0..5).chain(10..32) {
                assert!(decode_a64_control_word(word ^ (1 << bit)).is_none());
            }
        }
        for word in [
            0xd61f_03c0,
            0xd63f_03c0,
            0xd65f_0bff,
            0xd69f_03e0,
            0xd503_201f,
        ] {
            assert!(decode_a64_control_word(word).is_none(), "{word:#010x}");
        }
    }
}
