// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Compact fixed-field denotation for architectural ASR and MOV aliases.
//!
//! This optional API does not replace the registered value denotation. Symbolic
//! bitfield overrides and every nonalias instruction row delegate to that unchanged
//! implementation, preserving its expression/query identity. No source opcode,
//! normal-form equality, simplifier, proof or instruction credit selects a row.
//!
//! Reference: Arm A64 ISA v2021-06, ASR (immediate), an alias of SBFM:
//! <https://documentation-service.arm.com/static/60df18dc0320e92fa40b7e59>.

use super::{
    A64DenoteRefusal, A64Effect, A64ValueWord, FieldOverrides, bv, denote_a64_value_word,
    gpr_dest_zr, read_gpr_zr, zext,
};
use crate::aarch64_semantics::encode_asr_rr;
use trust_cg_ir::cc::OperandSize;

/// Denote the exact ORR/ZR/LSL#0 MOV alias as a register read, and the
/// valid fixed SBFM alias with `imms == datasize-1` as arithmetic
/// right shift. Both fields must be concrete: either bitfield override causes
/// an exact delegation to [`denote_a64_value_word`]. All other rows also use
/// that existing API unchanged. Manually malformed SBFM fields are refused.
///
/// Every W result is zero-extended to the full X destination; Rn/Rd=31 mean
/// ZR/discard, never SP. The decoded alias does not write NZCV. Construction
/// is not equivalence replay, a proof registration, Checked or native credit.
pub fn denote_a64_value_word_compact(
    word: &A64ValueWord,
    fields: &FieldOverrides,
) -> Result<A64Effect, A64DenoteRefusal> {
    if let A64ValueWord::LogicalShiftedReg {
        sf,
        opc: 1,
        shift: 0,
        n: 0,
        rm,
        imm6: 0,
        rn: 31,
        rd,
    } = *word
    {
        if sf > 1 || rm > 31 || rd > 31 {
            return Err(A64DenoteRefusal::UnmodeledInstruction(
                "invalid decoded MOV register fields",
            ));
        }
        // Arm's MOV (register) alias selects exactly these encoding fields.
        // W reads retain the architecture's full-X zero extension; register
        // 31 is ZR/discard. No source identity or equality goal selects it.
        return Ok(A64Effect {
            dest: gpr_dest_zr(rd),
            value: zext(read_gpr_zr(rm, 32 << sf), 64),
            writes_nzcv: false,
        });
    }
    let A64ValueWord::Bitfield {
        sf,
        opc: 0,
        n,
        immr,
        imms,
        rn,
        rd,
    } = *word
    else {
        return denote_a64_value_word(word, fields);
    };
    let invalid = || A64DenoteRefusal::UnmodeledInstruction("invalid decoded SBFM fields");
    if sf > 1 {
        return Err(invalid());
    }
    let width = 32 << sf;
    if n != sf || immr >= width || imms >= width || rn > 31 || rd > 31 {
        return Err(invalid());
    }
    if fields.immr.is_some() || fields.imms.is_some() || imms != width - 1 {
        return denote_a64_value_word(word, fields);
    }
    // The literal ISA field is already restricted to 0..datasize. There is
    // no out-of-range register shift, source premise or amount masking here.
    let size = if width == 32 {
        OperandSize::S32
    } else {
        OperandSize::S64
    };
    let value = encode_asr_rr(size, read_gpr_zr(rn, width), bv(u64::from(immr), width));
    Ok(A64Effect {
        dest: gpr_dest_zr(rd),
        value: zext(value, 64),
        writes_nzcv: false,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aarch64_value_decode_proofs::{A64Dest, decode_a64_value_word};
    use crate::smt::{EvalEnv, SmtExpr};

    fn asr(sf: u32, amount: u32, rn: u32, rd: u32) -> u32 {
        (sf << 31)
            | 0x1300_0000
            | (sf << 22)
            | (amount << 16)
            | (((32 << sf) - 1) << 10)
            | (rn << 5)
            | rd
    }

    fn evaluate(value: &SmtExpr, source: u64) -> u64 {
        let mut env = EvalEnv::default();
        env.insert("x1".into(), source);
        value.try_eval(&env).unwrap().as_u64()
    }

    fn occurrences(expression: &SmtExpr) -> usize {
        let mut pending = vec![expression];
        let mut count = 0;
        while let Some(node) = pending.pop() {
            if matches!(node, SmtExpr::Var { name, width: 64 } if name == "x1") {
                count += 1;
            }
            node.for_each_child(&mut |child| pending.push(child));
        }
        count
    }

    #[test]
    fn all_mov_register_fields_keep_full_w_x_values_and_nonaliases_delegate() {
        for sf in 0..=1 {
            for rm in 0..32 {
                for rd in 0..32 {
                    let raw = (sf << 31) | 0x2a00_03e0 | (rm << 16) | rd;
                    let word = decode_a64_value_word(raw).unwrap();
                    let generic = denote_a64_value_word(&word, &FieldOverrides::default()).unwrap();
                    let compact =
                        denote_a64_value_word_compact(&word, &FieldOverrides::default()).unwrap();
                    assert_eq!(compact.dest, generic.dest);
                    assert!(!compact.writes_nzcv);
                    assert_eq!(compact.value.bv_width(), 64);
                    for input in [
                        0,
                        1,
                        u64::MAX,
                        0x8000_0000_0000_0000,
                        0x0123_4567_89ab_cdef,
                        0xffff_ffff_0000_0001,
                    ] {
                        let mut env = EvalEnv::default();
                        if rm != 31 {
                            env.insert(format!("x{rm}"), input);
                        }
                        let expected = if rm == 31 {
                            0
                        } else if sf == 0 {
                            u64::from(input as u32)
                        } else {
                            input
                        };
                        assert_eq!(generic.value.try_eval(&env).unwrap().as_u64(), expected);
                        assert_eq!(compact.value.try_eval(&env).unwrap().as_u64(), expected);
                    }
                    // Every alias-defining field has an independent changed
                    // encoding: source Rn, inversion, shift kind/amount, opcode.
                    for changed in [
                        raw & !(31 << 5),
                        raw | (1 << 21),
                        raw | (1 << 22),
                        raw | (1 << 10),
                        raw ^ (1 << 29),
                    ] {
                        let other = decode_a64_value_word(changed).unwrap();
                        assert_eq!(
                            denote_a64_value_word_compact(&other, &FieldOverrides::default())
                                .unwrap(),
                            denote_a64_value_word(&other, &FieldOverrides::default()).unwrap()
                        );
                    }
                }
            }
        }
        for (sf, rm, rd) in [(2, 1, 0), (1, 32, 0), (1, 1, 32)] {
            let word = A64ValueWord::LogicalShiftedReg {
                sf,
                opc: 1,
                shift: 0,
                n: 0,
                rm,
                imm6: 0,
                rn: 31,
                rd,
            };
            assert!(denote_a64_value_word_compact(&word, &FieldOverrides::default()).is_err());
        }
    }

    #[test]
    fn all_asr_fields_match_raw_bitfield_and_host_shift_full_w_x_results() {
        let mut random = 0x6a09_e667_f3bc_c909u64;
        for sf in 0..=1 {
            let width = 32 << sf;
            for amount in 0..width {
                for (rn, rd) in [(1, 0), (1, 1), (31, 0), (1, 31), (31, 31)] {
                    let word = decode_a64_value_word(asr(sf, amount, rn, rd)).unwrap();
                    let generic = denote_a64_value_word(&word, &FieldOverrides::default()).unwrap();
                    let compact =
                        denote_a64_value_word_compact(&word, &FieldOverrides::default()).unwrap();
                    assert_eq!(
                        compact.dest,
                        if rd == 31 {
                            A64Dest::Discarded
                        } else {
                            A64Dest::Gpr(rd as u8)
                        }
                    );
                    assert_eq!(compact.dest, generic.dest);
                    assert!(!compact.writes_nzcv);
                    assert_eq!(compact.value.bv_width(), 64);
                    let mut samples = vec![
                        0,
                        1,
                        u64::MAX,
                        1u64 << (width - 1),
                        (1u64 << (width - 1)) - 1,
                        0x5555_5555_5555_5555,
                        0xaaaa_aaaa_aaaa_aaaa,
                        0x0123_4567_89ab_cdef,
                        0x8000_0000_8000_0000,
                    ];
                    for _ in 0..8 {
                        random = random
                            .wrapping_mul(6_364_136_223_846_793_005)
                            .wrapping_add(1_442_695_040_888_963_407);
                        samples.push(random ^ (random >> 29));
                    }
                    for input in samples {
                        let source = if rn == 31 { 0 } else { input };
                        let expected = if sf == 0 {
                            ((source as u32 as i32 >> amount) as u32) as u64
                        } else {
                            (source as i64 >> amount) as u64
                        };
                        assert_eq!(
                            evaluate(&generic.value, input),
                            expected,
                            "raw bitfield {sf}/{amount}/{rn}/{rd}/{input:#x}"
                        );
                        assert_eq!(
                            evaluate(&compact.value, input),
                            expected,
                            "compact ASR {sf}/{amount}/{rn}/{rd}/{input:#x}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn fixed_alias_uses_one_source_copy_without_replacing_old_ast() {
        for sf in 0..=1 {
            for amount in [0, 1, (32 << sf) - 1] {
                let word = decode_a64_value_word(asr(sf, amount, 1, 0)).unwrap();
                let generic = denote_a64_value_word(&word, &FieldOverrides::default()).unwrap();
                let compact =
                    denote_a64_value_word_compact(&word, &FieldOverrides::default()).unwrap();
                assert_eq!(
                    occurrences(&generic.value),
                    3,
                    "original registered denotation retained"
                );
                assert_eq!(
                    occurrences(&compact.value),
                    1,
                    "only the new API is compact"
                );
                assert_ne!(generic.value, compact.value);
            }
        }
    }

    #[test]
    fn symbolic_overrides_and_nonalias_rows_keep_exact_old_expression_identity() {
        for sf in 0..=1 {
            let word = decode_a64_value_word(asr(sf, 3, 1, 0)).unwrap();
            for fields in [
                FieldOverrides {
                    immr: Some(SmtExpr::var("r", 6)),
                    ..Default::default()
                },
                FieldOverrides {
                    imms: Some(SmtExpr::var("s", 6)),
                    ..Default::default()
                },
                FieldOverrides {
                    immr: Some(SmtExpr::var("r", 6)),
                    imms: Some(SmtExpr::var("s", 6)),
                    ..Default::default()
                },
            ] {
                let original = denote_a64_value_word(&word, &fields).unwrap();
                let forwarded = denote_a64_value_word_compact(&word, &fields).unwrap();
                assert_eq!(forwarded, original);
                assert_eq!(
                    forwarded.value.to_smt2_expr(),
                    original.value.to_smt2_expr()
                );
            }
        }
        for raw in [
            asr(1, 3, 1, 0) | (1 << 29),                 // BFM, not the ASR alias.
            asr(1, 3, 1, 0) | (2 << 29),                 // UBFM/LSR is not specialized here.
            (asr(1, 3, 1, 0) & !(63 << 10)) | (5 << 10), // Nonalias SBFM.
            0x9240_0c20,
            0xf2c2_4680,
            0xcb02_0020,
        ] {
            let word = decode_a64_value_word(raw).unwrap();
            assert_eq!(
                denote_a64_value_word_compact(&word, &FieldOverrides::default()).unwrap(),
                denote_a64_value_word(&word, &FieldOverrides::default()).unwrap()
            );
        }
    }

    #[test]
    fn malformed_manual_sbfm_fields_refuse_before_specialization_or_delegation() {
        for (sf, n, r, s, rn, rd) in [
            (2, 2, 0, 63, 1, 0),
            (1, 0, 0, 63, 1, 0),
            (0, 1, 0, 31, 1, 0),
            (1, 1, 64, 63, 1, 0),
            (0, 0, 32, 31, 1, 0),
            (1, 1, 0, 64, 1, 0),
            (0, 0, 0, 32, 1, 0),
            (1, 1, 0, 63, 32, 0),
            (1, 1, 0, 63, 1, 32),
        ] {
            let word = A64ValueWord::Bitfield {
                sf,
                opc: 0,
                n,
                immr: r,
                imms: s,
                rn,
                rd,
            };
            for fields in [
                FieldOverrides::default(),
                FieldOverrides {
                    immr: Some(SmtExpr::var("r", 6)),
                    ..Default::default()
                },
            ] {
                assert_eq!(
                    denote_a64_value_word_compact(&word, &fields).unwrap_err(),
                    A64DenoteRefusal::UnmodeledInstruction("invalid decoded SBFM fields")
                );
            }
        }
    }
}
