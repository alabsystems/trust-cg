// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use std::collections::BTreeMap;

use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
use trust_cg_codegen::aarch64::{EncodeError, encode_instruction};
use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
use trust_cg_ir::regs::{D0, W2, W7, WSP, WZR, X2, X7, XZR};
use trust_cg_ir::{AArch64Opcode as Op, MachInst, MachOperand as O, SpecialReg};

const BINARY_OPS: [(Op, u32); 3] = [(Op::AndRI, 0), (Op::OrrRI, 1), (Op::EorRI, 2)];

#[derive(Clone, Copy)]
struct Fields {
    n: u32,
    immr: u32,
    imms: u32,
}

/// Decode an architectural field triple one output bit at a time, without
/// sharing the encoder's run detection, rotation or replication helpers.
fn reference_decode(width: u32, fields: Fields) -> Option<(u64, u32)> {
    let length = ((fields.n << 6) | (!fields.imms & 63)).checked_ilog2()?;
    let element_width = 1 << length;
    let ones = (fields.imms % element_width) + 1;
    if element_width > width || ones == element_width {
        return None;
    }
    let mut mask = 0;
    for bit in 0..width {
        if (bit + fields.immr) % element_width < ones {
            mask |= 1u64 << bit;
        }
    }
    Some((mask, element_width))
}

fn expected_word(width: u32, opc: u32, rd: u32, rn: u32, fields: Fields) -> u32 {
    (u32::from(width == 64) << 31)
        | (opc << 29)
        | 0x1200_0000
        | (fields.n << 22)
        | (fields.immr << 16)
        | (fields.imms << 10)
        | (rn << 5)
        | rd
}

fn actual_inst(op: Op, rd: O, rn: O, mask: i64) -> MachInst {
    let operands = if op == Op::Tst {
        vec![rn, O::Imm(mask)]
    } else {
        vec![rd, rn, O::Imm(mask)]
    };
    MachInst::new(op, operands)
}

fn raw_inst(op: Op, rd: O, rn: O, fields: Fields) -> MachInst {
    MachInst::new(
        op,
        vec![
            rd,
            rn,
            O::Imm(fields.n.into()),
            O::Imm(fields.immr.into()),
            O::Imm(fields.imms.into()),
        ],
    )
}

fn assert_word(inst: &MachInst, expected: u32) {
    let word = encode_instruction(inst).unwrap_or_else(|err| panic!("{inst:?}: {err}"));
    assert_eq!(word, expected, "{inst:?}");
}

fn assert_invalid_operand(inst: &MachInst, index: usize) {
    let got = encode_instruction(inst);
    assert!(
        matches!(got, Err(EncodeError::InvalidOperand { opcode, index: at, .. })
            if opcode == inst.opcode && at == index),
        "{inst:?}: expected invalid operand at {index}, got {got:?}"
    );
}

#[test]
fn raw_fields_and_canonical_masks_match_the_original_search_order() {
    for (width, rd, rn, allocated, distinct) in [(32, W2, W7, 3648, 1302), (64, X2, X7, 7680, 5334)]
    {
        let mut canonical = BTreeMap::new();
        let mut allocated_fields = 0;
        for n in 0..=1 {
            for imms in 0..64 {
                for immr in 0..64 {
                    let fields = Fields { n, immr, imms };
                    // Raw carriers preserve the exact fields, including the
                    // noncanonical aliases and in-range reserved encodings.
                    for (op, opc) in BINARY_OPS {
                        let inst = raw_inst(op, O::PReg(rd), O::PReg(rn), fields);
                        assert_word(&inst, expected_word(width, opc, 2, 7, fields));
                    }

                    let Some((mask, element_width)) = reference_decode(width, fields) else {
                        continue;
                    };
                    allocated_fields += 1;
                    // The original search takes the first element width,
                    // ones count and rotation. At a given width, imms
                    // increases with the ones count. Ignored high bits of
                    // immr cannot win against its smallest alias.
                    let key = (element_width, imms, immr);
                    let best = canonical.entry(mask).or_insert((key, fields));
                    if key < best.0 {
                        *best = (key, fields);
                    }
                }
            }
        }
        assert_eq!(allocated_fields, allocated);
        assert_eq!(canonical.len(), distinct);

        for (mask, (_, fields)) in canonical {
            for (op, opc) in BINARY_OPS.into_iter().chain([(Op::Tst, 3)]) {
                let inst = actual_inst(op, O::PReg(rd), O::PReg(rn), mask as i64);
                let dst = if op == Op::Tst { 31 } else { 2 };
                assert_word(&inst, expected_word(width, opc, dst, 7, fields));
            }
        }
    }
}

#[test]
fn mask_carriers_reject_unencodable_values_and_truncate_to_w_width() {
    for (op, opc) in BINARY_OPS.into_iter().chain([(Op::Tst, 3)]) {
        let index = if op == Op::Tst { 1 } else { 2 };
        for (rd, rn) in [(W2, W7), (X2, X7)] {
            for raw in [0, -1, 5] {
                assert_invalid_operand(&actual_inst(op, O::PReg(rd), O::PReg(rn), raw), index);
            }
        }
        for raw in [0x0123_4567_0000_0000, 0x0123_4567_ffff_ffff] {
            assert_invalid_operand(&actual_inst(op, O::PReg(W2), O::PReg(W7), raw), index);
        }

        // Both carriers name the same wrapped pair of ones in a W register.
        let fields = Fields {
            n: 0,
            immr: 1,
            imms: 1,
        };
        let dst = if op == Op::Tst { 31 } else { 2 };
        for raw in [0x0123_4567_8000_0001, i64::from(i32::MIN) + 1] {
            let inst = actual_inst(op, O::PReg(W2), O::PReg(W7), raw);
            assert_word(&inst, expected_word(32, opc, dst, 7, fields));
        }
    }
}

#[test]
fn logical_register_roles_and_reserved_words_reach_the_live_decode_gate() {
    let fields = Fields {
        n: 0,
        immr: 0,
        imms: 60,
    };
    let mask = 0x5555_5555_5555_5555;
    for (width, sp, zr) in [
        (32, O::PReg(WSP), WZR),
        (64, O::Special(SpecialReg::SP), XZR),
    ] {
        for (op, opc) in BINARY_OPS {
            // Register 31 writes SP in Rd, and reads ZR in Rn.
            let word = expected_word(width, opc, 31, 31, fields);
            for raw in [false, true] {
                let inst = if raw {
                    raw_inst(op, sp.clone(), O::PReg(zr), fields)
                } else {
                    actual_inst(op, sp.clone(), O::PReg(zr), mask)
                };
                assert_word(&inst, word);
                assert!(matches!(
                    A64DecodeCheck.check_one(&inst, &word.to_le_bytes(), None),
                    DecodeCheckOutcome::Match
                ));
                let mut swapped = inst;
                swapped.operands.swap(0, 1);
                assert!(matches!(
                    A64DecodeCheck.check_one(&swapped, &word.to_le_bytes(), None),
                    DecodeCheckOutcome::Mismatch(_)
                ));
            }

            let reserved = Fields {
                n: 1,
                immr: 0,
                imms: if width == 32 { 0 } else { 63 },
            };
            let inst = raw_inst(op, sp.clone(), O::PReg(zr), reserved);
            let word = expected_word(width, opc, 31, 31, reserved);
            assert_word(&inst, word);
            assert!(matches!(
                A64DecodeCheck.check_one(&inst, &word.to_le_bytes(), None),
                DecodeCheckOutcome::Mismatch(_)
            ));
        }

        let inst = MachInst::new(Op::Tst, vec![O::PReg(zr), O::Imm(mask)]);
        let word = expected_word(width, 3, 31, 31, fields);
        assert_word(&inst, word);
        assert!(matches!(
            A64DecodeCheck.check_one(&inst, &word.to_le_bytes(), None),
            DecodeCheckOutcome::Match
        ));
        for bad in [sp, O::PReg(D0)] {
            assert_invalid_operand(&MachInst::new(Op::Tst, vec![bad, O::Imm(mask)]), 0);
        }
        assert_invalid_operand(
            &MachInst::new(Op::Tst, vec![O::PReg(zr), O::Imm(0), O::Imm(0), O::Imm(60)]),
            2,
        );
    }

    let shifted = MachInst::new(Op::Tst, vec![O::PReg(W7), O::PReg(WZR)]);
    assert_word(&shifted, 0x6a1f_00ff);
    let mixed = MachInst::new(Op::Tst, vec![O::PReg(W7), O::PReg(XZR)]);
    assert_invalid_operand(&mixed, 1);
}
