// trust-cg-verify/tests/aarch64_value_decode_gate.rs - AArch64 decoded-word value credits against the live encoder
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The AArch64 register-copy, scalar value and half-precision FCVT credits
//! (`MovR`, the typed post-allocation copies `MOVWrr`/`MOVXrr` — register and
//! zero-register sources — `FmovFprFpr`,
//! `FmovFprGpr`, `FmovGprFpr`, `Smull`, `Bfm`, `Rbit`, `AddRIShift12`, `Mrs`,
//! `FcvtHS`, `FcvtHD`, `FcvtSH`, `FcvtDH`, and the `NeonOrrV` register copy
//! `ORR Vd.16B, Vn.16B, Vn.16B`)
//! rest on a CAPTURED corpus of encoder words, because `trust-cg-verify` cannot
//! call the encoder outside tests. This target ties that corpus and the
//! per-instance obligation to the LIVE encoder and to ENC-5:
//!
//! * the corpus is re-derived word for word;
//! * a live sweep encodes every register pair (and every immediate of the
//!   immediate-carrying forms) and requires the per-instance check to accept;
//! * every single-bit corruption of every canonical word must be refuted,
//!   except bits that are semantically neutral for that word, which are
//!   pinned by name;
//! * ENC-5 (`trust-cg-codegen`'s AArch64 decode check) runs the obligation per
//!   emitted word and rejects wrong pairings;
//! * the credit hook accepts every opcode and refuses a surviving control.
//!
//! The sweeps are exhaustive over register fields and over the immediates
//! named, and each accepted word is decided exactly (bit routing) or as an
//! instance of its separately checked form. None of this is a formal proof or
//! a silicon differential.

use std::collections::BTreeMap;

use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, PReg, SpecialReg};
use trust_cg_verify::aarch64_value_decode_proofs::{
    A64ControlMutation, A64RefusalClass, A64ValueCheckError, A64ValueControl, A64ValueForm,
    CAPTURED_A64_VALUE_WORDS, TPIDR_EL0_KEY, a64_value_controls, a64_value_credit,
    a64_value_credit_with, check_emitted_a64_value_word,
};
use trust_cg_verify::lowering_proof::VerificationConfig;

#[path = "support/a64_value_live_encode.rs"]
mod live;

fn x(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(n))
}

fn w(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(32 + n))
}

fn d(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(96 + n))
}

fn s(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(128 + n))
}

fn h(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(165 + n))
}

fn q(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(64 + n))
}

fn imm(value: i64) -> MachOperand {
    MachOperand::Imm(value)
}

fn special(reg: SpecialReg) -> MachOperand {
    MachOperand::Special(reg)
}

fn inst(opcode: AArch64Opcode, operands: Vec<MachOperand>) -> MachInst {
    MachInst::new(opcode, operands)
}

const DECODED_VALUE_OPCODES: [AArch64Opcode; 16] = [
    AArch64Opcode::MovR,
    AArch64Opcode::MOVWrr,
    AArch64Opcode::MOVXrr,
    AArch64Opcode::FmovFprFpr,
    AArch64Opcode::FmovFprGpr,
    AArch64Opcode::FmovGprFpr,
    AArch64Opcode::NeonOrrV,
    AArch64Opcode::Smull,
    AArch64Opcode::Bfm,
    AArch64Opcode::Rbit,
    AArch64Opcode::AddRIShift12,
    AArch64Opcode::Mrs,
    AArch64Opcode::FcvtHS,
    AArch64Opcode::FcvtHD,
    AArch64Opcode::FcvtSH,
    AArch64Opcode::FcvtDH,
];

#[test]
fn corpus_is_what_the_live_encoder_emits_today() {
    let checked = live::assert_a64_value_corpus_is_what_the_live_encoder_emits();
    assert_eq!(checked, CAPTURED_A64_VALUE_WORDS.len());
    for &form in A64ValueForm::ALL {
        assert!(form.canonical().is_some(), "{form:?} has no captured word");
    }
}

/// Encode `inst` with the live encoder and require the per-instance check to
/// accept the word.
fn accept(counts: &mut BTreeMap<&'static str, usize>, label: &'static str, inst: MachInst) {
    let word = encode_instruction(&inst)
        .unwrap_or_else(|error| panic!("live encoder refused {inst:?}: {error:?}"));
    if let Err(error) = check_emitted_a64_value_word(&inst, word) {
        panic!("{label}: {inst:?} = {word:#010x} rejected: {error}");
    }
    *counts.entry(label).or_default() += 1;
}

#[test]
fn live_sweep_holds_for_every_register_and_immediate() {
    use AArch64Opcode as O;
    let mut counts = BTreeMap::new();
    let xzr = MachOperand::PReg(PReg::new(160));
    let wzr = MachOperand::PReg(PReg::new(161));
    for a in 0..31u16 {
        // Zero-register sources in the physical spelling ISel uses (the
        // Special spelling is swept below), and the typed copies from ZR.
        accept(
            &mut counts,
            "MOV Rd, ZR (physical ZR)",
            inst(O::MovR, vec![w(a), wzr.clone()]),
        );
        accept(
            &mut counts,
            "MOV Rd, ZR (physical ZR)",
            inst(O::MovR, vec![x(a), xzr.clone()]),
        );
        accept(
            &mut counts,
            "MOVWrr/MOVXrr Rd, ZR",
            inst(O::MOVWrr, vec![w(a), wzr.clone()]),
        );
        accept(
            &mut counts,
            "MOVWrr/MOVXrr Rd, ZR",
            inst(O::MOVXrr, vec![x(a), xzr.clone()]),
        );
    }
    for a in 0..31u16 {
        for b in 0..31u16 {
            accept(&mut counts, "MOV Wd, Wn", inst(O::MovR, vec![w(a), w(b)]));
            accept(&mut counts, "MOV Xd, Xn", inst(O::MovR, vec![x(a), x(b)]));
            // The typed post-allocation copies, over both operand views: the
            // opcode, not the view, fixes the width.
            accept(
                &mut counts,
                "MOVWrr Wd, Wn",
                inst(O::MOVWrr, vec![w(a), w(b)]),
            );
            accept(
                &mut counts,
                "MOVWrr, X views",
                inst(O::MOVWrr, vec![x(a), x(b)]),
            );
            accept(
                &mut counts,
                "MOVXrr Xd, Xn",
                inst(O::MOVXrr, vec![x(a), x(b)]),
            );
            accept(
                &mut counts,
                "MOVXrr, W views",
                inst(O::MOVXrr, vec![w(a), w(b)]),
            );
            accept(&mut counts, "RBIT W", inst(O::Rbit, vec![w(a), w(b)]));
            accept(&mut counts, "RBIT X", inst(O::Rbit, vec![x(a), x(b)]));
            for m in 0..31u16 {
                accept(&mut counts, "SMULL", inst(O::Smull, vec![x(a), w(b), w(m)]));
            }
        }
        accept(
            &mut counts,
            "MOV Xd, SP",
            inst(O::MovR, vec![x(a), special(SpecialReg::SP)]),
        );
        accept(
            &mut counts,
            "MOV Xd, SP (physical)",
            inst(O::MovR, vec![x(a), x(31)]),
        );
        accept(
            &mut counts,
            "MOV SP, Xn",
            inst(O::MovR, vec![special(SpecialReg::SP), x(a)]),
        );
        accept(
            &mut counts,
            "MOV Xd, XZR",
            inst(O::MovR, vec![x(a), special(SpecialReg::XZR)]),
        );
        accept(
            &mut counts,
            "MOV Wd, WZR",
            inst(O::MovR, vec![w(a), special(SpecialReg::WZR)]),
        );
        accept(
            &mut counts,
            "MRS Xt, TPIDR_EL0",
            inst(O::Mrs, vec![x(a), imm(i64::from(TPIDR_EL0_KEY))]),
        );
    }
    accept(
        &mut counts,
        "MRS XZR, TPIDR_EL0",
        inst(
            O::Mrs,
            vec![special(SpecialReg::XZR), imm(i64::from(TPIDR_EL0_KEY))],
        ),
    );
    for a in 0..32u16 {
        for b in 0..32u16 {
            accept(
                &mut counts,
                "FMOV Sd, Sn",
                inst(O::FmovFprFpr, vec![s(a), s(b)]),
            );
            accept(
                &mut counts,
                "FMOV Dd, Dn",
                inst(O::FmovFprFpr, vec![d(a), d(b)]),
            );
        }
    }
    for g in 0..31u16 {
        for f in 0..32u16 {
            accept(
                &mut counts,
                "FMOV Wd, Sn",
                inst(O::FmovFprGpr, vec![w(g), s(f)]),
            );
            accept(
                &mut counts,
                "FMOV Xd, Dn",
                inst(O::FmovFprGpr, vec![x(g), d(f)]),
            );
            accept(
                &mut counts,
                "FMOV Wd, Hn",
                inst(O::FmovFprGpr, vec![w(g), h(f)]),
            );
            accept(
                &mut counts,
                "FMOV Xd, Hn",
                inst(O::FmovFprGpr, vec![x(g), h(f)]),
            );
            accept(
                &mut counts,
                "FMOV Sd, Wn",
                inst(O::FmovGprFpr, vec![s(f), w(g)]),
            );
            accept(
                &mut counts,
                "FMOV Dd, Xn",
                inst(O::FmovGprFpr, vec![d(f), x(g)]),
            );
            accept(
                &mut counts,
                "FMOV Hd, Wn",
                inst(O::FmovGprFpr, vec![h(f), w(g)]),
            );
            accept(
                &mut counts,
                "FMOV Hd, Xn",
                inst(O::FmovGprFpr, vec![h(f), x(g)]),
            );
        }
    }
    // FCVT between binary16 and binary32/binary64: every register pair.
    for a in 0..32u16 {
        for b in 0..32u16 {
            accept(
                &mut counts,
                "FCVT Sd, Hn",
                inst(O::FcvtHS, vec![s(a), h(b)]),
            );
            accept(
                &mut counts,
                "FCVT Dd, Hn",
                inst(O::FcvtHD, vec![d(a), h(b)]),
            );
            accept(
                &mut counts,
                "FCVT Hd, Sn",
                inst(O::FcvtSH, vec![h(a), s(b)]),
            );
            accept(
                &mut counts,
                "FCVT Hd, Dn",
                inst(O::FcvtDH, vec![h(a), d(b)]),
            );
        }
    }
    // ORR (vector) register copies: the 16B copy of a Q, D, S or H value
    // (the D/S/H copies carry the full-width selector), and the 8B copy of a
    // D value with no selector, which zeroes the upper half. Every register
    // pair.
    for a in 0..32u16 {
        for b in 0..32u16 {
            accept(
                &mut counts,
                "ORR Vd.16B, Vn.16B, Vn.16B (Q)",
                inst(O::NeonOrrV, vec![q(a), q(b), q(b)]),
            );
            for (label, reg) in [
                (
                    "ORR Vd.16B, Vn.16B, Vn.16B (D, #1)",
                    d as fn(u16) -> MachOperand,
                ),
                ("ORR Vd.16B, Vn.16B, Vn.16B (S, #1)", s),
                ("ORR Vd.16B, Vn.16B, Vn.16B (H, #1)", h),
            ] {
                accept(
                    &mut counts,
                    label,
                    inst(O::NeonOrrV, vec![reg(a), reg(b), reg(b), imm(1)]),
                );
            }
            accept(
                &mut counts,
                "ORR Vd.8B, Vn.8B, Vn.8B (D)",
                inst(O::NeonOrrV, vec![d(a), d(b), d(b)]),
            );
        }
    }
    for f in 0..32u16 {
        accept(
            &mut counts,
            "FMOV Dd, XZR",
            inst(O::FmovGprFpr, vec![d(f), special(SpecialReg::XZR)]),
        );
        accept(
            &mut counts,
            "FMOV XZR, Dn",
            inst(O::FmovFprGpr, vec![special(SpecialReg::XZR), d(f)]),
        );
    }
    // BFM: every bitfield-insert (lsb, width) at both widths, and every
    // register pair for one field.
    for (datasize, reg) in [(32u32, w as fn(u16) -> MachOperand), (64, x)] {
        for lsb in 0..datasize {
            for width in 1..=datasize - lsb {
                let immr = i64::from((datasize - lsb) % datasize);
                let imms = i64::from(width - 1);
                accept(
                    &mut counts,
                    "BFM insert, every field",
                    inst(O::Bfm, vec![reg(3), reg(7), imm(immr), imm(imms)]),
                );
            }
        }
        for a in 0..31u16 {
            for b in 0..31u16 {
                accept(
                    &mut counts,
                    "BFM insert, every register pair",
                    inst(O::Bfm, vec![reg(a), reg(b), imm(1), imm(0)]),
                );
            }
        }
    }
    // ADD #imm12, LSL #12: every imm12 at both widths; every register pair,
    // SP included, at the boundary immediates.
    for imm12 in 0..=4095 {
        accept(
            &mut counts,
            "ADD W, LSL #12, every imm12",
            inst(O::AddRIShift12, vec![w(3), w(7), imm(imm12)]),
        );
        accept(
            &mut counts,
            "ADD X, LSL #12, every imm12",
            inst(O::AddRIShift12, vec![x(3), x(7), imm(imm12)]),
        );
    }
    let x_or_sp = |n: u16| {
        if n == 31 {
            special(SpecialReg::SP)
        } else {
            x(n)
        }
    };
    for a in 0..32u16 {
        for b in 0..32u16 {
            for imm12 in [0, 1, 0xFFF] {
                accept(
                    &mut counts,
                    "ADD X|SP, X|SP, LSL #12, every register pair",
                    inst(O::AddRIShift12, vec![x_or_sp(a), x_or_sp(b), imm(imm12)]),
                );
            }
        }
    }
    let total: usize = counts.values().sum();
    eprintln!("aarch64 decoded-value live sweep: {total} words accepted");
    for (label, count) in &counts {
        eprintln!("  {label}: {count}");
    }
    assert_eq!(counts["SMULL"], 31 * 31 * 31);
    assert_eq!(counts["BFM insert, every field"], 528 + 2080);
    assert_eq!(counts["ADD X, LSL #12, every imm12"], 4096);
    assert_eq!(counts["FCVT Hd, Dn"], 32 * 32);
    assert_eq!(counts["MOVWrr, X views"], 31 * 31);
    assert_eq!(counts["MOVXrr, W views"], 31 * 31);
    assert_eq!(counts["MOV Rd, ZR (physical ZR)"], 2 * 31);
    assert_eq!(counts["MOVWrr/MOVXrr Rd, ZR"], 2 * 31);
    assert_eq!(counts["ORR Vd.16B, Vn.16B, Vn.16B (H, #1)"], 32 * 32);
    assert_eq!(counts["ORR Vd.8B, Vn.8B, Vn.8B (D)"], 32 * 32);
    assert_eq!(total, 72_848, "the sweep's denominator changed");
}

/// Single-bit corruption of every canonical word: refuted, unless the bit is
/// semantically neutral FOR THAT WORD, which must then be named here.
///
/// * MOV and the typed MOVWrr/MOVXrr (ORR alias): bits 23:22 are the shift
///   type; with `imm6 == 0` every shift type (LSL/LSR/ASR/ROR by zero) leaves
///   the source unchanged.
/// * MOV Xd, SP (ADD alias): bit 22 (`sh`) shifts a zero immediate, and bit 30
///   (`op`) turns `ADD #0` into `SUB #0`; both still copy SP.
/// * The zero-source copies (`ORR Rd, ZR, ZR`) write zero whatever the shift
///   type (23:22) or amount (15:10; the W forms' bit 15 makes the word
///   unallocated and is refuted), whether the logical operation is ORR or AND
///   (bit 29; bit 30 gives ANDS, refuted for writing NZCV), and at either width
///   (bit 31: a W zero write clears Xd[63:32], an X zero write is zero).
/// * `FMOV Wd, Hn` / `FMOV Hd, Wn`: bit 31 (`sf`) selects the X register; an H
///   value zero-extends to the same 64 bits, and `FMOV Hd, Xn` reads the same
///   low 16 bits as `FMOV Hd, Wn`.
/// * `ORR Vd.16B, Vn.16B, Vn.16B`: bit 23 turns ORR into AND, and
///   `AND Vn, Vn == Vn` is the same copy. Bit 22 (ORN), bit 29 (BIT, which
///   reads Vd) and bit 30 (the 8B arrangement) are refuted.
#[test]
fn every_single_bit_corruption_is_refuted_or_a_named_neutral_bit() {
    let expected_neutral: BTreeMap<A64ValueForm, Vec<u32>> = A64ValueForm::ALL
        .iter()
        .map(|&form| {
            let bits = match form {
                A64ValueForm::MovW
                | A64ValueForm::MovX
                | A64ValueForm::MovWrr
                | A64ValueForm::MovXrr => vec![22, 23],
                A64ValueForm::MovXFromSp => vec![22, 30],
                A64ValueForm::MovWFromZr | A64ValueForm::MovWrrFromZr => {
                    vec![10, 11, 12, 13, 14, 22, 23, 29, 31]
                }
                A64ValueForm::MovXFromZr | A64ValueForm::MovXrrFromZr => {
                    vec![10, 11, 12, 13, 14, 15, 22, 23, 29, 31]
                }
                A64ValueForm::FmovWFromH | A64ValueForm::FmovHFromW => vec![31],
                A64ValueForm::MovV16B => vec![23],
                _ => Vec::new(),
            };
            (form, bits)
        })
        .collect();
    let mut refuted_by_class: BTreeMap<String, usize> = BTreeMap::new();
    for &form in A64ValueForm::ALL {
        let canonical = form.canonical().unwrap();
        let instruction = canonical.inst();
        let mut neutral = Vec::new();
        for bit in 0..32 {
            match check_emitted_a64_value_word(&instruction, canonical.word ^ (1 << bit)) {
                Ok(_) => neutral.push(bit),
                Err(A64ValueCheckError::Refuted(refutation)) => {
                    *refuted_by_class
                        .entry(format!("{:?}", refutation.class))
                        .or_default() += 1;
                }
                Err(other) => panic!("{form:?} bit {bit}: unexpected {other}"),
            }
        }
        assert_eq!(
            neutral, expected_neutral[&form],
            "{form:?}: semantically neutral bits of {:#010x}",
            canonical.word
        );
    }
    eprintln!("single-bit corruptions refuted by class: {refuted_by_class:?}");
}

#[test]
fn per_compile_decode_check_runs_the_value_obligation() {
    let enc5 =
        |inst: &MachInst, word: u32| A64DecodeCheck.check_one(inst, &word.to_le_bytes(), None);
    // Live encoder output for every captured instruction is an ENC-5 Match.
    for entry in CAPTURED_A64_VALUE_WORDS {
        let instruction = entry.inst();
        let word = encode_instruction(&instruction).unwrap();
        assert!(
            matches!(enc5(&instruction, word), DecodeCheckOutcome::Match),
            "{instruction:?} = {word:#010x}: {:?}",
            enc5(&instruction, word)
        );
    }
    // Wrong pairings: every one must be rejected BY THE VALUE OBLIGATION.
    let rejected = [
        // The ORR spelling of MOV X3, SP reads XZR. It is exactly what the
        // encoder used to emit for a physical-SP source, and ENC-5's
        // structural MOV arm matched it.
        (inst(AArch64Opcode::MovR, vec![x(3), x(31)]), 0xAA1F_03E3),
        // X-width ORR for a W copy: Xd[63:32] not cleared.
        (inst(AArch64Opcode::MovR, vec![w(3), w(7)]), 0xAA07_03E3),
        // FMOV S3, S7 read as FMOV D3, D7.
        (
            inst(AArch64Opcode::FmovFprFpr, vec![s(3), s(7)]),
            0x1E60_40E3,
        ),
        // FMOV X3, D7 read as FMOV W3, S7.
        (
            inst(AArch64Opcode::FmovFprGpr, vec![x(3), d(7)]),
            0x1E26_00E3,
        ),
        // FMOV D3, X7 read as FMOV X3, D7 (other direction).
        (
            inst(AArch64Opcode::FmovGprFpr, vec![d(3), x(7)]),
            0x9E66_00E3,
        ),
        // UMULL for SMULL.
        (
            inst(AArch64Opcode::Smull, vec![x(3), w(7), w(12)]),
            0x9BAC_7CE3,
        ),
        // UBFM for BFM.
        (
            inst(AArch64Opcode::Bfm, vec![x(3), x(7), imm(56), imm(4)]),
            0xD378_10E3,
        ),
        // RBIT X3, X7 read as REV X3, X7.
        (inst(AArch64Opcode::Rbit, vec![x(3), x(7)]), 0xDAC0_0CE3),
        // ADD X3, X7, #0x123 without the LSL #12.
        (
            inst(AArch64Opcode::AddRIShift12, vec![x(3), x(7), imm(0x123)]),
            0x9104_8CE3,
        ),
        // MRS X3, TPIDRRO_EL0 for TPIDR_EL0.
        (
            inst(
                AArch64Opcode::Mrs,
                vec![x(3), imm(i64::from(TPIDR_EL0_KEY))],
            ),
            0xD53B_D063,
        ),
        // FCVT D3, H7 for FCVT S3, H7: wrong destination format.
        (inst(AArch64Opcode::FcvtHS, vec![s(3), h(7)]), 0x1EE2_C0E3),
        // FCVT S3, H7 for FCVT H3, S7: the opposite direction.
        (inst(AArch64Opcode::FcvtSH, vec![h(3), s(7)]), 0x1EE2_40E3),
        // FCVT H3, S7 for FCVT H3, D7: wrong source format.
        (inst(AArch64Opcode::FcvtDH, vec![h(3), d(7)]), 0x1E23_C0E3),
        // BFCVT H3, S7 (bfloat16) for FCVT H3, S7.
        (inst(AArch64Opcode::FcvtSH, vec![h(3), s(7)]), 0x1E63_40E3),
        // ORR V3.16B, V7.16B, V8.16B for the copy of V7.
        (
            inst(AArch64Opcode::NeonOrrV, vec![q(3), q(7), q(7)]),
            0x4EA8_1CE3,
        ),
        // ORR V3.8B, V7.8B, V7.8B for a full-width D copy: upper half zeroed.
        (
            inst(AArch64Opcode::NeonOrrV, vec![d(3), d(7), d(7), imm(1)]),
            0x0EA7_1CE3,
        ),
        // ORN V3.16B, V7.16B, V7.16B (all ones) for the copy.
        (
            inst(AArch64Opcode::NeonOrrV, vec![q(3), q(7), q(7)]),
            0x4EE7_1CE3,
        ),
    ];
    for (instruction, word) in rejected {
        assert!(
            check_emitted_a64_value_word(&instruction, word).is_err(),
            "{instruction:?} = {word:#010x}"
        );
        match enc5(&instruction, word) {
            DecodeCheckOutcome::Mismatch(error) => assert!(
                format!("{error:?}").contains("aarch64_value_decode_proofs"),
                "{instruction:?}: {error:?}"
            ),
            other => panic!("{instruction:?} = {word:#010x}: expected Mismatch, got {other:?}"),
        }
    }
    // The live encoder now spells a physical-SP source as the ADD alias.
    assert_eq!(
        encode_instruction(&inst(AArch64Opcode::MovR, vec![x(3), x(31)])).unwrap(),
        0x9100_03E3
    );

    // The NEON bitwise ops in their bound 16B shape are field-checked: the
    // live word matches; a word with other registers, another operation or
    // the 8B arrangement is a Mismatch. The 8B shapes, which the function
    // verifier refuses, are decoded field by field by ENC-5's FP/SIMD slice.
    let bitwise = [
        (
            AArch64Opcode::NeonOrrV,
            0x4EA2_1C20,
            vec![0x4EA1_1C40, 0x4E22_1C20, 0x6E22_1C20, 0x0EA2_1C20],
        ),
        (
            AArch64Opcode::NeonAndV,
            0x4E22_1C20,
            vec![0x4E21_1C40, 0x4EA2_1C20, 0x6E22_1C20, 0x0E22_1C20],
        ),
        (
            AArch64Opcode::NeonEorV,
            0x6E22_1C20,
            vec![0x6E21_1C40, 0x4E22_1C20, 0x6E62_1C20, 0x2E22_1C20],
        ),
        (
            AArch64Opcode::NeonBicV,
            0x4E62_1C20,
            vec![0x4E61_1C40, 0x4E22_1C20, 0x4EE2_1C20, 0x0E62_1C20],
        ),
    ];
    for (opcode, live, wrong) in bitwise {
        let bound = inst(opcode, vec![q(0), q(1), q(2)]);
        let word = encode_instruction(&bound).unwrap();
        assert_eq!(word, live, "{opcode:?}");
        assert!(
            matches!(enc5(&bound, word), DecodeCheckOutcome::Match),
            "{opcode:?}"
        );
        for w in wrong {
            match enc5(&bound, w) {
                DecodeCheckOutcome::Mismatch(error) => assert!(
                    format!("{error:?}").contains("does not encode the bound 16B intent"),
                    "{opcode:?} {w:#010x}: {error:?}"
                ),
                other => panic!("{opcode:?} {w:#010x}: expected Mismatch, got {other:?}"),
            }
        }
        // The 8B shape binds no lanewise obligation, but ENC-5's FP/SIMD
        // slice decodes its word field by field (L10-P6): the live word
        // matches and the 16B word of the same registers does not.
        let narrow = inst(opcode, vec![d(0), d(1), d(2)]);
        let narrow_word = encode_instruction(&narrow).unwrap();
        assert!(
            matches!(enc5(&narrow, narrow_word), DecodeCheckOutcome::Match),
            "{opcode:?}"
        );
        assert!(
            matches!(
                enc5(&narrow, narrow_word | 1 << 30),
                DecodeCheckOutcome::Mismatch(_)
            ),
            "{opcode:?}"
        );
    }
    let not = inst(AArch64Opcode::NeonNotV, vec![q(3), q(7)]);
    let word = encode_instruction(&not).unwrap();
    assert_eq!(word, 0x6E20_58E3);
    assert!(matches!(enc5(&not, word), DecodeCheckOutcome::Match));
    for w in [0x2E20_58E3, 0x6E20_58E4, 0x6E20_5903, 0x4E20_58E3] {
        assert!(
            matches!(enc5(&not, w), DecodeCheckOutcome::Mismatch(_)),
            "{w:#010x}"
        );
    }
    let narrow_not = inst(AArch64Opcode::NeonNotV, vec![d(3), d(7)]);
    let narrow_word = encode_instruction(&narrow_not).unwrap();
    assert!(matches!(
        enc5(&narrow_not, narrow_word),
        DecodeCheckOutcome::Match
    ));
    assert!(matches!(
        enc5(&narrow_not, narrow_word | 1 << 30),
        DecodeCheckOutcome::Mismatch(_)
    ));
}

#[test]
fn credit_hook_accepts_every_opcode_and_refuses_a_surviving_control() {
    let mut forms = 0;
    let mut controls = 0;
    for opcode in DECODED_VALUE_OPCODES {
        let credit = a64_value_credit(opcode).unwrap_or_else(|error| panic!("{opcode:?}: {error}"));
        forms += credit.forms;
        controls += credit.controls_refuted;
    }
    assert_eq!(forms, A64ValueForm::ALL.len());
    assert_eq!(controls, a64_value_controls().len());
    let mut battery = a64_value_controls();
    battery.push(A64ValueControl {
        form: A64ValueForm::FmovXFromD,
        label: "identity: must survive",
        mutation: A64ControlMutation::Word(|word| word),
        expected: A64RefusalClass::Value,
    });
    let refused = a64_value_credit_with(
        AArch64Opcode::FmovFprGpr,
        CAPTURED_A64_VALUE_WORDS,
        &battery,
        &VerificationConfig::default(),
    );
    assert!(
        refused
            .as_ref()
            .is_err_and(|error| error.contains("identity: must survive")),
        "{refused:?}"
    );
}
