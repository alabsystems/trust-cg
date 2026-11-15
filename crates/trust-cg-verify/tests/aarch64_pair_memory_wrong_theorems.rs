// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Wrong-theorem negative control for the AArch64 pair-memory obligations
//! (`aarch64_pair_memory_proofs`), run through the discharge the function
//! verifier uses (`discharge_reconstructed_obligation`) at the compiler's
//! configuration (`VerificationConfig::for_proof_promotion`, the default
//! 100,000-sample budget).
//!
//! # Why
//!
//! trust-cg `7af30f92df0849b329a5fe42200e749417e7af3c` (2026-09-15, never on
//! main) measured that the default sampler accepted 93 of 143 deliberately
//! wrong pair theorems of ITS design, which observed memory through a free
//! query byte that uniform sampling almost never places on an accessed slot.
//! `reports/2026-09-29-ref-salvage-evidence.md` and
//! `docs/branch-audit-2026-09-28.md` asked for the same kind of control over
//! main's pair obligations, which probe an enumerated byte set instead. This
//! is that control.
//!
//! # What a wrong theorem is here
//!
//! Main's pair obligation compares the operands' intent with the effect of
//! the instruction's encoded word, decoded independently. A wrong theorem is
//! therefore the obligation built from a DEFECTIVE machine word
//! (`pair_memory_obligation_from_word`): every single-bit corruption of the
//! word, plus the multi-field defects a single bit cannot express (transposed
//! transfer fields, every other addressing mode, every other element width and
//! register bank, the scaled immediate off by one or negated, every other base
//! of the grid). A defective obligation carries the faithful obligation's name
//! by construction, so it is the "wrong theorem under the faithful name" of
//! the 7af30f92 control.
//!
//! Each defect must be REFUSED (no obligation, so no evidence at all) or
//! REFUTED by the evaluation. The one pinned exception is architectural
//! equivalence: with a zero immediate the signed-offset, pre-index and
//! post-index forms have the same effect (the writeback adds zero), so a
//! mode-field change of a zero-offset shape is not a wrong theorem.
//!
//! This is testing evidence about the pair lane's refutation power at the
//! production budget. It credits nothing: sampled pair evidence is reported,
//! never credited (`STATISTICAL_EVIDENCE_IS_NOT_CREDIT`).

use std::collections::BTreeSet;

use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, PReg, SpecialReg};
use trust_cg_verify::aarch64_pair_memory_proofs::{
    decode_pair_memory_word, pair_memory_intent, pair_memory_obligation,
    pair_memory_obligation_from_word, pair_memory_word,
};
use trust_cg_verify::lowering_proof::{VerificationConfig, discharge_reconstructed_obligation};
use trust_cg_verify::verify::VerificationResult;

const PAIR_OPCODES: [AArch64Opcode; 6] = [
    AArch64Opcode::StpRI,
    AArch64Opcode::LdpRI,
    AArch64Opcode::StpPreIndex,
    AArch64Opcode::LdpPostIndex,
    AArch64Opcode::NeonLdpQPost,
    AArch64Opcode::NeonStpQPost,
];

/// `(first register encoding of the bank, element bytes)`: X, W, S, D, Q.
const BANKS: [(u16, i64); 5] = [(0, 8), (32, 4), (128, 4), (96, 8), (64, 16)];

/// Scaled immediates: both extremes of the signed seven-bit field, zero, and
/// its neighbours.
const SCALED_OFFSETS: [i64; 5] = [-64, -1, 0, 1, 63];

fn preg(encoding: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(encoding))
}

/// Base operands: two numbered X registers and SP.
fn bases() -> [MachOperand; 3] {
    [preg(3), preg(29), MachOperand::Special(SpecialReg::SP)]
}

/// Every admitted shape of the grid: 6 opcodes, their banks, 3 bases and 5
/// scaled offsets.
fn grid() -> Vec<MachInst> {
    let mut out = Vec::new();
    for opcode in PAIR_OPCODES {
        let q_only = matches!(
            opcode,
            AArch64Opcode::NeonLdpQPost | AArch64Opcode::NeonStpQPost
        );
        for (bank, element) in BANKS {
            if q_only && bank != 64 {
                continue;
            }
            for base in bases() {
                for scaled in SCALED_OFFSETS {
                    out.push(MachInst::new(
                        opcode,
                        vec![
                            preg(bank + 1),
                            preg(bank + 2),
                            base.clone(),
                            MachOperand::Imm(scaled * element),
                        ],
                    ));
                }
            }
        }
    }
    out
}

/// Every defective word of one faithful `word`, deduplicated, excluding the
/// word itself.
fn defects(word: u32) -> BTreeSet<u32> {
    let mut out = BTreeSet::new();
    // Every single-bit corruption.
    for bit in 0..32 {
        out.insert(word ^ (1 << bit));
    }
    // Transposed transfer fields.
    let rt = word & 0x1f;
    let rt2 = (word >> 10) & 0x1f;
    out.insert((word & !0x7c1f) | (rt << 10) | rt2);
    // Every addressing-mode field, including the non-temporal class.
    for mode in 0..4u32 {
        out.insert((word & !(0b11 << 23)) | (mode << 23));
    }
    // Every (opc, V) element-width and register-bank field.
    for opc in 0..4u32 {
        for v in 0..2u32 {
            out.insert((word & !((0b11 << 30) | (1 << 26))) | (opc << 30) | (v << 26));
        }
    }
    // The scaled immediate off by one either way, and negated.
    let imm7 = (word >> 15) & 0x7f;
    for changed in [
        imm7.wrapping_add(1),
        imm7.wrapping_sub(1),
        imm7.wrapping_neg(),
    ] {
        out.insert((word & !(0x7f << 15)) | ((changed & 0x7f) << 15));
    }
    // Every other base of the grid (X3, X29, SP).
    for rn in [3u32, 29, 31] {
        out.insert((word & !(0x1f << 5)) | (rn << 5));
    }
    out.remove(&word);
    out
}

/// A mode-field-only change of a zero-immediate word between the three
/// allocated pair modes: offset, pre-index and post-index all access `Xn` and
/// leave it unchanged, so the two words have the same architectural effect.
fn architecturally_equivalent(word: u32, defective: u32) -> bool {
    let mode_mask = 0b11 << 23;
    let (Some(faithful), Some(defect)) = (
        decode_pair_memory_word(word),
        decode_pair_memory_word(defective),
    ) else {
        return false;
    };
    (word ^ defective) & !mode_mask == 0 && faithful.offset == 0 && defect.offset == 0
}

#[derive(Default)]
struct Tally {
    shapes: usize,
    defects: usize,
    refused: usize,
    refuted: usize,
    equivalent: usize,
    accepted: Vec<String>,
    undecided: Vec<String>,
}

#[test]
fn every_pair_word_defect_is_refused_or_refuted_at_the_production_budget() {
    let config = VerificationConfig::for_proof_promotion();
    let mut tally = Tally::default();
    for inst in grid() {
        let intent =
            pair_memory_intent(&inst).unwrap_or_else(|| panic!("{inst:?}: grid shape refused"));
        let word = pair_memory_word(&intent).expect("admitted shapes encode");
        let faithful = pair_memory_obligation(&inst).expect("admitted shapes build");
        // The unmutated word must hold, or every refutation below proves
        // nothing.
        let (verdict, _) = discharge_reconstructed_obligation(&faithful, &faithful, &config);
        assert!(
            matches!(verdict, VerificationResult::Valid),
            "{inst:?}: the faithful obligation does not hold: {verdict:?}"
        );
        tally.shapes += 1;
        for defective in defects(word) {
            tally.defects += 1;
            let Some(obligation) = pair_memory_obligation_from_word(&inst, defective) else {
                tally.refused += 1;
                continue;
            };
            assert_eq!(
                obligation.name, faithful.name,
                "a defective obligation must carry the faithful name"
            );
            let (verdict, _) =
                discharge_reconstructed_obligation(&obligation, &obligation, &config);
            match verdict {
                VerificationResult::Invalid { .. } => tally.refuted += 1,
                VerificationResult::Valid if architecturally_equivalent(word, defective) => {
                    tally.equivalent += 1;
                }
                VerificationResult::Valid => tally.accepted.push(format!(
                    "{inst:?}: word {word:#010x} -> defect {defective:#010x} ({:?}) was accepted",
                    decode_pair_memory_word(defective)
                )),
                VerificationResult::Unknown { reason } => tally.undecided.push(format!(
                    "{inst:?}: word {word:#010x} -> defect {defective:#010x}: {reason}"
                )),
            }
        }
    }
    eprintln!(
        "PAIR_WRONG_THEOREMS shapes={} defects={} refused={} refuted={} equivalent={} \
         accepted={} undecided={}",
        tally.shapes,
        tally.defects,
        tally.refused,
        tally.refuted,
        tally.equivalent,
        tally.accepted.len(),
        tally.undecided.len()
    );
    assert!(
        tally.accepted.is_empty(),
        "{} wrong pair theorems were accepted; first 12: {:#?}",
        tally.accepted.len(),
        &tally.accepted[..tally.accepted.len().min(12)]
    );
    assert!(
        tally.undecided.is_empty(),
        "{} wrong pair theorems were undecided; first 12: {:#?}",
        tally.undecided.len(),
        &tally.undecided[..tally.undecided.len().min(12)]
    );
    assert_eq!(tally.shapes, 330, "grid size changed");
    assert_eq!(tally.defects, 13_508, "defect corpus size changed");
    assert_eq!(
        tally.defects,
        tally.refused + tally.refuted + tally.equivalent,
        "every defect is classified"
    );
    // The only exception is the documented one: each of the 66 zero-offset
    // shapes has exactly two equivalent mode spellings.
    assert_eq!(tally.equivalent, 2 * 66, "equivalence exception widened");
    // Measured 2026-09-30. Before bit 25 was checked and same-width bank
    // flips were refused, 570 of these defects (330 bit-25 words, 240 W/S and
    // X/D bank flips) were ACCEPTED and counted in neither column.
    assert_eq!(
        (tally.refused, tally.refuted),
        (6_510, 6_866),
        "refusal/refutation split changed"
    );
}
