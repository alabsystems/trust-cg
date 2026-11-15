// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Tests for the word-bound NEON lane-effect decomposition: re-derived words
//! against clang-assembled words, every part holding (and decided exactly)
//! for every admitted shape of a sweep, the corruption controls that must
//! refute and WHICH part refutes each, every single-bit flip refuting, the
//! exact decision agreeing with the evaluator, the checker-friendly term
//! vocabulary, and the refused shapes. Testing evidence about this module,
//! not a proof of it.

use super::*;
use crate::smt::SmtExpr;
use trust_cg_ir::MachOperand;
use trust_cg_ir::regs::{PReg, SpecialReg};

fn x(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(n))
}
fn w(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(32 + n))
}
fn q(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(64 + n))
}
fn d(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(96 + n))
}
fn s(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(128 + n))
}
fn wzr() -> MachOperand {
    MachOperand::Special(SpecialReg::WZR)
}
fn imm(value: i64) -> MachOperand {
    MachOperand::Imm(value)
}
fn inst(opcode: O, operands: Vec<MachOperand>) -> MachInst {
    MachInst::new(opcode, operands)
}
fn config() -> VerificationConfig {
    VerificationConfig {
        sample_count: 2048,
        ..VerificationConfig::default()
    }
}

/// Words assembled by `clang -c -target arm64-apple-macos` (read back with
/// `otool -tvj`) for the listed instructions.
fn assembler_rows() -> Vec<(MachInst, u32)> {
    vec![
        (
            inst(O::NeonDupElem, vec![q(2), q(0), imm(3), imm(4)]),
            0x4e1c_0402,
        ),
        (
            inst(O::NeonDupElem, vec![d(2), q(0), imm(9), imm(1)]),
            0x0e13_0402,
        ),
        (
            inst(O::NeonDupElem, vec![q(5), q(17), imm(1), imm(8)]),
            0x4e18_0625,
        ),
        (inst(O::NeonDupGen, vec![q(1), w(3), imm(1)]), 0x4e01_0c61),
        (inst(O::NeonDupGen, vec![d(2), wzr(), imm(4)]), 0x0e04_0fe2),
        (inst(O::NeonDupGen, vec![q(6), x(30), imm(8)]), 0x4e08_0fc6),
        (
            inst(O::NeonInsGen, vec![q(4), w(9), imm(5), imm(2)]),
            0x4e16_1d24,
        ),
        (
            inst(O::NeonInsGen, vec![q(4), x(2), imm(1), imm(8)]),
            0x4e18_1c44,
        ),
        (
            inst(O::NeonUmovGen, vec![w(10), q(0), imm(7), imm(1)]),
            0x0e0f_3c0a,
        ),
        (
            inst(O::NeonUmovGen, vec![w(10), q(0), imm(3), imm(2)]),
            0x0e0e_3c0a,
        ),
        (
            inst(O::NeonUmovGen, vec![w(10), q(31), imm(2), imm(4)]),
            0x0e14_3fea,
        ),
        (
            inst(O::NeonUmovGen, vec![x(10), q(0), imm(1), imm(8)]),
            0x4e18_3c0a,
        ),
        (
            inst(O::NeonDupScalarD, vec![d(2), q(0), imm(1)]),
            0x5e18_0402,
        ),
        (inst(O::NeonUmaxv, vec![s(2), q(0), imm(5)]), 0x6eb0_a802),
        (
            inst(O::NeonAddpScalar, vec![d(2), q(0), imm(6)]),
            0x5ef1_b802,
        ),
        (inst(O::NeonRev32V, vec![q(2), q(0), imm(1)]), 0x6e20_0802),
        (inst(O::NeonRev32V, vec![q(2), q(0), imm(0)]), 0x2e20_0802),
        (inst(O::NeonRev64V, vec![q(2), q(0), imm(1)]), 0x4e20_0802),
        (inst(O::NeonRev64V, vec![q(2), q(0), imm(5)]), 0x4ea0_0802),
        (inst(O::NeonRev64V, vec![q(2), q(0), imm(0)]), 0x0e20_0802),
        (inst(O::NeonRbitV, vec![q(2), q(0), imm(1)]), 0x6e60_5802),
        (inst(O::NeonRbitV, vec![q(2), q(0), imm(0)]), 0x2e60_5802),
        (
            inst(O::NeonExtV, vec![q(2), q(0), q(1), imm(4)]),
            0x6e01_2002,
        ),
        (
            inst(O::NeonExtV, vec![q(2), q(0), q(1), imm(15)]),
            0x6e01_7802,
        ),
        (inst(O::NeonMovi, vec![q(2), imm(0xa5)]), 0x4f05_e4a2),
        (inst(O::NeonMovi, vec![d(2), imm(0xff)]), 0x0f07_e7e2),
    ]
}

fn assert_every_part_holds_exactly(decomposition: &NeonLaneEffectDecomposition) {
    for part in &decomposition.parts {
        match decide_in_process(part, &config()) {
            InProcess::Holds(VerificationStrength::Exhaustive) => {}
            other => panic!("{}: {other:?}", part.obligation.name),
        }
        assert!(!needs_sampling(part), "{}", part.obligation.name);
    }
}

#[test]
fn rederived_words_are_clangs_and_every_part_holds_exactly() {
    let rows = assembler_rows();
    let opcodes: std::collections::BTreeSet<String> = rows
        .iter()
        .map(|(instruction, _)| format!("{:?}", instruction.opcode))
        .collect();
    assert_eq!(opcodes.len(), NEON_LANE_EFFECT_OPCODES.len());
    for (instruction, expected) in rows {
        assert_eq!(
            neon_lane_effect_word(&instruction),
            Some(expected),
            "{instruction:?}"
        );
        let decomposition = neon_lane_effect(&instruction).expect("admitted");
        assert_eq!(decomposition.word, expected);
        assert_every_part_holds_exactly(&decomposition);
        assert_eq!(
            check_emitted_neon_lane_effect_word(&instruction, expected),
            Some(Ok(()))
        );
        assert!(matches!(
            check_emitted_neon_lane_effect_word(&instruction, expected ^ 1),
            Some(Err(_))
        ));
    }
}

#[test]
fn the_part_inventory_of_each_class() {
    let names = |instruction: MachInst| -> Vec<String> {
        neon_lane_effect(&instruction)
            .unwrap()
            .parts
            .iter()
            .map(|part| part.part.to_string())
            .collect()
    };
    assert_eq!(
        names(inst(O::NeonDupElem, vec![q(2), q(0), imm(3), imm(4)])),
        ["fields", "half 0", "half 1"]
    );
    assert_eq!(
        names(inst(O::NeonUmovGen, vec![w(10), q(0), imm(7), imm(1)])),
        ["fields", "gpr"]
    );
    assert_eq!(
        names(inst(O::NeonUmaxv, vec![s(2), q(0), imm(5)])),
        ["fields", "half 0"]
    );
}

/// Every admitted shape across element sizes, lanes, arrangements, EXT byte
/// indices and MOVI immediates: the word decomposes and every part holds,
/// decided exactly.
#[test]
fn every_admitted_shape_of_a_sweep_holds_exactly() {
    let mut shapes = Vec::new();
    for (bytes, lanes) in [(1i64, 16i64), (2, 8), (4, 4), (8, 2)] {
        for lane in 0..lanes {
            shapes.push(inst(
                O::NeonDupElem,
                vec![q(3), q(7), imm(lane), imm(bytes)],
            ));
            if bytes < 8 {
                shapes.push(inst(
                    O::NeonDupElem,
                    vec![d(3), q(7), imm(lane), imm(bytes)],
                ));
            }
            let gpr = if bytes == 8 { x(9) } else { w(9) };
            shapes.push(inst(O::NeonInsGen, vec![q(3), gpr, imm(lane), imm(bytes)]));
            let dest = if bytes == 8 { x(10) } else { w(10) };
            shapes.push(inst(
                O::NeonUmovGen,
                vec![dest, q(7), imm(lane), imm(bytes)],
            ));
        }
        let gpr = if bytes == 8 { x(9) } else { w(9) };
        shapes.push(inst(O::NeonDupGen, vec![q(3), gpr.clone(), imm(bytes)]));
        if bytes < 8 {
            shapes.push(inst(O::NeonDupGen, vec![d(3), gpr, imm(bytes)]));
        }
    }
    for lane in 0..2 {
        shapes.push(inst(O::NeonDupScalarD, vec![d(3), q(7), imm(lane)]));
    }
    for selector in 0..=6 {
        for opcode in [O::NeonRev32V, O::NeonRev64V, O::NeonRbitV] {
            shapes.push(inst(opcode, vec![q(3), q(7), imm(selector)]));
        }
    }
    for index in 0..16 {
        shapes.push(inst(O::NeonExtV, vec![q(3), q(7), q(8), imm(index)]));
    }
    for byte in [0, 1, 0x5a, 0x80, 0xff] {
        shapes.push(inst(O::NeonMovi, vec![q(3), imm(byte)]));
        shapes.push(inst(O::NeonMovi, vec![d(3), imm(byte)]));
    }
    shapes.push(inst(O::NeonUmaxv, vec![s(3), q(7), imm(5)]));
    shapes.push(inst(O::NeonAddpScalar, vec![d(3), q(7), imm(6)]));
    let mut admitted = 0;
    for shape in shapes {
        let Some(decomposition) = neon_lane_effect(&shape) else {
            continue;
        };
        assert_every_part_holds_exactly(&decomposition);
        admitted += 1;
    }
    // 30 Q=1 DUP element + 28 Q=0 + 30 INS + 30 UMOV + 7 DUP general, 2 DUP
    // scalar, 8 REV/RBIT forms (REV32 and RBIT at 8B/16B; REV64 at 8B, 16B,
    // 2S and 4S, as ENC-5 admits, though nothing emits .2S), 16 EXT, 10
    // MOVI, UMAXV, ADDP.
    assert_eq!(admitted, 163);
}

/// The parts that refute a mutated word, by name.
fn refuted_parts(instruction: &MachInst, word: u32) -> Vec<String> {
    neon_lane_effect_for_word(instruction, word)
        .unwrap()
        .parts
        .iter()
        .filter(|part| matches!(decide_in_process(part, &config()), InProcess::Refuted(_)))
        .map(|part| part.part.to_string())
        .collect()
}

#[test]
fn corrupted_words_refute_in_the_part_that_owns_the_fact() {
    let dup = inst(O::NeonDupElem, vec![q(2), q(0), imm(3), imm(4)]);
    let dup_word = 0x4e1c_0402;
    let ins = inst(O::NeonInsGen, vec![q(4), w(9), imm(5), imm(2)]);
    let ins_word = 0x4e16_1d24;
    let umov = inst(O::NeonUmovGen, vec![w(10), q(0), imm(7), imm(1)]);
    let umov_word = 0x0e0f_3c0a;
    let umaxv = inst(O::NeonUmaxv, vec![s(2), q(0), imm(5)]);
    let umaxv_word = 0x6eb0_a802;
    let addp = inst(O::NeonAddpScalar, vec![d(2), q(0), imm(6)]);
    let addp_word = 0x5ef1_b802;
    let rev32 = inst(O::NeonRev32V, vec![q(2), q(0), imm(1)]);
    let rev32_word = 0x6e20_0802;
    let rbit = inst(O::NeonRbitV, vec![q(2), q(0), imm(1)]);
    let rbit_word = 0x6e60_5802;
    let ext = inst(O::NeonExtV, vec![q(2), q(0), q(1), imm(4)]);
    let ext_word = 0x6e01_2002;
    let movi = inst(O::NeonMovi, vec![q(2), imm(0xa5)]);
    let movi_word = 0x4f05_e4a2;
    let cases: Vec<(&str, &MachInst, u32, &[&str])> = vec![
        // The lane index is the value parts': lane 3 -> lane 1.
        (
            "DUP wrong lane",
            &dup,
            dup_word ^ (1 << 20),
            &["half 0", "half 1"],
        ),
        // The element-size marker is pinned: .S[3] -> .B[...].
        (
            "DUP wrong element size",
            &dup,
            dup_word | (1 << 16),
            &["fields", "half 0", "half 1"],
        ),
        (
            "DUP element as DUP general",
            &dup,
            dup_word | (1 << 11),
            &["fields", "half 0", "half 1"],
        ),
        (
            "DUP .4S as .2S (Q)",
            &dup,
            dup_word & !(1 << 30),
            &["fields", "half 1"],
        ),
        // INS .H[5] -> .H[4]: both in the high half.
        ("INS wrong lane", &ins, ins_word ^ (1 << 18), &["half 1"]),
        // INS .H[5] -> .H[1]: the write moves into the low half.
        (
            "INS lane across halves",
            &ins,
            ins_word ^ (1 << 20),
            &["half 0", "half 1"],
        ),
        (
            "UMOV as SMOV",
            &umov,
            umov_word & !(1 << 12),
            &["fields", "gpr"],
        ),
        ("UMOV wrong lane", &umov, umov_word ^ (1 << 18), &["gpr"]),
        (
            "UMAXV as SMAXV",
            &umaxv,
            umaxv_word & !(1 << 29),
            &["fields", "half 0"],
        ),
        (
            "UMAXV as UMINV",
            &umaxv,
            umaxv_word | (1 << 16),
            &["fields", "half 0"],
        ),
        (
            "UMAXV .4S as .8H",
            &umaxv,
            umaxv_word & !(1 << 23) | (1 << 22),
            &["fields", "half 0"],
        ),
        (
            "ADDP as FADDP",
            &addp,
            addp_word | (1 << 29),
            &["fields", "half 0"],
        ),
        (
            "REV32 as REV64",
            &rev32,
            rev32_word & !(1 << 29),
            &["fields", "half 0", "half 1"],
        ),
        (
            "REV32 .16B as .8B (Q)",
            &rev32,
            rev32_word & !(1 << 30),
            &["fields", "half 1"],
        ),
        (
            "RBIT as NOT",
            &rbit,
            rbit_word & !(1 << 22),
            &["fields", "half 0", "half 1"],
        ),
        // EXT #4 -> #5: imm4 is the value parts'.
        (
            "EXT wrong byte index",
            &ext,
            ext_word ^ (1 << 11),
            &["half 0", "half 1"],
        ),
        // MOVI #0xa5 -> #0xa4: imm8 is the value parts'.
        (
            "MOVI wrong immediate",
            &movi,
            movi_word ^ (1 << 5),
            &["half 0", "half 1"],
        ),
        ("wrong destination", &ext, ext_word ^ 1, &["fields"]),
        ("wrong first source", &dup, dup_word ^ (1 << 5), &["fields"]),
        (
            "wrong second source",
            &ext,
            ext_word ^ (1 << 16),
            &["fields"],
        ),
    ];
    for (label, instruction, word, expected) in cases {
        assert_eq!(
            refuted_parts(instruction, word),
            expected.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
            "{label}: {word:#010x}"
        );
    }
}

/// Every single-bit flip of every assembler word refutes at least one part:
/// every bit is a field `fields` pins or an index or immediate a value part
/// reads.
#[test]
fn every_single_bit_flip_of_every_assembler_word_refutes() {
    for (instruction, word) in assembler_rows() {
        for bit in 0..32 {
            let flipped = word ^ (1 << bit);
            assert!(
                !refuted_parts(&instruction, flipped).is_empty(),
                "{instruction:?}: bit {bit} of {word:#010x} refutes nothing"
            );
        }
    }
}

/// The exact decision never contradicts the evaluator on any single-bit flip
/// of any assembler word.
#[test]
fn the_exact_decision_agrees_with_the_evaluator_on_every_single_bit_flip() {
    for (instruction, word) in assembler_rows() {
        for bit in 0..32 {
            let flipped = word ^ (1 << bit);
            for part in neon_lane_effect_for_word(&instruction, flipped)
                .unwrap()
                .parts
            {
                if part.obligation.inputs.is_empty() {
                    continue;
                }
                let exact = decide_exactly(&part.obligation);
                let sampled = memoized_verify_by_evaluation(&part.obligation, &config());
                match (&exact, &sampled) {
                    (Some(Ok(())), VerificationResult::Invalid { .. })
                    | (Some(Err(_)), VerificationResult::Valid) => panic!(
                        "{instruction:?} bit {bit} {}: exact {exact:?}, sampled {sampled:?}",
                        part.obligation.name
                    ),
                    _ => {}
                }
            }
        }
    }
}

/// The vocabulary of every part: no symbolic shift or multiplication, no
/// array, uninterpreted function, quantifier or `zero_extend`, no variable
/// wider than 64 bits, and no part structurally identical on both sides.
#[test]
fn every_part_stays_in_the_checker_friendly_vocabulary() {
    fn walk(expr: &SmtExpr, bad: &mut Vec<String>) {
        match expr {
            SmtExpr::BvShl { .. }
            | SmtExpr::BvLshr { .. }
            | SmtExpr::BvAshr { .. }
            | SmtExpr::BvMul { .. }
            | SmtExpr::BvUDiv { .. }
            | SmtExpr::BvSDiv { .. }
            | SmtExpr::BvURem { .. }
            | SmtExpr::Select { .. }
            | SmtExpr::Store { .. }
            | SmtExpr::ConstArray { .. }
            | SmtExpr::MemLoad { .. }
            | SmtExpr::UF { .. }
            | SmtExpr::UFDecl { .. }
            | SmtExpr::ForAll { .. }
            | SmtExpr::Exists { .. }
            | SmtExpr::ZeroExtend { .. } => {
                bad.push(format!("{expr:?}").chars().take(60).collect())
            }
            SmtExpr::Var { width, name } if *width > 64 => bad.push(name.clone()),
            _ => {}
        }
        expr.for_each_child(&mut |child| walk(child, bad));
    }
    for (instruction, _) in assembler_rows() {
        for part in neon_lane_effect(&instruction).unwrap().parts {
            let mut bad = Vec::new();
            walk(&part.obligation.trust_ir_expr, &mut bad);
            walk(&part.obligation.aarch64_expr, &mut bad);
            assert!(bad.is_empty(), "{}: {bad:?}", part.obligation.name);
            assert!(!part.obligation.is_degenerate(), "{}", part.obligation.name);
        }
    }
}

#[test]
fn unadmitted_shapes_get_no_decomposition() {
    for instruction in [
        // A scalar-view DUP (element) source (ENC-5 admits it; this module
        // states V sources only).
        inst(O::NeonDupElem, vec![q(2), s(0), imm(0), imm(4)]),
        // .1D is reserved.
        inst(O::NeonDupElem, vec![d(2), q(0), imm(0), imm(8)]),
        inst(O::NeonDupGen, vec![d(2), x(1), imm(8)]),
        // An 8-byte element needs an X source / destination.
        inst(O::NeonDupGen, vec![q(2), w(1), imm(8)]),
        inst(O::NeonUmovGen, vec![w(10), q(0), imm(0), imm(8)]),
        inst(O::NeonUmovGen, vec![x(10), q(0), imm(0), imm(4)]),
        // A lane past the register.
        inst(O::NeonInsGen, vec![q(4), w(9), imm(8), imm(2)]),
        // Arrangements outside each operation.
        inst(O::NeonUmaxv, vec![s(2), q(0), imm(3)]),
        inst(O::NeonAddpScalar, vec![d(2), q(0), imm(5)]),
        inst(O::NeonRev32V, vec![q(2), q(0), imm(5)]),
        inst(O::NeonRbitV, vec![q(2), q(0), imm(3)]),
        // A 16-byte form into a D register.
        inst(O::NeonRev64V, vec![d(2), d(0), imm(1)]),
        inst(O::NeonExtV, vec![q(2), q(0), q(1), imm(16)]),
        inst(O::NeonMovi, vec![q(2), imm(256)]),
    ] {
        assert!(neon_lane_effect(&instruction).is_none(), "{instruction:?}");
        assert!(check_emitted_neon_lane_effect_word(&instruction, 0).is_none());
    }
}

// ---------------------------------------------------------------------------
// The walk's arm
// ---------------------------------------------------------------------------

use crate::function_verifier::{
    FunctionVerifier, InstructionVerificationResult, NEON_LANE_EFFECT_IS_NOT_CREDIT,
};

const LANE_REASON: &str = "the registry arm's uncredited reason";

fn uncredited() -> InstructionVerificationResult {
    InstructionVerificationResult::Unverified {
        reason: LANE_REASON.into(),
    }
}

/// An uncredited row keeps its reason and gains the clause, which says every
/// part held exactly and none is Clean-checked.
#[test]
fn the_check_annotates_an_uncredited_row() {
    let verifier = FunctionVerifier::with_config(config());
    let dup = inst(O::NeonDupElem, vec![q(2), q(0), imm(3), imm(4)]);
    match verifier.with_neon_lane_effect(&dup, uncredited()) {
        InstructionVerificationResult::Unverified { reason } => {
            assert_eq!(
                reason,
                format!(
                    "{LANE_REASON}; {NEON_LANE_EFFECT_IS_NOT_CREDIT}: `A64 NEON lane effect \
                     NeonDupElem 0x4e1c0402` holds in process: all 3 parts exactly; 0 of 3 \
                     parts have a Clean-checked certificate (no live replay lane)"
                )
            );
        }
        other => panic!("{other:?}"),
    }
}

/// A refuted part fails the row, a credited one included; a failed, skipped
/// or unadmitted row is returned unchanged.
#[test]
fn a_refuted_part_fails_the_row_and_other_rows_pass_through() {
    let verifier = FunctionVerifier::with_config(config());
    let umaxv = inst(O::NeonUmaxv, vec![s(2), q(0), imm(5)]);
    let smaxv = neon_lane_effect_for_word(&umaxv, 0x6eb0_a802 & !(1 << 29)).unwrap();
    let credited = InstructionVerificationResult::Verified {
        proof_name: "credited".into(),
        category: crate::proof_database::ProofCategory::NeonLowering,
        strength: VerificationStrength::Formal,
        degenerate: false,
    };
    for row in [credited.clone(), uncredited()] {
        match verifier.with_neon_lane_decomposition(&smaxv, row) {
            InstructionVerificationResult::Failed { proof_name, detail } => {
                assert_eq!(
                    proof_name,
                    "A64 NEON lane effect NeonUmaxv 0x4eb0a802: fields"
                );
                assert!(detail.starts_with("NEON lane-effect part refuted in process: "));
            }
            other => panic!("{other:?}"),
        }
    }
    let own = neon_lane_effect(&umaxv).unwrap();
    assert_eq!(
        format!(
            "{:?}",
            verifier.with_neon_lane_decomposition(&own, credited.clone())
        ),
        format!("{credited:?}")
    );
    let failed = InstructionVerificationResult::Failed {
        proof_name: "x".into(),
        detail: "y".into(),
    };
    assert_eq!(
        format!(
            "{:?}",
            verifier.with_neon_lane_effect(&umaxv, failed.clone())
        ),
        format!("{failed:?}")
    );
    let unadmitted = inst(O::NeonUmaxv, vec![s(2), q(0), imm(3)]);
    assert_eq!(
        format!(
            "{:?}",
            verifier.with_neon_lane_effect(&unadmitted, uncredited())
        ),
        format!("{:?}", uncredited())
    );
}

/// The walk applies the decomposition: in a function verified end to end,
/// every admitted lane-effect row carries the clause (all parts exactly, none
/// credited), and an unadmitted shape of the same opcode does not.
#[test]
fn the_function_walk_annotates_every_admitted_lane_effect_row() {
    use trust_cg_ir::{InstId, MachFunction, function::Signature};
    let rows = assembler_rows();
    let mut function = MachFunction::new(
        "lane_effect_walk".to_string(),
        Signature::new(vec![], vec![]),
    );
    for (index, (instruction, _)) in rows.iter().enumerate() {
        function.insts.push(instruction.clone());
        function.blocks[0].insts.push(InstId(index as u32));
    }
    let report = FunctionVerifier::with_config(config()).verify(&function);
    for (row, (instruction, word)) in report.instructions.iter().zip(&rows) {
        let label = format!(
            "`A64 NEON lane effect {:?} {word:#010x}`",
            instruction.opcode
        );
        match &row.result {
            InstructionVerificationResult::Unverified { reason } => assert!(
                reason.contains(&format!(
                    "{NEON_LANE_EFFECT_IS_NOT_CREDIT}: {label} holds in process: all"
                )) && reason
                    .contains("parts have a Clean-checked certificate (no live replay lane)"),
                "{instruction:?}: {reason}"
            ),
            other => panic!("{instruction:?}: {other:?}"),
        }
    }
    assert_eq!(report.instructions.len(), rows.len());
}
