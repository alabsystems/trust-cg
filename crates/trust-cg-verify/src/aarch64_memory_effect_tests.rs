// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Tests for the word-bound memory-effect decomposition: the re-derived words
//! against clang-assembled words, every part holding in process for every
//! admitted shape of a sweep, the corruption controls that must refute (and
//! WHICH part refutes each), the checker-friendly term vocabulary, and the
//! ENC-5 binding. Testing evidence about this module, not a proof of it.

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
fn sp() -> MachOperand {
    MachOperand::Special(SpecialReg::SP)
}
fn xzr() -> MachOperand {
    MachOperand::Special(SpecialReg::XZR)
}
fn imm(value: i64) -> MachOperand {
    MachOperand::Imm(value)
}
fn inst(opcode: O, operands: Vec<MachOperand>) -> MachInst {
    MachInst::new(opcode, operands)
}
fn config() -> VerificationConfig {
    VerificationConfig::default()
}
/// The controls and the sweep sample less: a counterexample to a corrupted
/// word is found within a few samples, and the production sample count is
/// exercised by the assembler rows.
fn control_config() -> VerificationConfig {
    VerificationConfig {
        sample_count: 2048,
        ..VerificationConfig::default()
    }
}

/// Words assembled by clang 17 (`clang -c -target arm64-apple-darwin`, read
/// back with `objdump -d`) for the listed instructions.
fn assembler_rows() -> Vec<(MachInst, u32)> {
    vec![
        (
            inst(O::StpPreIndex, vec![x(29), x(30), sp(), imm(-16)]),
            0xa9bf_7bfd,
        ),
        (
            inst(O::LdpPostIndex, vec![x(29), x(30), sp(), imm(16)]),
            0xa8c1_7bfd,
        ),
        (
            inst(O::StpRI, vec![x(19), x(20), sp(), imm(16)]),
            0xa901_53f3,
        ),
        (
            inst(O::LdpRI, vec![x(19), x(20), sp(), imm(16)]),
            0xa941_53f3,
        ),
        (
            inst(O::NeonStpQPost, vec![q(0), q(1), x(0), imm(32)]),
            0xac81_0400,
        ),
        (
            inst(O::NeonLdpQPost, vec![q(2), q(3), x(1), imm(32)]),
            0xacc1_0c22,
        ),
        (inst(O::StpRI, vec![w(3), w(4), x(5), imm(8)]), 0x2901_10a3),
        (inst(O::LdpRI, vec![w(3), w(4), x(5), imm(-8)]), 0x297f_10a3),
        (
            inst(O::StpPreIndex, vec![d(8), d(9), sp(), imm(-32)]),
            0x6dbe_27e8,
        ),
        (inst(O::LdpRI, vec![s(0), s(1), x(2), imm(4)]), 0x2d40_8440),
        (inst(O::StpRI, vec![xzr(), xzr(), x(0)]), 0xa900_7c1f),
        (inst(O::StpRI, vec![x(7), x(7), x(0), imm(16)]), 0xa901_1c07),
        (inst(O::LdrRI, vec![x(1), x(0), imm(16)]), 0xf940_0801),
        (inst(O::StrRI, vec![x(0), x(1)]), 0xf900_0020),
        (inst(O::StrRI, vec![w(0), x(1)]), 0xb900_0020),
        (inst(O::StrbRI, vec![w(2), x(1), imm(3)]), 0x3900_0c22),
        (inst(O::LdrbRI, vec![w(5), x(6), imm(1)]), 0x3940_04c5),
        (inst(O::LdrhRI, vec![w(5), x(6), imm(2)]), 0x7940_04c5),
        (inst(O::StrhRI, vec![w(9), x(10), imm(6)]), 0x7900_0d49),
        (inst(O::LdrRI, vec![w(2), sp(), imm(68)]), 0xb940_47e2),
        (inst(O::LdrRI, vec![x(0), x(1), imm(-8)]), 0xf85f_8020),
        (inst(O::StrRI, vec![w(3), x(4), imm(-1)]), 0xb81f_f083),
        (inst(O::StrRI, vec![xzr(), sp()]), 0xf900_03ff),
        (inst(O::LdrRI, vec![x(16), sp(), imm(88)]), 0xf940_2ff0),
        // NEON LD1/ST1 one register, immediate post-index (ledger L04-P6).
        (inst(O::NeonLd1Post, vec![q(2), x(9), imm(1)]), 0x4cdf_7122),
        (inst(O::NeonSt1Post, vec![q(2), x(9), imm(0)]), 0x0c9f_7122),
        (inst(O::NeonLd1Post, vec![q(0), x(1), imm(5)]), 0x4cdf_7820),
        (inst(O::NeonSt1Post, vec![q(3), sp(), imm(6)]), 0x4c9f_7fe3),
        (inst(O::NeonLd1Post, vec![d(5), x(2), imm(2)]), 0x0cdf_7445),
        (inst(O::NeonSt1Post, vec![q(7), x(0), imm(3)]), 0x4c9f_7407),
        (
            inst(O::NeonLd1Post, vec![q(31), x(30), imm(4)]),
            0x0cdf_7bdf,
        ),
    ]
}

fn assert_holds_under(decomposition: &MemoryEffectDecomposition, config: &VerificationConfig) {
    for part in &decomposition.parts {
        match decide_in_process(part, config) {
            InProcess::Holds(_) => {}
            other => panic!("{}: {other:?}", part.obligation.name),
        }
    }
}

fn assert_holds(decomposition: &MemoryEffectDecomposition) {
    assert_holds_under(decomposition, &config());
}

#[test]
fn rederived_words_are_clangs_and_every_part_holds() {
    for (instruction, expected) in assembler_rows() {
        assert_eq!(
            memory_effect_word(&instruction),
            Some(expected),
            "{:?}",
            instruction
        );
        let decomposition = memory_effect(&instruction).expect("admitted");
        assert_eq!(decomposition.word, expected);
        assert_holds(&decomposition);
        assert_eq!(
            check_emitted_memory_effect_word(&instruction, expected),
            Some(Ok(()))
        );
        assert!(matches!(
            check_emitted_memory_effect_word(&instruction, expected ^ 1),
            Some(Err(_))
        ));
    }
}

#[test]
fn the_part_inventory_of_each_class() {
    let names = |instruction: MachInst| -> Vec<String> {
        memory_effect(&instruction)
            .unwrap()
            .parts
            .iter()
            .map(|part| part.part.to_string())
            .collect()
    };
    assert_eq!(
        names(inst(O::StpPreIndex, vec![x(29), x(30), sp(), imm(-16)])),
        [
            "fields",
            "address lane 0",
            "address lane 1",
            "writeback",
            "store lane 0 half 0",
            "store lane 1 half 0"
        ]
    );
    assert_eq!(
        names(inst(O::NeonLdpQPost, vec![q(2), q(3), x(1), imm(32)])),
        [
            "fields",
            "address lane 0",
            "address lane 1",
            "writeback",
            "load lane 0 half 0",
            "load lane 0 half 1",
            "load lane 1 half 0",
            "load lane 1 half 1"
        ]
    );
    assert_eq!(
        names(inst(O::LdrRI, vec![x(1), x(0), imm(16)])),
        ["fields", "address lane 0", "load lane 0 half 0"]
    );
    // LD1/ST1 address `X[n]`: the base the fields name, so no address part.
    // A 64-bit transfer states the untouched upper half too.
    assert_eq!(
        names(inst(O::NeonLd1Post, vec![q(2), x(9), imm(1)])),
        [
            "fields",
            "writeback",
            "load lane 0 half 0",
            "load lane 0 half 1"
        ]
    );
    assert_eq!(
        names(inst(O::NeonLd1Post, vec![d(5), x(2), imm(2)])),
        [
            "fields",
            "writeback",
            "load lane 0 half 0",
            "load lane 0 half 1"
        ]
    );
    assert_eq!(
        names(inst(O::NeonSt1Post, vec![q(2), x(9), imm(0)])),
        [
            "fields",
            "writeback",
            "store lane 0 half 0",
            "store lane 0 half 1"
        ]
    );
}

/// Every LD1/ST1 arrangement over register-field boundaries is admitted, its
/// word is the layout mirror's, and every part holds in process.
#[test]
fn every_ld1_st1_post_shape_holds() {
    let mut count = 0;
    for opcode in [O::NeonLd1Post, O::NeonSt1Post] {
        for selector in 0..=6 {
            for (rt, base) in [(q(0), x(0)), (q(31), sp()), (q(17), x(30))] {
                let instruction = inst(opcode, vec![rt, base, imm(selector)]);
                let decomposition = memory_effect(&instruction).expect("admitted");
                assert_holds_under(&decomposition, &control_config());
                count += 1;
            }
        }
    }
    assert_eq!(count, 42);
}

/// LD1/ST1 corruptions refute in the part that owns the fact: the transfer
/// size (Q) in fields, the writeback and the upper half; the direction in
/// fields and the data parts; the element size, the register post-index and
/// the registers in fields; the offset form in fields and the writeback.
#[test]
fn ld1_st1_corruptions_refute_in_the_owning_part() {
    let ld1q = inst(O::NeonLd1Post, vec![q(2), x(9), imm(1)]);
    let ld1q_word = 0x4cdf_7122;
    let st1d = inst(O::NeonSt1Post, vec![q(2), x(9), imm(0)]);
    let st1d_word = 0x0c9f_7122;
    let cases: Vec<(&str, &MachInst, u32, &[&str])> = vec![
        (
            "16-byte load as 8-byte",
            &ld1q,
            ld1q_word & !(1 << 30),
            &["fields", "writeback", "load lane 0 half 1"],
        ),
        (
            "8-byte store as 16-byte",
            &st1d,
            st1d_word | (1 << 30),
            &["fields", "writeback", "store lane 0 half 1"],
        ),
        ("load as store", &ld1q, ld1q_word & !(1 << 22), &["fields"]),
        (
            "element size B as H",
            &ld1q,
            ld1q_word | (1 << 10),
            &["fields"],
        ),
        (
            "immediate post-index as register post-index (Rm = x30)",
            &ld1q,
            ld1q_word & !(1 << 16),
            &["fields"],
        ),
        (
            "post-index as no-offset form",
            &st1d,
            st1d_word & !(1 << 23),
            &["fields", "writeback"],
        ),
        ("wrong base", &ld1q, ld1q_word ^ (1 << 5), &["fields"]),
        ("wrong transfer register", &st1d, st1d_word ^ 1, &["fields"]),
    ];
    for (label, instruction, word, expected) in cases {
        assert_eq!(
            refuted_parts(instruction, word),
            expected.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
            "{label}: {word:#010x}"
        );
    }
}

/// An opcode, the register bank its transfer operands come from, and the
/// bytes one transfer moves.
type Form = (O, fn(u16) -> MachOperand, i64);

/// Selected pair bank/mode forms at immediate boundaries and selected scalar
/// widths at both immediate-form boundaries: every admitted swept part holds.
#[test]
fn every_part_holds_over_a_sweep_of_admitted_shapes() {
    let pair_forms: [Form; 10] = [
        (O::StpRI, x, 8),
        (O::LdpRI, x, 8),
        (O::StpPreIndex, x, 8),
        (O::LdpPostIndex, x, 8),
        (O::StpRI, w, 4),
        (O::LdpPostIndex, w, 4),
        (O::StpPreIndex, d, 8),
        (O::LdpRI, s, 4),
        (O::NeonStpQPost, q, 16),
        (O::NeonLdpQPost, q, 16),
    ];
    let mut count = 0;
    for (opcode, bank, size) in pair_forms {
        for scaled in [-64, -2, -1, 0, 1, 2, 63] {
            let instruction = inst(opcode, vec![bank(3), bank(4), x(5), imm(scaled * size)]);
            assert_holds_under(
                &memory_effect(&instruction).expect("admitted"),
                &control_config(),
            );
            count += 1;
        }
    }
    let scalar_forms: [Form; 8] = [
        (O::LdrRI, x, 8),
        (O::StrRI, x, 8),
        (O::LdrRI, w, 4),
        (O::StrRI, w, 4),
        (O::LdrhRI, w, 2),
        (O::StrhRI, w, 2),
        (O::LdrbRI, w, 1),
        (O::StrbRI, w, 1),
    ];
    for (opcode, data, size) in scalar_forms {
        for offset in [-256, -1, 0, 1, 255, size, 4095 * size] {
            let instruction = inst(opcode, vec![data(7), x(8), imm(offset)]);
            let Some(decomposition) = memory_effect(&instruction) else {
                // Only offsets neither form can carry are refused.
                assert!(offset > 255 && offset % size != 0, "{instruction:?}");
                continue;
            };
            assert_holds_under(&decomposition, &control_config());
            count += 1;
        }
    }
    assert!(count >= 120, "swept {count} shapes");
}

/// The vocabulary of every part: no shift or multiplication, no array, no
/// uninterpreted function, no quantifier, no `zero_extend` (Clean 8606 rejects
/// the `refl` step between it and `concat` with zero bits), no variable wider
/// than 64 bits.
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
        for part in memory_effect(&instruction).unwrap().parts {
            let mut bad = Vec::new();
            walk(&part.obligation.trust_ir_expr, &mut bad);
            walk(&part.obligation.aarch64_expr, &mut bad);
            assert!(bad.is_empty(), "{}: {bad:?}", part.obligation.name);
            assert!(!part.obligation.is_degenerate(), "{}", part.obligation.name);
        }
    }
}

/// The parts that refute a mutated word, by name.
fn refuted_parts(instruction: &MachInst, word: u32) -> Vec<String> {
    memory_effect_for_word(instruction, word)
        .unwrap()
        .parts
        .iter()
        .filter(|part| {
            matches!(
                decide_in_process(part, &control_config()),
                InProcess::Refuted(_)
            )
        })
        .map(|part| part.part.to_string())
        .collect()
}

#[test]
fn corrupted_words_refute_in_the_part_that_owns_the_fact() {
    let stp = inst(O::StpPreIndex, vec![x(29), x(30), sp(), imm(-16)]);
    let stp_word = 0xa9bf_7bfd;
    let ldp = inst(O::LdpPostIndex, vec![x(29), x(30), sp(), imm(16)]);
    let ldp_word = 0xa8c1_7bfd;
    let ldr = inst(O::LdrRI, vec![x(1), x(0), imm(16)]);
    let ldr_word = 0xf940_0801;
    let strb = inst(O::StrbRI, vec![w(2), x(1), imm(3)]);
    let strb_word = 0x3900_0c22;
    let ldrh = inst(O::LdrhRI, vec![w(5), x(6), imm(2)]);
    let ldrh_word = 0x7940_04c5;

    let swap = |word: u32| {
        let rt = word & 31;
        let rt2 = (word >> 10) & 31;
        (word & !(31 | (31 << 10))) | rt2 | (rt << 10)
    };
    let cases: Vec<(&str, &MachInst, u32, &[&str])> = vec![
        // Swapped lanes: only the register fields say which lane is which.
        ("swapped lanes (store)", &stp, swap(stp_word), &["fields"]),
        ("swapped lanes (load)", &ldp, swap(ldp_word), &["fields"]),
        // Wrong offset: the imm7 field is not a fixed field; the address and
        // the writeback that use it refute.
        (
            "wrong offset (pre-index)",
            &stp,
            stp_word ^ (1 << 15),
            &["address lane 0", "address lane 1", "writeback"],
        ),
        (
            "wrong offset (post-index)",
            &ldp,
            ldp_word ^ (1 << 15),
            &["writeback"],
        ),
        (
            "wrong offset (scalar)",
            &ldr,
            ldr_word ^ (1 << 10),
            &["address lane 0"],
        ),
        // Missing writeback: pre-index -> signed offset.
        (
            "missing writeback",
            &stp,
            (stp_word & !(0b11 << 23)) | (0b10 << 23),
            &["fields", "writeback"],
        ),
        // Wrong writeback form: post-index -> pre-index.
        (
            "post-index as pre-index",
            &ldp,
            ldp_word | (0b11 << 23),
            &["fields", "address lane 0", "address lane 1"],
        ),
        // Wrong width: X pair as W pair (opc 10 -> 00).
        (
            "X pair as W pair",
            &stp,
            stp_word & !(0b11 << 30),
            &[
                "fields",
                "address lane 0",
                "address lane 1",
                "writeback",
                "store lane 0 half 0",
                "store lane 1 half 0",
            ],
        ),
        (
            "X load as W load",
            &ldr,
            (ldr_word & !(0b11 << 30)) | (0b10 << 30),
            &["fields", "address lane 0", "load lane 0 half 0"],
        ),
        (
            "byte store as halfword store",
            &strb,
            strb_word | (0b01 << 30),
            &["fields", "address lane 0", "store lane 0 half 0"],
        ),
        // Wrong extension: LDRH (opc 01) as LDRSH to X (opc 10).
        (
            "zero-extending load as sign-extending",
            &ldrh,
            (ldrh_word & !(0b11 << 22)) | (0b10 << 22),
            &["fields", "load lane 0 half 0"],
        ),
        // Wrong direction and wrong base register.
        // Direction: the load part reads the opc field too (00 is no load).
        (
            "load as store",
            &ldr,
            ldr_word & !(1 << 22),
            &["fields", "load lane 0 half 0"],
        ),
        ("wrong base", &ldr, ldr_word ^ (1 << 5), &["fields"]),
    ];
    for (label, instruction, word, expected) in cases {
        assert_eq!(
            refuted_parts(instruction, word),
            expected.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
            "{label}: {word:#010x}"
        );
    }
}

/// Every single-bit flip of every assembler word refutes at least one part,
/// except the flips that name an architecturally equal access: none exist for
/// these words, because every bit is either a fixed field the `fields` part
/// pins or an immediate bit the address part reads.
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

/// Every symbolic part of every assembler row is decided for every input
/// without sampling (`decide_exactly`), and the sampling lane agrees.
#[test]
fn every_symbolic_part_of_the_assembler_rows_is_decided_exactly() {
    let mut decided = 0;
    for (instruction, _) in assembler_rows() {
        for part in memory_effect(&instruction).unwrap().parts {
            if part.obligation.inputs.is_empty() {
                continue;
            }
            assert_eq!(
                decide_exactly(&part.obligation),
                Some(Ok(())),
                "{}",
                part.obligation.name
            );
            assert!(!needs_sampling(&part), "{}", part.obligation.name);
            assert!(
                matches!(
                    memoized_verify_by_evaluation(&part.obligation, &control_config()),
                    VerificationResult::Valid
                ),
                "{}",
                part.obligation.name
            );
            decided += 1;
        }
    }
    assert!(decided >= 80, "{decided} symbolic parts");
}

/// The exact decision never contradicts the evaluator over every single-bit
/// flip of every assembler word: a part it decides to hold has no
/// counterexample in the sampling lane, and a part the sampling lane refutes
/// it refutes too (or leaves undecided). It also refutes some part of every
/// flip, as the evaluator does.
#[test]
fn the_exact_decision_agrees_with_the_evaluator_on_every_single_bit_flip() {
    for (instruction, word) in assembler_rows() {
        for bit in 0..32 {
            let flipped = word ^ (1 << bit);
            let decomposition = memory_effect_for_word(&instruction, flipped).unwrap();
            for part in decomposition.parts {
                if part.obligation.inputs.is_empty() {
                    continue;
                }
                let exact = decide_exactly(&part.obligation);
                let sampled = memoized_verify_by_evaluation(&part.obligation, &control_config());
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

#[test]
fn unadmitted_shapes_get_no_decomposition() {
    for instruction in [
        // A load into the zero register discards its value.
        inst(O::LdrRI, vec![xzr(), x(1)]),
        // Duplicate LDP destinations are constrained unpredictable.
        inst(O::LdpRI, vec![x(1), x(1), x(2)]),
        // Writeback onto a transfer register.
        inst(O::LdpPostIndex, vec![x(2), x(3), x(2), imm(16)]),
        // An offset neither scalar form can carry.
        inst(O::LdrRI, vec![x(1), x(2), imm(257)]),
        // Writeback onto the transfer register, a load overwriting its own
        // base and a volatile access bind no scalar form.
        inst(O::LdrPostIndex, vec![x(2), x(2), imm(8)]),
        inst(O::LdrRO, vec![x(2), x(2), x(3)]),
        inst(O::VolatileLdrRI, vec![x(1), x(2), imm(8)]),
        // A D register cannot receive a 16-byte LD1; the base is never XZR;
        // an arrangement selector must name one of the seven arrangements.
        inst(O::NeonLd1Post, vec![d(1), x(2), imm(1)]),
        inst(O::NeonLd1Post, vec![q(1), xzr(), imm(1)]),
        // ... in either spelling: the allocator's XZR/WZR registers are
        // 64-/32-bit GPR class registers whose field 31 would name SP here.
        inst(
            O::NeonLd1Post,
            vec![
                q(1),
                MachOperand::PReg(trust_cg_ir::aarch64_regs::XZR),
                imm(1),
            ],
        ),
        inst(
            O::NeonSt1Post,
            vec![
                d(1),
                MachOperand::PReg(trust_cg_ir::aarch64_regs::XZR),
                imm(0),
            ],
        ),
        inst(
            O::NeonSt1Post,
            vec![
                q(1),
                MachOperand::PReg(trust_cg_ir::aarch64_regs::WZR),
                imm(1),
            ],
        ),
        // A 32-bit base register is not an address.
        inst(O::NeonLd1Post, vec![q(1), w(2), imm(1)]),
        inst(O::NeonSt1Post, vec![q(1), x(2), imm(7)]),
        inst(O::NeonSt1Post, vec![q(1), x(2)]),
        inst(O::NeonLd1Post, vec![x(1), x(2), imm(0)]),
    ] {
        assert!(memory_effect(&instruction).is_none(), "{instruction:?}");
        assert!(check_emitted_memory_effect_word(&instruction, 0).is_none());
    }
}

/// The raw query every part sends is small: the largest part of any assembler
/// row stays under 4 KiB (the one-formula pair obligation it replaces is an
/// order of magnitude larger, see `crates/trust-cg-verify/tests/memory_effect_queries.rs`).
#[test]
fn every_part_query_is_small() {
    let ay = crate::ay_bridge::AYConfig::default();
    let mut largest = 0;
    for (instruction, _) in assembler_rows() {
        for part in memory_effect(&instruction).unwrap().parts {
            let query = crate::ay_bridge::generate_smt2_query_raw(&part.obligation, &ay);
            assert!(query.contains("(set-logic QF_BV)"), "{query}");
            largest = largest.max(query.len());
        }
    }
    assert!(largest < 4096, "largest part query is {largest} bytes");
}

// ---------------------------------------------------------------------------
// The walk's arm and the live replay lane
// ---------------------------------------------------------------------------

use crate::function_verifier::{
    FunctionVerifier, InstructionVerificationResult, MEMORY_EFFECT_EVERY_PART_CHECKED,
    MEMORY_EFFECT_IS_NOT_CREDIT, MEMORY_EFFECT_REPLAY_NOT_REQUESTED,
};
use crate::provenance_xcheck::ProvenanceXCheckMode;

/// The previous reason the combinator receives in these tests, as the row's
/// own lane and the Formal-only rule would leave an uncredited row.
const LANE_REASON: &str = "the lane's own uncredited reason";

/// [`FunctionVerifier::with_memory_effect`] applied to `row`.
fn check_row(
    verifier: &FunctionVerifier,
    instruction: &MachInst,
    row: InstructionVerificationResult,
    mode: ProvenanceXCheckMode,
) -> InstructionVerificationResult {
    verifier.with_memory_effect(instruction, row, mode, None, &std::cell::OnceCell::new())
}

/// [`check_row`] of an uncredited lane row ([`LANE_REASON`]).
fn walk_row(
    verifier: &FunctionVerifier,
    instruction: &MachInst,
    mode: ProvenanceXCheckMode,
) -> InstructionVerificationResult {
    check_row(
        verifier,
        instruction,
        InstructionVerificationResult::Unverified {
            reason: LANE_REASON.into(),
        },
        mode,
    )
}

fn unverified_reason(result: InstructionVerificationResult) -> String {
    match result {
        InstructionVerificationResult::Unverified { reason } => reason,
        other => panic!("expected an unverified memory-effect row, got {other:?}"),
    }
}

fn promotion_config() -> VerificationConfig {
    VerificationConfig {
        sample_count: 2048,
        ..VerificationConfig::for_proof_promotion()
    }
}

/// Without a replaying policy an uncredited row keeps its reason, then the
/// clause: it holds in process, names its word and says no part has a
/// checked certificate. It is never credit.
#[test]
fn the_check_annotates_an_unreplayed_uncredited_row() {
    let stp = inst(O::StpPreIndex, vec![x(29), x(30), sp(), imm(-16)]);
    let reason = unverified_reason(walk_row(
        &FunctionVerifier::with_config(control_config()),
        &stp,
        ProvenanceXCheckMode::Enforce,
    ));
    assert_eq!(
        reason,
        format!(
            "{LANE_REASON}; {MEMORY_EFFECT_IS_NOT_CREDIT}: `A64 memory effect StpPreIndex \
             0xa9bf7bfd` holds in process: all 6 parts exactly; 0 of 6 parts have a \
             Clean-checked certificate (no live replay under this verification policy)"
        )
    );
    // A replay policy outside Enforce replays nothing either, even when the
    // diagnostic replay is requested.
    let promotion = FunctionVerifier::with_config(promotion_config());
    for mode in [ProvenanceXCheckMode::Warn, ProvenanceXCheckMode::Off] {
        let reason =
            crate::env_lock::with_env_overrides(&[("TCG_MEMORY_EFFECT_REPLAY", "1")], || {
                unverified_reason(walk_row(&promotion, &stp, mode))
            });
        assert!(
            reason.ends_with("(no live replay under this verification policy)"),
            "{reason}"
        );
    }
}

/// The check never credits and never removes credit: a `Verified` row (the
/// Formal-only rule's credit) stays exactly as it was, a `Failed` or `Skipped`
/// row is untouched, and a row the decomposition does not admit is returned
/// as it came.
#[test]
fn the_check_keeps_a_credited_failed_skipped_or_unadmitted_row() {
    let verifier = FunctionVerifier::with_config(control_config());
    let stp = inst(O::StpPreIndex, vec![x(29), x(30), sp(), imm(-16)]);
    let credited = InstructionVerificationResult::Verified {
        proof_name: "PairMem[stp.pre.gpr.w8]".into(),
        category: crate::proof_database::ProofCategory::Memory,
        strength: crate::verify::VerificationStrength::Formal,
        degenerate: false,
    };
    let failed = InstructionVerificationResult::Failed {
        proof_name: "the lane's refutation".into(),
        detail: "Invalid: counterexample".into(),
    };
    let skipped = InstructionVerificationResult::Skipped {
        reason: "pseudo".into(),
    };
    // `InstructionVerificationResult` has no `PartialEq`; its `Debug` text
    // shows every field.
    for row in [credited, failed, skipped] {
        assert_eq!(
            format!(
                "{:?}",
                check_row(&verifier, &stp, row.clone(), ProvenanceXCheckMode::Enforce)
            ),
            format!("{row:?}")
        );
    }
    // `LDP X1, X1, [X0, #16]` loads one register twice (A4): not admitted.
    let unadmitted = inst(O::LdpRI, vec![x(1), x(1), x(0), imm(16)]);
    assert!(memory_effect(&unadmitted).is_none());
    let row = InstructionVerificationResult::Unverified {
        reason: LANE_REASON.into(),
    };
    assert_eq!(
        format!(
            "{:?}",
            check_row(
                &verifier,
                &unadmitted,
                row.clone(),
                ProvenanceXCheckMode::Enforce
            )
        ),
        format!("{row:?}")
    );
}

/// A refuted part fails the row whatever the lane concluded, a `Formal`
/// credit included (the seam decomposes a word whose writeback immediate is
/// not the operands'), and the failure names the refuted part.
#[test]
fn a_refuted_part_fails_even_a_credited_row() {
    let verifier = FunctionVerifier::with_config(control_config());
    let stp = inst(O::StpPreIndex, vec![x(29), x(30), sp(), imm(-16)]);
    let own = memory_effect_word(&stp).unwrap();
    // imm7, bits 21:15: -16 becomes -8.
    let wrong = own ^ (1 << 15);
    let credited = InstructionVerificationResult::Verified {
        proof_name: "PairMem[stp.pre.gpr.w8]".into(),
        category: crate::proof_database::ProofCategory::Memory,
        strength: crate::verify::VerificationStrength::Formal,
        degenerate: false,
    };
    let uncredited = InstructionVerificationResult::Unverified {
        reason: LANE_REASON.into(),
    };
    for row in [credited, uncredited] {
        let result = {
            let _seam = crate::function_verifier::memory_effect_word_seam::judge_against(wrong);
            check_row(&verifier, &stp, row, ProvenanceXCheckMode::Enforce)
        };
        match result {
            InstructionVerificationResult::Failed { proof_name, detail } => {
                assert_eq!(
                    proof_name,
                    format!("A64 memory effect StpPreIndex {wrong:#010x}: address lane 0")
                );
                assert!(
                    detail.starts_with("memory-effect part refuted in process: "),
                    "{detail}"
                );
            }
            other => panic!("a refuted part must fail the row, got {other:?}"),
        }
    }
}

/// Under the promotion policy the live replay is a diagnostic: without the
/// `memory-effect-replay` knob nothing is replayed and the row says so.
#[test]
fn the_live_replay_is_off_unless_requested() {
    let verifier = FunctionVerifier::with_config(promotion_config());
    let ldr = inst(O::LdrRI, vec![x(1), x(0), imm(16)]);
    let reason = crate::env_lock::with_env_overrides_removed(&["TCG_MEMORY_EFFECT_REPLAY"], || {
        unverified_reason(walk_row(&verifier, &ldr, ProvenanceXCheckMode::Enforce))
    });
    assert!(
        reason.ends_with(&format!(
            "; 0 of 3 parts have a Clean-checked certificate \
             ({MEMORY_EFFECT_REPLAY_NOT_REQUESTED})"
        )),
        "{reason}"
    );
    let reason = crate::env_lock::with_env_overrides(&[("TCG_MEMORY_EFFECT_REPLAY", "0")], || {
        unverified_reason(walk_row(&verifier, &ldr, ProvenanceXCheckMode::Enforce))
    });
    assert!(
        reason.contains(MEMORY_EFFECT_REPLAY_NOT_REQUESTED),
        "{reason}"
    );
}

/// Under the promotion policy with replay refused, the lane stops at the
/// first part and says why; the row is not credit.
#[test]
fn a_refused_replay_names_the_first_part_without_a_certificate() {
    let verifier = FunctionVerifier::with_config(promotion_config());
    let ldr = inst(O::LdrRI, vec![x(1), x(0), imm(16)]);
    let reason = crate::env_lock::with_env_overrides(
        &[
            ("TCG_REFINE_SOLVER", "0"),
            ("TCG_MEMORY_EFFECT_REPLAY", "1"),
        ],
        || unverified_reason(walk_row(&verifier, &ldr, ProvenanceXCheckMode::Enforce)),
    );
    assert!(
        reason.ends_with(
            "; 0 of 3 parts have a Clean-checked certificate; the first without one is `fields` \
             (replay refused: TCG_REFINE_SOLVER=0)"
        ),
        "{reason}"
    );
}

/// The development AY this host carries (`2657db47c`;
/// `reports/2026-09-18-darwin-ay-dev-build`) and the two capable Clean
/// checkers: the development Clean `ed21fee39` and the aterm-managed packaged
/// Clean 8606 (the checker the production lane selects on this host, because
/// the Trust package's own Clean is built without `carcara-verify`). Each is
/// admitted for this test only, by digest. Run with
/// `TRUST_CG_RUN_FORMAL_PROOF_TESTS=1`; without the flag or any binary the
/// test returns early and says so.
const DEV_AY: &str = "$HOME/ay-worktrees/bin/ay-2657db47c-darwin-dev";
const DEV_AY_SHA256: &str = "b37fa549fa0712cc6283f0675d029f2a802641d1c61c0a6a329ed69faae3a9a8";
const CHECKERS: [(&str, &str); 2] = [
    (
        "$HOME/clean-worktrees/bin/clean-ed21fee39-darwin-dev",
        "ad10bed671a8bf8110b3abefd4f72d6b13380ddba308aa1c58181867a03fac96",
    ),
    (
        "$HOME/Library/Application Support/aterm/pkg/store/clean/8606/bin/clean",
        "9c594e838ff7e73815977c2d675238828f82417e77986abfe38d75b8ab060e16",
    ),
];

fn dev_ay_and_checkers() -> Option<(std::path::PathBuf, Vec<std::path::PathBuf>)> {
    if trust_cg_process_env::var("TRUST_CG_RUN_FORMAL_PROOF_TESTS").as_deref() != Ok("1") {
        eprintln!("dev-AY lane test not run: TRUST_CG_RUN_FORMAL_PROOF_TESTS is not 1");
        return None;
    }
    let recorded = std::iter::once((DEV_AY, DEV_AY_SHA256)).chain(CHECKERS);
    let mut paths = Vec::new();
    for (path, digest) in recorded {
        let path = std::path::PathBuf::from(path);
        if !path.is_file() || crate::ay_identity::test_fixtures::sha256_of(&path) != digest {
            eprintln!(
                "dev-AY lane test not run: {} is not the recorded binary",
                path.display()
            );
            return None;
        }
        paths.push(path);
    }
    let ay = paths.remove(0);
    Some((ay, paths))
}

/// Through the lane's own AY invocation and Clean check, every part of every
/// assembler row gets a Clean-checked certificate with the development AY,
/// under each capable checker, and the row still is NOT credit: it reports
/// every part checked in its `MEMORY_EFFECT_IS_NOT_CREDIT` clause.
#[cfg(unix)]
#[test]
fn with_the_dev_ay_every_part_is_checked_by_each_capable_clean_and_the_row_stays_uncredited() {
    let Some((ay, checkers)) = dev_ay_and_checkers() else {
        return;
    };
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    for clean in checkers {
        // A fresh certificate store per checker, so no proof minted under
        // one checker is reused under the other.
        let cache = tempfile::tempdir().expect("scratch cache");
        trust_cg_process_env::with_env_edits(|env| {
            env.set("AY_SOLVER_PATH", &ay);
            env.set(
                crate::ay_identity::test_fixtures::FIXTURE_DIGESTS_ENV,
                crate::ay_identity::test_fixtures::declare(&[&ay]),
            );
            env.set("TCG_EXTERNAL_CLEAN_CHECKER", &clean);
            env.set("TCG_NO_SOLVER_SERVER", "1");
            env.set("TCG_NO_CERT_STORE", "1");
            env.set("TCG_CANARY_NO_CACHE", "1");
            env.set("TCG_NO_VERDICT_DB", "1");
            env.set("TCG_REFINE_SOLVER", "1");
            env.set("TCG_MEMORY_EFFECT_REPLAY", "1");
            env.set("XDG_CACHE_HOME", cache.path());
            env.remove("TCG_NO_PROOF_CACHE");
            let verifier = FunctionVerifier::with_config(promotion_config());
            let mut checked = 0;
            for (instruction, word) in assembler_rows() {
                let parts = memory_effect(&instruction).unwrap().parts.len();
                let reason = unverified_reason(walk_row(
                    &verifier,
                    &instruction,
                    ProvenanceXCheckMode::Enforce,
                ));
                assert!(
                    reason.starts_with(&format!(
                        "{LANE_REASON}; {MEMORY_EFFECT_IS_NOT_CREDIT}: `A64 memory effect {:?} \
                         {word:#010x}`",
                        instruction.opcode
                    )) && reason.ends_with(&format!(
                        "{MEMORY_EFFECT_EVERY_PART_CHECKED} ({parts} parts)"
                    )),
                    "{}: {reason}",
                    clean.display()
                );
                checked += parts;
            }
            assert_eq!(checked, 112, "{}", clean.display());
        });
    }
}

// ===========================================================================
// The remaining scalar forms (L04-P1): H/S/D/Q transfers, sign-extending
// loads, pre/post-index writeback and register offset, through the binder.
// ===========================================================================

/// One representative instruction per (opcode, legal form), self-checked.
fn every_scalar_form_instruction() -> Vec<MachInst> {
    use crate::aarch64_scalar_memory_proofs::{
        representative_scalar_instruction, scalar_opcode_forms,
    };
    let mut out = Vec::new();
    for opcode in [
        O::LdrRI,
        O::StrRI,
        O::LdrbRI,
        O::LdrhRI,
        O::LdrsbRI,
        O::LdrshRI,
        O::StrbRI,
        O::StrhRI,
        O::LdrPreIndex,
        O::LdrPostIndex,
        O::StrPreIndex,
        O::StrPostIndex,
        O::LdrRO,
        O::StrRO,
        O::LdrbRO,
        O::LdrhRO,
        O::StrbRO,
        O::StrhRO,
    ] {
        for form in scalar_opcode_forms(opcode).unwrap() {
            out.push(representative_scalar_instruction(opcode, &form).unwrap());
        }
    }
    // Every register-offset mode, SP bases, register 30 and ZR indices.
    for mode in [4, 5, 6, 7, 12, 13, 14, 15] {
        out.push(inst(O::LdrRO, vec![x(30), sp(), x(29), imm(mode)]));
        out.push(inst(
            O::StrRO,
            vec![q(31), x(4), w(5), imm(mode & !0b0010 | 0b0100)],
        ));
        out.push(inst(O::LdrRO, vec![d(7), x(8), xzr(), imm(mode)]));
    }
    out
}

#[test]
fn every_scalar_form_decomposes_and_every_part_is_decided_exactly() {
    let mut parts = 0;
    for instruction in every_scalar_form_instruction() {
        let decomposition =
            memory_effect(&instruction).unwrap_or_else(|| panic!("{instruction:?} must decompose"));
        assert_eq!(
            check_emitted_memory_effect_word(&instruction, decomposition.word),
            Some(Ok(()))
        );
        for part in &decomposition.parts {
            assert!(
                !needs_sampling(part),
                "{}: not decided exactly",
                part.obligation.name
            );
            match decide_in_process(part, &config()) {
                InProcess::Holds(VerificationStrength::Exhaustive) => {}
                other => panic!("{}: {other:?}", part.obligation.name),
            }
            assert!(!part.obligation.is_degenerate(), "{}", part.obligation.name);
            parts += 1;
        }
    }
    eprintln!("SCALAR_MEMORY_EFFECT parts={parts}");
}

#[test]
fn every_single_bit_flip_of_every_scalar_form_word_refutes_exactly() {
    for instruction in every_scalar_form_instruction() {
        let word = memory_effect_word(&instruction).unwrap();
        for bit in 0..32 {
            let flipped = word ^ (1 << bit);
            let decomposition = memory_effect_for_word(&instruction, flipped).unwrap();
            assert!(
                decomposition.parts.iter().any(|part| matches!(
                    decide_in_process(part, &config()),
                    InProcess::Refuted(_)
                )),
                "{instruction:?}: bit {bit} of {word:#010x} is not refuted"
            );
        }
    }
}

/// The word of a neighbouring form refutes in the part that owns the fact:
/// another width or bank in a load/store lane, another extension in the load
/// lane, pre for post in the writeback/address parts, another index
/// extension or shift in the address part.
#[test]
fn neighbouring_scalar_forms_refute_in_their_owning_part() {
    let owning = |operands: MachInst, word_of: MachInst, part: &str| {
        let word = memory_effect_word(&word_of).unwrap();
        let refuted: Vec<String> = memory_effect_for_word(&operands, word)
            .unwrap()
            .parts
            .iter()
            .filter(|candidate| {
                matches!(
                    decide_in_process(candidate, &config()),
                    InProcess::Refuted(_)
                )
            })
            .map(|candidate| candidate.part.to_string())
            .collect();
        assert!(
            refuted.iter().any(|name| name == part),
            "{operands:?} on the word of {word_of:?}: {refuted:?} must include {part}"
        );
    };
    // H for S, D for Q (width/bank in the lane).
    owning(
        inst(O::LdrRI, vec![s(1), x(2), imm(8)]),
        inst(
            O::LdrRI,
            vec![
                MachOperand::PReg(trust_cg_ir::PReg::new(165 + 1)),
                x(2),
                imm(8),
            ],
        ),
        "load lane 0 half 0",
    );
    owning(
        inst(O::StrRI, vec![q(1), x(2), imm(16)]),
        inst(O::StrRI, vec![d(1), x(2), imm(16)]),
        "store lane 0 half 1",
    );
    // Sign-extend to X for sign-extend to W; zero-extend for sign-extend.
    owning(
        inst(O::LdrsbRI, vec![w(1), x(2), imm(3)]),
        inst(O::LdrsbRI, vec![x(1), x(2), imm(3)]),
        "load lane 0 half 0",
    );
    owning(
        inst(O::LdrshRI, vec![x(1), x(2), imm(4)]),
        inst(O::LdrhRI, vec![x(1), x(2), imm(4)]),
        "load lane 0 half 0",
    );
    // Pre-index for post-index: the address moves, the writeback stays.
    owning(
        inst(O::LdrPostIndex, vec![x(1), x(2), imm(-16)]),
        inst(O::LdrPreIndex, vec![x(1), x(2), imm(-16)]),
        "address lane 0",
    );
    // Writeback dropped: the unscaled form with the same imm9.
    owning(
        inst(O::StrPreIndex, vec![x(1), x(2), imm(-16)]),
        inst(O::StrRI, vec![x(1), x(2), imm(-16)]),
        "writeback",
    );
    // SXTW for UXTW, and the shift dropped.
    owning(
        inst(O::LdrRO, vec![x(1), x(2), w(3), imm(5)]),
        inst(O::LdrRO, vec![x(1), x(2), w(3), imm(13)]),
        "address lane 0",
    );
    owning(
        inst(O::StrRO, vec![d(1), x(2), x(3), imm(7)]),
        inst(O::StrRO, vec![d(1), x(2), x(3), imm(6)]),
        "address lane 0",
    );
}

#[test]
fn every_scalar_form_part_stays_in_the_checker_friendly_vocabulary() {
    fn walk(expr: &SmtExpr, bad: &mut Vec<String>) {
        match expr {
            SmtExpr::BvShl { .. }
            | SmtExpr::BvLshr { .. }
            | SmtExpr::BvAshr { .. }
            | SmtExpr::BvMul { .. }
            | SmtExpr::ZeroExtend { .. } => {
                bad.push(format!("{expr:?}").chars().take(60).collect())
            }
            SmtExpr::Var { width, name } if *width > 64 => bad.push(name.clone()),
            _ => {}
        }
        expr.for_each_child(&mut |child| walk(child, bad));
    }
    for instruction in every_scalar_form_instruction() {
        for part in memory_effect(&instruction).unwrap().parts {
            let mut bad = Vec::new();
            walk(&part.obligation.trust_ir_expr, &mut bad);
            walk(&part.obligation.aarch64_expr, &mut bad);
            assert!(bad.is_empty(), "{}: {bad:?}", part.obligation.name);
        }
    }
}
