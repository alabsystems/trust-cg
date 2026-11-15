// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Tests of the word-bound atomic value/memory-effect decomposition.

use super::*;
use crate::aarch64_atomic_forms::{
    ATOMIC_MEMORY_OPCODES, atomic_opcode_forms, atomic_opcode_shape, representative_instruction,
};

/// Every (opcode, width) instruction the selector can emit, with three
/// register choices (distinct, SP base, and Rs == Rt).
fn every_instruction() -> Vec<MachInst> {
    let mut out = Vec::new();
    for opcode in ATOMIC_MEMORY_OPCODES {
        for form in atomic_opcode_forms(opcode).unwrap() {
            for (rs, rt, rn) in [(1, 2, 3), (9, 10, 31), (5, 5, 6)] {
                out.push(representative_instruction(opcode, form.bytes, rs, rt, rn).unwrap());
            }
        }
    }
    out
}

#[test]
fn every_admitted_instruction_holds_exactly_and_no_part_is_undecided() {
    let mut parts = 0;
    for inst in every_instruction() {
        let decomposition = atomic_effect(&inst).unwrap_or_else(|| panic!("{inst:?}"));
        assert_eq!(
            judge(&decomposition),
            AtomicEffectVerdict::Holds,
            "{inst:?}"
        );
        for part in &decomposition.parts {
            assert!(
                part.obligation.inputs.is_empty() || decide_exactly(&part.obligation).is_some(),
                "{inst:?} {}: not decided exactly",
                part.part
            );
            assert_ne!(
                part.obligation.trust_ir_expr, part.obligation.aarch64_expr,
                "{inst:?} {} is X == X before folding",
                part.part
            );
            parts += 1;
        }
        assert_eq!(
            check_emitted_atomic_word(&inst, decomposition.word),
            Some(Ok(()))
        );
    }
    eprintln!("ATOMIC_EFFECT parts={parts}");
}

/// The value and memory parts refute a word of another operation or width
/// on their own (not only through `fields`), so they say something about the
/// word beyond its field equality.
#[test]
fn semantic_parts_refute_another_operation_or_width_on_their_own() {
    let mut refuted = 0;
    let mut identical = 0;
    for inst in every_instruction() {
        let word = atomic_effect_word(&inst).unwrap();
        // size (31:30), the LSE operation (o3, opc) and the CAS/LDAR/STLR
        // class bits (23, 22, 21).
        for bit in [30u32, 31, 12, 13, 14, 15, 21, 22, 23] {
            let flipped = word ^ (1 << bit);
            let decomposition = atomic_effect_for_word(&inst, flipped).unwrap();
            let semantic: Vec<_> = decomposition
                .parts
                .iter()
                .filter(|part| part.part != AtomicEffectPart::Fields)
                .map(|part| (part.part, decide_exactly(&part.obligation)))
                .collect();
            assert!(
                matches!(judge(&decomposition), AtomicEffectVerdict::Refuted { .. }),
                "{inst:?} bit {bit}: the fields part must refute at least"
            );
            if semantic
                .iter()
                .any(|(_, verdict)| matches!(verdict, Some(Err(_))))
            {
                refuted += 1;
            } else {
                // Only the ordering bits (A/R, 23/22 in the LSE class) and
                // flips into an unallocated or identical-semantics encoding may
                // leave the value and memory parts holding.
                identical += 1;
            }
        }
    }
    eprintln!("ATOMIC_EFFECT_SEMANTIC_FLIPS refuted={refuted} fields_only={identical}");
    assert!(refuted > identical, "{refuted} vs {identical}");
}

#[test]
fn every_single_bit_flip_of_every_word_refutes() {
    for inst in every_instruction() {
        let word = atomic_effect_word(&inst).unwrap();
        for bit in 0..32 {
            let decomposition = atomic_effect_for_word(&inst, word ^ (1 << bit)).unwrap();
            assert!(
                matches!(judge(&decomposition), AtomicEffectVerdict::Refuted { .. }),
                "{inst:?} bit {bit}"
            );
            assert!(
                check_emitted_atomic_word(&inst, word ^ (1 << bit)).is_some_and(|r| r.is_err())
            );
        }
    }
}

/// Wrong width, wrong operation, wrong ordering and swapped operands: the
/// word of one instruction judged against the operands of another refutes.
#[test]
fn wrong_width_operation_ordering_and_swapped_operands_refute() {
    let cases = [
        // Wrong width: LDADD W against LDADD X operands.
        (
            representative_instruction(O::Ldaddal, 8, 1, 2, 3).unwrap(),
            representative_instruction(O::Ldaddal, 4, 1, 2, 3).unwrap(),
            AtomicEffectPart::Value,
        ),
        // Wrong width: a byte CAS against a halfword CAS.
        (
            representative_instruction(O::Casal, 2, 1, 2, 3).unwrap(),
            representative_instruction(O::Casal, 1, 1, 2, 3).unwrap(),
            AtomicEffectPart::Value,
        ),
        // Wrong operation: LDCLR against LDSET operands, SMAX against UMAX,
        // SWP against LDADD, STLR against LDAR.
        (
            representative_instruction(O::Ldset, 8, 1, 2, 3).unwrap(),
            representative_instruction(O::Ldclr, 8, 1, 2, 3).unwrap(),
            AtomicEffectPart::Memory,
        ),
        (
            representative_instruction(O::Ldumax, 4, 1, 2, 3).unwrap(),
            representative_instruction(O::Ldsmax, 4, 1, 2, 3).unwrap(),
            AtomicEffectPart::Memory,
        ),
        (
            representative_instruction(O::Ldadd, 1, 1, 2, 3).unwrap(),
            representative_instruction(O::Swp, 1, 1, 2, 3).unwrap(),
            AtomicEffectPart::Memory,
        ),
        (
            representative_instruction(O::Ldar, 8, 0, 2, 3).unwrap(),
            representative_instruction(O::Stlr, 8, 0, 2, 3).unwrap(),
            AtomicEffectPart::Memory,
        ),
        // Wrong ordering: only `fields` can see it.
        (
            representative_instruction(O::Ldadda, 8, 1, 2, 3).unwrap(),
            representative_instruction(O::Ldaddl, 8, 1, 2, 3).unwrap(),
            AtomicEffectPart::Fields,
        ),
        // Swapped operands: CAS compare/new registers exchanged.
        (
            representative_instruction(O::Casal, 8, 1, 2, 3).unwrap(),
            representative_instruction(O::Casal, 8, 2, 1, 3).unwrap(),
            AtomicEffectPart::Fields,
        ),
    ];
    for (operands, word_of, expected) in cases {
        let word = atomic_effect_word(&word_of).unwrap();
        let decomposition = atomic_effect_for_word(&operands, word).unwrap();
        match judge(&decomposition) {
            AtomicEffectVerdict::Refuted { part, .. } => {
                // `fields` runs first; the named semantic part must refute
                // on its own as well.
                if expected != AtomicEffectPart::Fields {
                    let semantic = decomposition
                        .parts
                        .iter()
                        .find(|candidate| candidate.part == expected)
                        .unwrap_or_else(|| panic!("{operands:?}: no {expected} part"));
                    assert!(
                        matches!(decide_exactly(&semantic.obligation), Some(Err(_))),
                        "{operands:?} judged on {word:#010x}: {expected} must refute"
                    );
                } else {
                    assert_eq!(part, AtomicEffectPart::Fields);
                }
            }
            other => panic!("{operands:?} judged on {word:#010x}: {other:?}"),
        }
    }
}

/// The decomposition's machine terms agree with the form theorem's machine
/// side on concrete inputs: both are transcriptions of the same pseudocode,
/// written separately, and must not drift apart.
#[test]
fn the_word_terms_agree_with_the_form_theorem_on_concrete_inputs() {
    use crate::smt::EvalEnv;
    let values = [
        0u64,
        u64::MAX,
        0x8000_0000_0000_0000,
        0x7FFF_FFFF_FFFF_FFFF,
        0x0000_0000_8000_0080,
        0x1234_5678_9ABC_DEF0,
    ];
    for opcode in ATOMIC_MEMORY_OPCODES {
        let shape = atomic_opcode_shape(opcode).unwrap();
        for form in atomic_opcode_forms(opcode).unwrap() {
            let inst = representative_instruction(opcode, form.bytes, 1, 2, 3).unwrap();
            let decomposition = atomic_effect(&inst).unwrap();
            let theorem = crate::aarch64_atomic_forms::proof_atomic_form(&form).unwrap();
            let memory_part = decomposition
                .parts
                .iter()
                .find(|part| part.part == AtomicEffectPart::Memory)
                .unwrap();
            for &old in &values {
                for &s in &values {
                    for &t in &values {
                        let mut env = EvalEnv::default();
                        env.insert(WINDOW.to_string(), old);
                        env.insert(REG_S.to_string(), s);
                        env.insert(REG_T.to_string(), t);
                        let after = memory_part
                            .obligation
                            .aarch64_expr
                            .try_eval(&env)
                            .unwrap()
                            .as_u64();
                        // The form theorem at byte k of the window (q = base + k).
                        for k in 0..8u64 {
                            let mut env = EvalEnv::default();
                            let base = 0x4000u64;
                            env.insert(crate::aarch64_atomic_forms::BASE.to_string(), base);
                            for b in 0..form.bytes {
                                env.insert(
                                    crate::aarch64_atomic_forms::window_byte(b),
                                    (old >> (8 * b)) & 0xFF,
                                );
                            }
                            env.insert(
                                crate::aarch64_atomic_forms::M.to_string(),
                                (old >> (8 * k)) & 0xFF,
                            );
                            env.insert(crate::aarch64_atomic_forms::Q.to_string(), base + k);
                            env.insert(crate::aarch64_atomic_forms::RS.to_string(), s);
                            env.insert(crate::aarch64_atomic_forms::RT.to_string(), t);
                            env.insert(crate::aarch64_atomic_forms::SEL.to_string(), 1);
                            env.insert(crate::aarch64_atomic_forms::J.to_string(), 0);
                            let byte = theorem.aarch64_expr.try_eval(&env).unwrap().as_u64();
                            assert_eq!(
                                byte & 0xFF,
                                (after >> (8 * k)) & 0xFF,
                                "{opcode:?} w{} byte {k} old={old:#x} s={s:#x} t={t:#x} ({shape:?})",
                                form.bytes
                            );
                        }
                    }
                }
            }
        }
    }
}
