// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Tests of the atomic form theorems, binder, encoder and decoder.

use super::*;
use std::collections::HashSet;
use trust_cg_ir::PReg;

fn x(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(n))
}

fn w(n: u16) -> MachOperand {
    MachOperand::PReg(PReg::new(32 + n))
}

fn sp() -> MachOperand {
    MachOperand::Special(SpecialReg::SP)
}

fn imm(value: i64) -> MachOperand {
    MachOperand::Imm(value)
}

#[test]
fn the_form_table_is_complete_unique_and_named_by_its_queries() {
    assert_eq!(ATOMIC_MEMORY_FORMS.len(), 48);
    let mut queries = HashSet::new();
    let mut forms = HashSet::new();
    for (form, query) in ATOMIC_MEMORY_FORMS {
        assert!(queries.insert(query), "duplicate query {query}");
        assert!(forms.insert(form), "duplicate form {form:?}");
        assert_eq!(form.query(), Some(query));
        let name = form.proof_name().to_lowercase();
        assert!(name.contains(query), "{name} must contain {query}");
        for (other, other_query) in ATOMIC_MEMORY_FORMS {
            if other != form {
                assert!(
                    !name.contains(other_query),
                    "{query}'s theorem name also contains {other_query}"
                );
            }
        }
    }
    for op in AtomicOp::ALL {
        for bytes in [1, 2, 4, 8] {
            assert!(forms.contains(&AtomicForm { op, bytes }), "{op:?} w{bytes}");
        }
    }
    assert_eq!(
        AtomicForm {
            op: AtomicOp::Add,
            bytes: 16
        }
        .query(),
        None
    );
}

#[test]
fn every_atomic_opcode_has_a_shape_and_its_emitted_widths() {
    assert_eq!(ATOMIC_MEMORY_OPCODES.len(), 46);
    let mut total = 0;
    for opcode in ATOMIC_MEMORY_OPCODES {
        let shape = atomic_opcode_shape(opcode).unwrap_or_else(|| panic!("{opcode:?}"));
        let forms = atomic_opcode_forms(opcode).expect("atomic opcode has forms");
        let name = format!("{opcode:?}").to_lowercase();
        match shape.op {
            AtomicOp::LoadAcquire | AtomicOp::StoreRelease => {
                let expected: &[u32] = if name.ends_with('b') {
                    &[1]
                } else if name.ends_with('h') {
                    &[2]
                } else {
                    &[4, 8]
                };
                assert_eq!(
                    forms.iter().map(|form| form.bytes).collect::<Vec<_>>(),
                    expected,
                    "{opcode:?}"
                );
            }
            _ => assert_eq!(
                forms.iter().map(|form| form.bytes).collect::<Vec<_>>(),
                [1, 2, 4, 8],
                "{opcode:?}"
            ),
        }
        // The ordering suffix the opcode name carries.
        let (acquire, release) = match shape.op {
            AtomicOp::LoadAcquire => (true, false),
            AtomicOp::StoreRelease => (false, true),
            _ => {
                let suffix = name.trim_start_matches(shape.op.stem()).to_string();
                match suffix.as_str() {
                    "" => (false, false),
                    "a" => (true, false),
                    "al" => (true, true),
                    "l" => (false, true),
                    other => panic!("{opcode:?}: unexpected suffix {other:?}"),
                }
            }
        };
        assert_eq!(
            (shape.acquire, shape.release),
            (acquire, release),
            "{opcode:?}"
        );
        total += forms.len();
    }
    // 6 LDAR/STLR opcodes cover 8 forms; 40 LSE/CAS opcodes 4 widths each.
    assert_eq!(total, 8 + 40 * 4);
    for opcode in [O::Ldxr, O::Stlxr, O::LdrRI, O::AddRR, O::Dmb] {
        assert!(!is_atomic_memory_opcode(opcode), "{opcode:?}");
    }
}

/// Words assembled by `llvm-mc -triple=aarch64 -mattr=+lse` (LLVM 21).
#[test]
fn the_encoder_matches_the_assembler_and_the_decoder_inverts_it() {
    let cases: [(MachInst, u32); 28] = [
        (MachInst::new(O::Ldarb, vec![w(3), x(4)]), 0x08df_fc83),
        (MachInst::new(O::Ldarh, vec![w(3), x(4)]), 0x48df_fc83),
        (MachInst::new(O::Ldar, vec![w(3), x(4)]), 0x88df_fc83),
        (MachInst::new(O::Ldar, vec![x(3), sp()]), 0xc8df_ffe3),
        (MachInst::new(O::Stlrb, vec![w(5), x(6)]), 0x089f_fcc5),
        (MachInst::new(O::Stlrh, vec![w(5), x(6)]), 0x489f_fcc5),
        (MachInst::new(O::Stlr, vec![w(5), x(6)]), 0x889f_fcc5),
        (
            MachInst::new(O::Stlr, vec![MachOperand::Special(SpecialReg::XZR), x(6)]),
            0xc89f_fcdf,
        ),
        (
            MachInst::new(O::Cas, vec![w(1), w(2), x(3), imm(0)]),
            0x08a1_7c62,
        ),
        (
            MachInst::new(O::Casa, vec![w(1), w(2), x(3), imm(1)]),
            0x48e1_7c62,
        ),
        (MachInst::new(O::Casal, vec![w(1), w(2), x(3)]), 0x88e1_fc62),
        (MachInst::new(O::Casl, vec![x(1), x(2), sp()]), 0xc8a1_ffe2),
        (
            MachInst::new(O::Swp, vec![w(7), w(8), x(9), imm(0)]),
            0x3827_8128,
        ),
        (
            MachInst::new(O::Swpa, vec![w(7), w(8), x(9), imm(1)]),
            0x78a7_8128,
        ),
        (MachInst::new(O::Swpal, vec![w(7), w(8), x(9)]), 0xb8e7_8128),
        (MachInst::new(O::Swpl, vec![x(7), x(8), x(9)]), 0xf867_8128),
        (
            MachInst::new(O::Ldadd, vec![w(10), w(11), x(12), imm(0)]),
            0x382a_018b,
        ),
        (
            MachInst::new(O::Ldadda, vec![w(10), w(11), x(12), imm(1)]),
            0x78aa_018b,
        ),
        (
            MachInst::new(O::Ldaddal, vec![w(10), w(11), x(12)]),
            0xb8ea_018b,
        ),
        (
            MachInst::new(O::Ldaddl, vec![x(10), x(11), x(12)]),
            0xf86a_018b,
        ),
        (
            MachInst::new(O::Ldclr, vec![w(10), w(11), x(12), imm(0)]),
            0x382a_118b,
        ),
        (
            MachInst::new(O::Ldeor, vec![w(10), w(11), x(12), imm(1)]),
            0x782a_218b,
        ),
        (
            MachInst::new(O::Ldseta, vec![w(10), w(11), x(12)]),
            0xb8aa_318b,
        ),
        (
            MachInst::new(O::Ldsmaxal, vec![x(10), x(11), x(12)]),
            0xf8ea_418b,
        ),
        (
            MachInst::new(O::Ldsminl, vec![w(10), w(11), x(12), imm(0)]),
            0x386a_518b,
        ),
        (
            MachInst::new(O::Ldumaxa, vec![w(10), w(11), x(12), imm(1)]),
            0x78aa_618b,
        ),
        (
            MachInst::new(O::Lduminl, vec![x(10), x(11), x(12)]),
            0xf86a_718b,
        ),
        // B1 carriers are X registers with the byte access-size immediate.
        (
            MachInst::new(O::Swpal, vec![x(7), x(8), x(9), imm(0)]),
            0x38e7_8128,
        ),
    ];
    for (inst, expected) in cases {
        let binding = bind_atomic_instruction(&inst).unwrap_or_else(|e| panic!("{inst:?}: {e}"));
        assert_eq!(atomic_word(&binding), expected, "{inst:?}");
        assert_eq!(decode_atomic_word(expected), Some(binding), "{inst:?}");
    }
}

#[test]
fn the_decoder_inverts_the_encoder_for_every_opcode_width_and_register() {
    for opcode in ATOMIC_MEMORY_OPCODES {
        let shape = atomic_opcode_shape(opcode).unwrap();
        for form in atomic_opcode_forms(opcode).unwrap() {
            for (rs, rt, rn) in [(0, 1, 2), (30, 29, 31), (31, 5, 0), (7, 7, 7)] {
                let binding = AtomicBinding {
                    form,
                    acquire: shape.acquire,
                    release: shape.release,
                    rs: match shape.op {
                        AtomicOp::LoadAcquire | AtomicOp::StoreRelease => None,
                        AtomicOp::Cas if rs == 31 => Some(4),
                        _ => Some(rs),
                    },
                    rt,
                    rn,
                };
                let word = atomic_word(&binding);
                assert_eq!(
                    decode_atomic_word(word),
                    Some(binding),
                    "{opcode:?} {word:#010x}"
                );
                // Every single-bit flip decodes to a different binding or to none.
                for bit in 0..32 {
                    assert_ne!(
                        decode_atomic_word(word ^ (1 << bit)),
                        Some(binding),
                        "{opcode:?} {word:#010x} bit {bit}"
                    );
                }
            }
        }
    }
    // Words of neighbouring classes are not atomic forms.
    for word in [
        0xc85f_7c20u32, // LDXR X0, [X1]
        0xc87f_0440,    // LDXP X0, X1, [X2]
        0xb8bf_c020,    // LDAPR W0, [X1]
        0x48207c82,     // CASP W0, W1, W2, W3, [X4]
        0xc8df_7c20,    // LDLAR X0, [X1] (o0 = 0)
        0xf940_0020,    // LDR X0, [X1]
    ] {
        assert_eq!(decode_atomic_word(word), None, "{word:#010x}");
    }
    // The ST<op> alias (Rt = ZR) is not attributable.
    assert_eq!(decode_atomic_word(0xf82a_019f), None);
    // A CAS whose compare register is ZR is not attributable.
    assert_eq!(decode_atomic_word(0x88ff_fc62), None);
}

#[test]
fn the_binder_refuses_malformed_and_unmodelled_shapes() {
    let refused = [
        MachInst::new(
            O::Ldadd,
            vec![x(1), MachOperand::Special(SpecialReg::XZR), x(2)],
        ),
        MachInst::new(O::Ldar, vec![MachOperand::Special(SpecialReg::WZR), x(2)]),
        MachInst::new(
            O::Cas,
            vec![MachOperand::Special(SpecialReg::XZR), x(1), x(2)],
        ),
        MachInst::new(O::Ldadd, vec![w(1), x(2), x(3)]),
        MachInst::new(O::Ldadd, vec![x(1), x(2), w(3)]),
        MachInst::new(
            O::Ldadd,
            vec![x(1), x(2), MachOperand::Special(SpecialReg::XZR)],
        ),
        MachInst::new(O::Ldadd, vec![x(1), x(2), x(3), imm(2)]),
        MachInst::new(O::Ldadd, vec![x(1), x(2)]),
        MachInst::new(O::Ldar, vec![x(1)]),
        MachInst::new(O::Stlr, vec![x(1), x(2), x(3)]),
        MachInst::new(O::Swp, vec![x(1), x(2), x(3), x(4)]),
        MachInst::new(O::AddRR, vec![x(1), x(2), x(3)]),
    ];
    for inst in refused {
        assert!(bind_atomic_instruction(&inst).is_err(), "{inst:?}");
    }
    // STLR of the zero register, CAS writing the zero register and an LSE
    // operation reading the zero register as its value are modelled.
    for inst in [
        MachInst::new(O::Stlr, vec![MachOperand::Special(SpecialReg::XZR), x(2)]),
        MachInst::new(
            O::Casal,
            vec![x(1), MachOperand::Special(SpecialReg::XZR), x(2)],
        ),
        MachInst::new(
            O::Ldaddal,
            vec![MachOperand::Special(SpecialReg::XZR), x(1), x(2)],
        ),
    ] {
        assert!(bind_atomic_instruction(&inst).is_ok(), "{inst:?}");
    }
}

#[test]
fn faithful_forms_have_no_counterexample_on_the_grid_and_are_non_degenerate() {
    for (form, _) in ATOMIC_MEMORY_FORMS {
        let obligation = proof_atomic_form(&form).expect("legal form");
        assert_ne!(
            obligation.trust_ir_expr, obligation.aarch64_expr,
            "{form:?} must not be X == X"
        );
        assert!(obligation.is_genuinely_proven(), "{form:?}");
        assert_eq!(grid_counterexample(&form, &obligation), None, "{form:?}");
    }
}

#[test]
fn every_applicable_defect_of_every_form_is_refuted_on_the_grid() {
    let mut refuted = 0;
    for (form, _) in ATOMIC_MEMORY_FORMS {
        for mutation in AtomicMachineMutation::DEFECTS {
            let Some(obligation) = proof_atomic_form_with_mutation(&form, mutation) else {
                assert!(!mutation.applies_to(&form));
                continue;
            };
            assert!(
                grid_counterexample(&form, &obligation).is_some(),
                "{form:?} {mutation:?} must be refuted"
            );
            refuted += 1;
        }
    }
    eprintln!("ATOMIC_FORM_DEFECTS refuted={refuted}");
    assert!(refuted >= 48 * 3, "{refuted}");
}

#[test]
fn the_wrong_theorem_wears_the_faithful_name_but_is_another_query() {
    let wrong = representative_wrong_atomic_theorem();
    let faithful = proof_atomic_form(&AtomicForm {
        op: AtomicOp::Add,
        bytes: 8,
    })
    .unwrap();
    assert_eq!(wrong.name, faithful.name);
    assert_ne!(
        crate::verdict_db::db_obligation_smt2(&wrong),
        crate::verdict_db::db_obligation_smt2(&faithful)
    );
    let queries = certifiable_atomic_queries();
    assert_eq!(queries.len(), 48);
    let files: HashSet<_> = queries.iter().map(|query| query.file.clone()).collect();
    assert_eq!(files.len(), 48);
}
