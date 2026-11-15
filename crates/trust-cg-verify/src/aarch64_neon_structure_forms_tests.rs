// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use crate::verify::VerificationResult;
use trust_cg_ir::PReg;

#[test]
fn fourteen_forms_have_unique_queries_and_names_and_are_non_degenerate() {
    let proofs = all_neon_structure_form_proofs();
    assert_eq!(proofs.len(), 14);
    let mut names = std::collections::BTreeSet::new();
    for ((form, query), proof) in NEON_STRUCTURE_FORMS.iter().zip(&proofs) {
        assert!(!proof.is_degenerate(), "{} is X==X", proof.name);
        assert!(names.insert(proof.name.clone()), "duplicate {}", proof.name);
        assert_eq!(*query, query.to_lowercase());
        let matching = proofs
            .iter()
            .filter(|other| other.name.to_lowercase().contains(query))
            .count();
        assert_eq!(matching, 1, "{query} must select exactly one form theorem");
        assert_eq!(form.query(), Some(*query));
        assert_eq!(form.elements() * form.element_bytes(), form.bytes());
    }
    let files: std::collections::BTreeSet<_> = certifiable_neon_queries()
        .into_iter()
        .map(|query| query.file)
        .collect();
    assert_eq!(files.len(), 14);
    assert_eq!(
        neon_opcode_forms(AArch64Opcode::NeonLd1Post).unwrap().len(),
        7
    );
    assert_eq!(
        neon_opcode_forms(AArch64Opcode::NeonSt1Post).unwrap().len(),
        7
    );
    assert!(neon_opcode_forms(AArch64Opcode::LdrRI).is_none());
}

#[test]
fn faithful_forms_hold_on_the_grid_and_under_sampling() {
    let config = crate::lowering_proof::VerificationConfig::with_sample_count(512);
    for (form, _) in NEON_STRUCTURE_FORMS {
        let faithful = proof_neon_structure_form(&form).unwrap();
        assert_eq!(
            grid_counterexample(&faithful, &form),
            None,
            "{}",
            faithful.name
        );
        let verdict = crate::lowering_proof::verify_by_evaluation_with_config(&faithful, &config);
        assert!(
            !matches!(verdict, VerificationResult::Invalid { .. }),
            "{}: {verdict:?}",
            faithful.name
        );
    }
}

#[test]
fn every_applicable_defect_is_refuted_on_the_grid() {
    let mut refuted = 0;
    for (form, _) in NEON_STRUCTURE_FORMS {
        for mutation in NeonStructureMutation::DEFECTS {
            let Some(wrong) = proof_neon_structure_form_with_mutation(&form, mutation) else {
                assert!(!mutation.applies_to(&form), "{form:?} {mutation:?}");
                continue;
            };
            assert!(
                grid_counterexample(&wrong, &form).is_some(),
                "{form:?}: the {mutation:?} defect survived the grid"
            );
            refuted += 1;
        }
    }
    // Seven defects over 14 forms, minus big-endian elements for the four
    // byte forms, no-zero-upper for every form but the three 64-bit loads,
    // and the extra stored byte for the seven loads.
    assert_eq!(refuted, 14 * 7 - 4 - 11 - 7);
}

#[test]
fn the_binder_attributes_every_form_and_refuses_other_shapes() {
    for (form, query) in NEON_STRUCTURE_FORMS {
        for base_sp in [false, true] {
            let inst = representative_neon_instruction(&form, base_sp);
            let binding = bind_neon_structure_instruction(&inst).expect("binds");
            assert_eq!(binding.query(), query);
            assert_eq!(binding.rt_field, 3);
            assert_eq!(binding.base_field, if base_sp { 31 } else { 9 });
        }
    }
    let ld1 = AArch64Opcode::NeonLd1Post;
    let q3 = MachOperand::PReg(PReg::new(64 + 3));
    let d3 = MachOperand::PReg(PReg::new(96 + 3));
    let s3 = MachOperand::PReg(PReg::new(128 + 3));
    let x9 = MachOperand::PReg(PReg::new(9));
    let w9 = MachOperand::PReg(PReg::new(32 + 9));
    let xzr = MachOperand::PReg(PReg::new(160));
    // A D register is accepted for a 64-bit arrangement.
    let d_form = MachInst::new(ld1, vec![d3.clone(), x9.clone(), MachOperand::Imm(0)]);
    assert_eq!(
        bind_neon_structure_instruction(&d_form).unwrap().query(),
        "neonmem[ld1.post.8b]"
    );
    for operands in [
        vec![q3.clone(), x9.clone(), MachOperand::Imm(7)],
        vec![q3.clone(), x9.clone(), MachOperand::Imm(-1)],
        vec![d3.clone(), x9.clone(), MachOperand::Imm(1)],
        vec![s3, x9.clone(), MachOperand::Imm(0)],
        vec![q3.clone(), w9, MachOperand::Imm(1)],
        vec![q3.clone(), xzr, MachOperand::Imm(1)],
        vec![q3.clone(), x9.clone()],
        vec![q3, x9, MachOperand::Imm(1), MachOperand::Imm(0)],
    ] {
        let inst = MachInst::new(ld1, operands);
        assert!(bind_neon_structure_instruction(&inst).is_err(), "{inst:?}");
    }
}

#[test]
fn the_word_decoder_inverts_the_memory_effect_word_and_agrees_with_the_binder() {
    for (form, _) in NEON_STRUCTURE_FORMS {
        for base_sp in [false, true] {
            let inst = representative_neon_instruction(&form, base_sp);
            let word = crate::aarch64_memory_effect::memory_effect_word(&inst)
                .expect("the memory-effect lane admits the representative");
            assert_eq!(
                decode_neon_structure_word(word),
                Some(bind_neon_structure_instruction(&inst).unwrap()),
                "{word:#010x}"
            );
            // A register post-index (Rm = x0), another opcode field and the
            // big-endian bit 31 are not this form.
            for bad in [
                word & !(0b1_1111 << 16),
                word ^ (1 << 12),
                word | (1 << 31),
                word ^ (1 << 21),
            ] {
                assert_eq!(decode_neon_structure_word(bad), None, "{bad:#010x}");
            }
        }
    }
    // 1D (size 11, Q 0) is a valid encoding but no table form.
    let one_d = crate::neon_semantics::neon_ld1_st1_post_word(true, false, 3, 9, 3);
    assert_eq!(decode_neon_structure_word(one_d), None);
}

#[test]
fn the_wrong_theorem_is_not_the_faithful_query() {
    let wrong = representative_wrong_neon_theorem();
    let (form, _) = NEON_STRUCTURE_FORMS[5];
    let faithful = proof_neon_structure_form(&form).unwrap();
    assert_eq!(wrong.name, faithful.name);
    assert_ne!(
        crate::verdict_db::db_obligation_smt2(&wrong),
        crate::verdict_db::db_obligation_smt2(&faithful)
    );
}
