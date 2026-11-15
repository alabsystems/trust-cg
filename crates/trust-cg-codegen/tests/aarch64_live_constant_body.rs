// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Optimized constant bodies retain checked, refutable source-bound proofs.
#![cfg(feature = "verify")]

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_ir::{AArch64Opcode as M, MachOperand as O};
use trust_cg_verify::ay_bridge::{AYConfig, AYResult, verify_with_cli_raw_attributed};
use trust_cg_verify::source_bound_a64_body::{
    diagnostic_a64_body_obligation, source_bound_a64_body,
};
#[path = "common/source_bound_body_cases.rs"]
mod cases;

#[test]
fn folded_body_problems_are_independently_checked_and_refutable() {
    cases::on_big_stack(|| {
        let source = cases::captured_narrow_leaf();
        for prep in cases::PREPS {
            for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let machine = cases::prepare_as(prep, &source, level);
                let owner = source_bound_a64_body(&source, &machine)
                    .expect("all optimization levels must bind the original source");
                assert!(!owner.copies_and_constants().is_empty());
                if matches!(level, OptLevel::O2 | OptLevel::O3) {
                    assert!(owner.covered().is_empty());
                    assert_eq!(owner.copies_and_constants().len(), 1);
                }
                let admission = format!(
                    "covered={} constants={}",
                    owner.covered().len(),
                    owner.copies_and_constants().len()
                );
                let obligation = diagnostic_a64_body_obligation(&source, &machine).unwrap();
                let verdict = verify_with_cli_raw_attributed(&obligation, &AYConfig::default());
                println!(
                    "A64_CONSTANT_CHECKED {prep:?}/{level:?}: rows={} opcodes={:?} admission={admission} result={} {}",
                    machine.insts.len(),
                    machine
                        .insts
                        .iter()
                        .map(|row| row.opcode)
                        .collect::<Vec<_>>(),
                    verdict.result,
                    verdict.provenance()
                );
                assert!(matches!(verdict.result, AYResult::Verified), "{verdict:?}");
                let mut wrong = machine.clone();
                let first = wrong
                    .insts
                    .iter_mut()
                    .find(|row| {
                        matches!(
                            row.opcode,
                            M::Movz | M::MovI | M::MovR | M::MOVWrr | M::MOVXrr
                        )
                    })
                    .unwrap();
                let destination = first.operands[0].clone();
                first.opcode = M::Movz;
                first.operands = vec![destination, O::Imm(1)];
                let problem = diagnostic_a64_body_obligation(&source, &wrong).unwrap();
                let verdict = verify_with_cli_raw_attributed(&problem, &AYConfig::default());
                println!(
                    "A64_CONSTANT_MUTANT {prep:?}/{level:?}: {} {}",
                    verdict.result,
                    verdict.provenance()
                );
                assert!(
                    matches!(verdict.result, AYResult::CounterExample(_)),
                    "{verdict:?}"
                );
            }
        }
    });
}
