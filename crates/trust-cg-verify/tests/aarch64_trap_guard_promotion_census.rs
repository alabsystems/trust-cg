// trust-cg-verify/tests/aarch64_trap_guard_promotion_census.rs - trap-guard promotion census
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Promotion census of the trap-guard fixtures (L04-P12): every exact guard
//! carrier kind, width and idiom, plus a source `Trap`, prepared through the
//! real AArch64 pipeline at O0 and O2 and verified under the compiler's
//! proof-promotion policy with the enforced source cross-check. It prints one
//! `TRAP-CENSUS` line per function and one `TRAP-CENSUS-ROW` line per emitted
//! row, and asserts nothing about them: it uses no trap-guard API, so the same
//! file runs on a tree before the obligation existed and the two outputs
//! compare row by row (reports/2026-10-04-l04p12-trap-guard-obligations).

#[path = "support/trap_guard_fixtures.rs"]
mod fixtures;

use trust_cg_verify::function_verifier::FunctionVerifier;
use trust_cg_verify::lowering_proof::VerificationConfig;
use trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode;

#[test]
fn trap_guard_fixture_promotion_census() {
    let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
    let mut functions = 0;
    for fixture in fixtures::fixtures() {
        for opt in fixtures::LEVELS {
            let machine = fixtures::prepare(&fixture, opt);
            let report = verifier.verify_with_lir_source_and_mode(
                &machine,
                Some(&fixture.lir),
                ProvenanceXCheckMode::Enforce,
            );
            let inventory = report.emitted_opcode_inventory();
            println!(
                "TRAP-CENSUS\t{}\t{opt:?}\tpromotable={}\trows={}\tblocking={}",
                fixture.name,
                inventory.is_promotable(),
                inventory.entries.len(),
                inventory.uncovered_non_pseudo_opcodes().len()
            );
            for entry in &inventory.entries {
                let detail: String = entry
                    .detail
                    .replace(['\t', '\n'], " ")
                    .chars()
                    .take(200)
                    .collect();
                println!(
                    "TRAP-CENSUS-ROW\t{}\t{opt:?}\t{}\t{}\t{}\t{detail}",
                    fixture.name, entry.inst_index, entry.opcode, entry.status
                );
            }
            functions += 1;
        }
    }
    assert_eq!(
        functions,
        fixtures::fixtures().len() * fixtures::LEVELS.len()
    );
}
