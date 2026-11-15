// trust-cg-codegen/examples/wasm_island_evidence.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Run the P4 obligation families over a SHIPPED island module.
//!
//! The P4 audit's closing finding: no P4 family ran over any module the
//! project actually distributes. Every corpus was a synthetic shape built
//! inside a test file — while the design makes *"the proof attaches to the
//! distributed artifact"* the lane's differentiator. An obligation that only
//! ever meets fixtures is evidence about fixtures.
//!
//! This closes that gap in the only direction that is honest: the families
//! take BYTES, so point them at the exact `.wasm` a visitor downloads.
//!
//!     scripts/trust_cargo.sh run --example wasm_island_evidence -- <module.wasm> [more.wasm ...]
//!
//! It runs, per module:
//!   * the module-indexing family (4) — every declared index resolves, imports
//!     occupy the low space, sections are ordered, vectors are exactly consumed
//!   * the wasm32 target-conformance family (6)
//!   * the CFG structural family (1) — br depths resolve to live labels, stack
//!     height/type consistency at joins
//!
//! and exits nonzero if any obligation is REFUTED, or if a module cannot be
//! decoded at all. Rows that do not apply to a module are reported as
//! NOT-APPLICABLE and are never counted as credit.
//!
//! WHAT A GREEN RUN DOES NOT SAY, because this is exactly where a reader
//! would over-read it: none of these families is a proof that the module
//! computes what its trust-ir computes. The CFG family is a NECESSARY
//! condition on structuring, not a bisimulation (which is a RED named
//! deferral). The indexing family says nothing about whether the lowering
//! chose the right values. The lane remains DIFFERENTIAL-EXPERIMENTAL, and
//! the execution differentials — trust-cg vs rustc/LLVM vs the interpreter,
//! re-run in every visitor's browser — remain the load-bearing evidence for
//! these artifacts. This adds structural evidence over the SAME bytes; it
//! does not replace that.

use std::process::ExitCode;

use trust_cg_verify::wasm_cfg_proofs::{self, CfgVerdict};
use trust_cg_verify::wasm_encoding_proofs::{self, Outcome};

fn main() -> ExitCode {
    let paths: Vec<String> = std::env::args().skip(1).collect();
    if paths.is_empty() {
        eprintln!(
            "usage: wasm_island_evidence <module.wasm> [more.wasm ...]\n\
             runs the P4 indexing / target-conformance / CFG-structural families over \
             SHIPPED module bytes"
        );
        return ExitCode::from(2);
    }

    let mut total_holds = 0usize;
    let mut total_na = 0usize;
    let mut total_refuted = 0usize;
    let mut failed_modules = 0usize;

    for path in &paths {
        let bytes = match std::fs::read(path) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("FAIL {path}: cannot read: {e}");
                failed_modules += 1;
                continue;
            }
        };
        println!("== {path} ({} bytes)", bytes.len());

        let mut holds = 0usize;
        let mut na = 0usize;
        let mut refuted = 0usize;
        let mut rows = wasm_encoding_proofs::module_indexing_obligations(&bytes);
        rows.extend(wasm_encoding_proofs::target_conformance_obligations(
            &bytes,
            &[],
        ));
        for row in &rows {
            match &row.outcome {
                Outcome::Holds => holds += 1,
                Outcome::NotApplicable(_) => na += 1,
                Outcome::Refuted(why) => {
                    refuted += 1;
                    println!("   REFUTED [{}] {}: {why}", row.family, row.name);
                }
            }
        }

        // The CFG structural verdict is three-valued: Inconclusive (an opcode
        // with no typing rule) is NOT credit and NOT a refutation — it is
        // reported as its own outcome, the same way the family's own gate
        // treats it.
        match wasm_cfg_proofs::check_module_structure(&bytes) {
            CfgVerdict::Holds(report) => {
                holds += 1;
                let funcs = report.functions.len();
                let insts: usize = report.functions.iter().map(|f| f.instructions).sum();
                let joins: usize = report.functions.iter().map(|f| f.joins_checked).sum();
                let branches: usize = report.functions.iter().map(|f| f.branches.len()).sum();
                println!(
                    "   holds   [cfg-structural] {funcs} fn, {insts} typed instructions, \
                     {branches} branch label(s) resolved, {joins} join(s) checked"
                );
            }
            CfgVerdict::Inconclusive(why) => {
                na += 1;
                println!("   INCONCLUSIVE [cfg-structural] (uncredited): {why:?}");
            }
            CfgVerdict::Refuted(violation) => {
                refuted += 1;
                println!("   REFUTED [cfg-structural] {violation:?}");
            }
        }

        println!("   {holds} holding, {na} not-applicable/inconclusive, {refuted} REFUTED");
        if refuted > 0 {
            failed_modules += 1;
        }
        total_holds += holds;
        total_na += na;
        total_refuted += refuted;
    }

    println!(
        "\nshipped-artifact evidence: {} module(s), {total_holds} holding, \
         {total_na} not-applicable/inconclusive, {total_refuted} REFUTED",
        paths.len()
    );
    println!(
        "NOT a correctness proof: the CFG family is a necessary condition, not a bisimulation \
         (RED deferral); the indexing family says nothing about the VALUES the lowering chose. \
         The lane stays differential-experimental."
    );

    if failed_modules > 0 {
        eprintln!("{failed_modules} module(s) REFUTED or unreadable");
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}
