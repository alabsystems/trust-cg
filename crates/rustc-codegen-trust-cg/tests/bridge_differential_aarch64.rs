// Compiled only on an AArch64 host: another host builds this target with no
// test in it, never one that passes without running (L06-P10).
#![cfg(target_arch = "aarch64")]

#[path = "support/a64_differential.rs"]
mod a64_differential;
#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// crates/rustc-codegen-trust-cg/tests/bridge_differential_aarch64.rs
//
// The AArch64 lane of the bridge differential corpus (ledger L06-P3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// `bridge_differential_x86.rs` owns the corpus: its `corpus()` table names
// every program (one `tests/bridge_corpus/*.rs` file per case) and why it is
// there. That lane compiles for x86-64 and runs only on an x86-64 host, so on
// an AArch64 host the whole corpus used to skip. This file reads the same
// table (the x86 file is included as text and its `corpus()` rows are parsed,
// so a case added there is a case here) and runs every program natively on
// the host's AArch64 triple through `support/a64_differential.rs`: LLVM
// against this backend with the x86 lane's flags
// (`-Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1`), compared on exit
// status, stdout and stderr. The corpus programs' checksums are their exit
// codes and output, so a wrong value is a divergence.
//
// Two backend lanes, each against the committed census
// `tests/a64_census/bridge_corpus.txt` (one line per cell that does not build
// and match):
//
//   * PROOFS OFF (`no-proof-certs`, a diagnostic lane that isolates lowering
//     from the AArch64 proof inventory), at -Copt-level 0, 2 and 3.
//   * CERTIFICATES ON (the default lane), at -Copt-level 2. AArch64 functions
//     meet the proof wall here (`[TCG-PROOF-465]`, ledger L07-P2), so this lane
//     is a refusal census; every cell that builds must still match LLVM.
//
// In both, a divergence is a miscompile and fails; a refusal the census does
// not list is a regression; a listed cell that now builds and matches fails
// until its line is removed. Testing evidence for the host that ran it, in
// the explicit unverified Trust lane; not proof. On an aarch64 Linux host the
// file compiles for `aarch64-unknown-linux-gnu`; it has not yet run there.

use a64_differential::{Lane, Panic, Program, Tally};
use std::path::Path;

/// The x86 lane, read for its `corpus()` table only.
const X86_LANE: &str = include_str!("bridge_differential_x86.rs");

/// One line per corpus cell that does not build and match.
const CENSUS: &str = include_str!("a64_census/bridge_corpus.txt");

/// The proofs-off lane's levels.
const OPT_LEVELS: [&str; 3] = ["0", "2", "3"];

/// The certificates-on lane runs one level. Its full three-level census
/// (2026-10-01, 462 cells) built none: 435 refused at `[TCG-PROOF-465]` and
/// 27 earlier in lowering, and it took 30 minutes, almost all of it proof
/// work. One level keeps the lane inside the runner's per-target budget and
/// still names the first cell that builds once the wall moves.
const CERTS_ON_OPT_LEVELS: [&str; 1] = ["2"];

fn between<'a>(text: &'a str, open: &str, close: &str) -> Option<&'a str> {
    let start = text.find(open)? + open.len();
    let len = text[start..].find(close)?;
    Some(&text[start..start + len])
}

/// The rows of the x86 lane's `corpus()` table, in order, with their sources
/// read from `tests/bridge_corpus`. Panics, naming the defect, when the table
/// cannot be read exactly: every row is one `Case { name, bug_ref, src:
/// include_str!("bridge_corpus/<file>") }`.
fn corpus() -> Vec<Program> {
    let header = "fn corpus() -> Vec<Case> {";
    let start = X86_LANE
        .find(header)
        .expect("bridge_differential_x86.rs has no `fn corpus() -> Vec<Case>` table");
    let table = &X86_LANE[start + header.len()..];
    let table = &table[..table
        .find("\n}\n")
        .expect("the x86 corpus() table has no closing brace at column 0")];
    let include = "include_str!(\"bridge_corpus/";
    let mut programs = Vec::new();
    for row in table.split("Case {").skip(1) {
        let name = between(row, "name: \"", "\"").expect("corpus row without a name");
        let file = between(row, include, "\")").expect("corpus row without an include_str! source");
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join("bridge_corpus")
            .join(file);
        let src = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("corpus row `{name}`: cannot read {path:?}: {error}"));
        programs.push(Program {
            id: name.to_owned(),
            src,
            panic: Panic::Abort,
            overflow_checks_off: true,
            expected: None,
        });
    }
    assert_eq!(
        programs.len(),
        table.matches(include).count(),
        "every x86 corpus row must be one `Case {{ .. }}` with one bridge_corpus source"
    );
    let mut names: Vec<&str> = programs.iter().map(|p| p.id.as_str()).collect();
    names.sort_unstable();
    names.dedup();
    assert_eq!(
        names.len(),
        programs.len(),
        "x86 corpus case names must be unique"
    );
    assert!(
        programs.iter().all(|p| !p.id.contains(char::is_whitespace)),
        "x86 corpus case names must not contain whitespace"
    );
    assert!(
        !programs.is_empty(),
        "the x86 corpus table parsed to no cases"
    );
    programs
}

fn run_lane(test: &str, lane: Lane, proofs_off_knob: &str) {
    a64_differential::require_prerequisites(test);
    let programs = corpus();
    let levels: &[&'static str] = if lane == Lane::CertsOn {
        &CERTS_ON_OPT_LEVELS
    } else {
        &OPT_LEVELS
    };
    let dylib = backend_artifact_support::current_test_backend();
    let cells = a64_differential::run_cells(
        lane.label(),
        &dylib,
        &programs,
        levels,
        lane,
        proofs_off_knob,
    );
    let census = a64_differential::parse_census(CENSUS);
    let problems = a64_differential::check_against_census(lane, &cells, &census, &|_| true);
    let tally = Tally::of(&cells);
    let summary = format!(
        "A64_CORPUS lane={} cases={} cells={} llvm_runs={} cg_runs={} matched={} refused={} \
         refusals={} panic_message={} diverged={}",
        lane.label(),
        programs.len(),
        tally.cells,
        tally.cells - tally.unbuildable,
        tally.matched + tally.diverged + tally.panic_message,
        tally.matched,
        tally.refused(),
        tally.spell_refusals(),
        tally.panic_message,
        tally.diverged
    );
    assert!(
        problems.is_empty(),
        "{summary}\nAArch64 bridge corpus ({}): {} problem(s):\n{}\n\nthis run's census lines for \
         the lane:\n{}",
        lane.label(),
        problems.len(),
        problems.join("\n"),
        a64_differential::census_lines(lane, &cells)
    );
    // Printed only once the census has been met.
    println!("{summary}");
}

/// Proofs off: every corpus cell builds and matches LLVM natively, except the
/// census's refusals, each by its exact diagnostic code.
#[test]
fn bridge_corpus_proofs_off_matches_llvm_natively() {
    // Built on the test thread: the knob trace belongs to this test.
    let knob = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    run_lane(
        "bridge_corpus_proofs_off_matches_llvm_natively",
        Lane::ProofsOff,
        &knob,
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// Certificates on: every corpus cell either builds, runs and matches LLVM,
/// or refuses with exactly the census's `[TCG-*]` code. Its claim is the
/// refusal census of the proof wall (most cells refuse at `[TCG-PROOF-465]`),
/// so it is credited as an expected refusal; the cells that build are run.
#[test]
fn bridge_corpus_certs_on_matches_llvm_or_refuses_by_name() {
    run_lane(
        "bridge_corpus_certs_on_matches_llvm_or_refuses_by_name",
        Lane::CertsOn,
        "",
    );
    positive_evidence::record(
        positive_evidence::Evidence::ExpectedRefusal,
        positive_evidence::Certs::On,
    );
}
