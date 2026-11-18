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
#[path = "support/x86_suite_programs.rs"]
mod x86_suite_programs;

// crates/rustc-codegen-trust-cg/tests/bridge_feature_suites_aarch64.rs
//
// The AArch64 lane of the bridge's x86-64 feature suites (ledger L06-P3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The feature suites `tests/*_x86*.rs` (iterators, closures, dyn dispatch,
// enums and niches, drops and heap values, Vec/HashMap/BTreeMap/String,
// formatting, std `fn main`, statics, slices, unwinding, ...) compile for
// x86-64 and run only on an x86-64 host. Most of their programs are table
// literals, `(name, program, exit code)` or `(name, program)`.
// `support/x86_suite_programs.rs` reads those tables out of every suite that
// compiles for `host_target_support::X86_64_TARGET`, so a row added there is
// a row here, and this file runs every whole program natively on the host's
// AArch64 triple through `support/a64_differential.rs`: LLVM against this
// backend at -Copt-level 0 and 3, compared on exit status, stdout and stderr.
// A suite's pinned exit code is its checksum: the oracle must produce it.
//
// Each suite's panic strategy is its own (`-Cpanic=abort` where the suite
// spells it, unwinding otherwise). The backend runs with proof certificates
// off (`no-proof-certs`): a std program's certificates-on compile meets the
// AArch64 proof wall at `std::rt::lang_start` (`[TCG-PROOF-465]`, ledger
// L07-P2; `hello_loop`), so that lane is measured on the corpus
// (`bridge_differential_aarch64`), not here.
//
// The suites are partitioned into families, one test each; every harvested
// suite must belong to exactly one family. Every cell is compared with the
// committed census `tests/a64_census/feature_suites.txt` (one line per cell
// that does not build and match, and one `oracle` line per cell whose LLVM
// run differs from the suite's pinned code): a divergence is a miscompile and
// fails, an unlisted refusal is a regression, and a listed cell that now
// builds and matches fails until its line is removed. A row whose program a
// suite builds from fragments, macros or constants is not harvested and not
// run (53 rows on 2026-10-01; `x86_suite_programs::Harvest::other_rows`).
//
// Testing evidence for the host that ran it, in the explicit unverified Trust
// lane; not proof. On an aarch64 Linux host the file compiles for
// `aarch64-unknown-linux-gnu`; it has not yet run there.

use a64_differential::{Ending, Lane, Panic, Program, Tally};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

/// One line per cell that does not build and match, plus the oracle lines.
const CENSUS: &str = include_str!("a64_census/feature_suites.txt");

const OPT_LEVELS: [&str; 2] = ["0", "3"];

/// The census lane name for an oracle that differs from the suite's pin.
const ORACLE_LANE: &str = "oracle";

/// Every x86 feature suite with harvested programs, by family.
const FAMILIES: &[(&str, &[&str])] = &[
    (
        "closures",
        &[
            "closures_x86",
            "closure_capture_x86",
            "m96_closure_collection_x86",
            "m109_mono_method_link_x86",
        ],
    ),
    (
        "iterators",
        &[
            "iter_adapters_x86",
            "m99_iter_adapters_x86",
            "for_loops_x86",
            "m101_o3_gaps_x86",
            "m103_nested_collect_x86",
            "m139_flatmap_bounded_x86",
        ],
    ),
    (
        "dyn_enums_try",
        &[
            "dyn_dispatch_x86",
            "enum_match_x86",
            "niche_enum_x86",
            "narrow_repr_enum_x86",
            "try_operator_x86",
        ],
    ),
    (
        "heap_collections",
        &[
            "heap_types_x86",
            "heap_canary_x86",
            "vec_x86",
            "m94_vec_o3_x86",
            "m98_vec_collect_sort_x86",
            "m91_btreemap_x86",
            "m92_hashmap_x86",
        ],
    ),
    ("slice_capabilities", &["slice_capabilities_x86"]),
    (
        "strings_format",
        &[
            "m100_str_memcpy_x86",
            "m122_to_vec_string_from_x86",
            "m123_int_to_string_x86",
            "m127_to_vec_o3_x86",
            "m129_string_from_o3_x86",
            "m140_println_x86",
            "m90_format_x86",
        ],
    ),
    (
        "std_main_statics_memory",
        &[
            "std_main_run_x86",
            "std_breadth_x86",
            "static_data_x86",
            "m124_static_mut_slice_write_x86",
            "m130_cross_static_ptreq_x86",
            "memory_model_x86",
            "memory_model_aggregates_x86",
            "cell_interior_mut_x86",
        ],
    ),
    (
        "slices_aggregates_numerics",
        &[
            "slice_fatptr_x86",
            "slice_index_x86",
            "slice_split_first_last_x86",
            "m125_reassign_slice_ref_x86",
            "m113_array_raw_eq_x86",
            "m111_byval_aggregate_x86",
            "m117_byval_float_aggregate_return_x86",
            "m110_bitmanip_x86",
            "m112_fround_x86",
        ],
    ),
    (
        "panics_unwind",
        &["panic_unwind_raise_x86", "m94_track_caller_unwrap_x86"],
    ),
];

/// Every x86 feature suite's harvested programs, keyed by suite. Panics when
/// a suite's tables cannot be read or a harvested suite has no family.
fn harvest_all() -> BTreeMap<String, Vec<Program>> {
    x86_suite_programs::self_check();
    let tests = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    let mut suites = BTreeMap::new();
    let mut entries: Vec<_> = std::fs::read_dir(&tests)
        .expect("read the bridge tests directory")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "rs"))
        .collect();
    entries.sort();
    for path in entries {
        let text = std::fs::read_to_string(&path).expect("read a bridge test");
        if !text.contains("host_target_support::X86_64_TARGET") {
            continue;
        }
        let suite = path
            .file_stem()
            .and_then(|stem| stem.to_str())
            .expect("UTF-8 test name")
            .to_owned();
        let harvest = x86_suite_programs::harvest(&suite, &text)
            .unwrap_or_else(|error| panic!("cannot read the program tables of {suite}: {error}"));
        if harvest.programs.is_empty() {
            continue;
        }
        // A suite that never asks for `-Cpanic=abort` unwinds.
        let panic = if text.contains("-Cpanic=abort") {
            Panic::Abort
        } else {
            Panic::Unwind
        };
        let mut ids = BTreeSet::new();
        let programs: Vec<Program> = harvest
            .programs
            .into_iter()
            .map(|program| {
                let name: String = program
                    .name
                    .chars()
                    .map(|c| if c.is_whitespace() { '_' } else { c })
                    .collect();
                let id = format!("{suite}/{name}");
                assert!(ids.insert(id.clone()), "duplicate harvested program {id}");
                Program {
                    id,
                    src: program.src,
                    panic,
                    overflow_checks_off: false,
                    expected: program.expected,
                }
            })
            .collect();
        suites.insert(suite, programs);
    }
    let mut assigned = BTreeSet::new();
    for (family, members) in FAMILIES {
        for suite in *members {
            assert!(
                assigned.insert(*suite),
                "suite {suite} belongs to more than one family (second: {family})"
            );
        }
    }
    let harvested: BTreeSet<&str> = suites.keys().map(String::as_str).collect();
    let unassigned: Vec<&&str> = harvested.difference(&assigned).collect();
    let vanished: Vec<&&str> = assigned.difference(&harvested).collect();
    assert!(
        unassigned.is_empty() && vanished.is_empty(),
        "the feature-suite families must partition the harvested suites exactly: \
         harvested but in no family {unassigned:?}; in a family but harvested no program {vanished:?}"
    );
    suites
}

fn run_family(test: &str, family: &str, proofs_off_knob: &str) {
    a64_differential::require_prerequisites(test);
    let suites = harvest_all();
    let members = FAMILIES
        .iter()
        .find(|(name, _)| *name == family)
        .map(|(_, members)| *members)
        .unwrap_or_else(|| panic!("no family {family}"));
    let programs: Vec<Program> = members
        .iter()
        .flat_map(|suite| suites[*suite].iter().cloned())
        .collect();
    let dylib = backend_artifact_support::current_test_backend();
    let cells = a64_differential::run_cells(
        family,
        &dylib,
        &programs,
        &OPT_LEVELS,
        Lane::ProofsOff,
        proofs_off_knob,
    );
    let census = a64_differential::parse_census(CENSUS);
    let owns = |id: &str| {
        members
            .iter()
            .any(|suite| id.starts_with(&format!("{suite}/")))
    };
    let mut problems =
        a64_differential::check_against_census(Lane::ProofsOff, &cells, &census, &owns);

    // The suite's pinned exit code is the program's checksum: the oracle must
    // produce it, except the census's `oracle` lines (each with the oracle's
    // actual ending), which only shrink.
    let mut oracle_census = Vec::new();
    for cell in &cells {
        let (Some(code), Some(oracle)) = (cell.expected, &cell.oracle) else {
            continue;
        };
        let key = (ORACLE_LANE.to_owned(), cell.id.clone(), cell.opt.to_owned());
        let actual = match &oracle.ending {
            Ending::Exited(actual) => format!("exit-{actual}"),
            Ending::Signalled(signal) => format!("signal-{signal}"),
            Ending::TimedOut => "timeout".to_owned(),
        };
        let pinned = census.get(&key);
        if oracle.ending == Ending::Exited(code) {
            if pinned.is_some() {
                problems.push(format!(
                    "`{}` -Copt-level={}: the oracle now exits {code} as pinned; remove its oracle line",
                    cell.id, cell.opt
                ));
            }
            continue;
        }
        oracle_census.push(format!("{ORACLE_LANE} {} O{} {actual}", cell.id, cell.opt));
        if pinned != Some(&actual) {
            problems.push(format!(
                "`{}` -Copt-level={}: LLVM ended {actual}, the suite pins exit {code}, census says {pinned:?}",
                cell.id, cell.opt
            ));
        }
    }
    // A cell whose oracle now meets its pin is flagged above; an oracle line
    // naming no cell of this run is stale.
    for (lane, id, opt) in census.keys() {
        if lane == ORACLE_LANE && owns(id) && !cells.iter().any(|c| &c.id == id && c.opt == opt) {
            problems.push(format!(
                "census line `oracle {id} O{opt}` names no cell of this run"
            ));
        }
    }

    let tally = Tally::of(&cells);
    let summary = format!(
        "A64_FEATURE_SUITES family={family} suites={} programs={} cells={} llvm_runs={} cg_runs={} \
         matched={} refused={} refusals={} panic_message={} diverged={} unbuildable={} \
         oracle_off_pin={}",
        members.len(),
        programs.len(),
        tally.cells,
        tally.cells - tally.unbuildable,
        tally.matched + tally.diverged + tally.panic_message,
        tally.matched,
        tally.refused(),
        tally.spell_refusals(),
        tally.panic_message,
        tally.diverged,
        tally.unbuildable,
        tally.oracle_off_pin
    );
    assert!(
        problems.is_empty(),
        "{summary}\nAArch64 feature suites ({family}): {} problem(s):\n{}\n\nthis run's census \
         lines:\n{}\n{}",
        problems.len(),
        problems.join("\n"),
        a64_differential::census_lines(Lane::ProofsOff, &cells),
        oracle_census.join("\n")
    );
    // Printed only once the census has been met.
    println!("{summary}");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// Capturing closures, closure collections and monomorphized method links.
#[test]
fn closures_match_llvm_natively() {
    let knob = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    run_family("closures_match_llvm_natively", "closures", &knob);
}

/// Iterator adapters and terminals, `for` loops, nested collects, flat maps.
#[test]
fn iterators_match_llvm_natively() {
    let knob = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    run_family("iterators_match_llvm_natively", "iterators", &knob);
}

/// `dyn` dispatch, enums, niches, narrow reprs and the `?` operator.
#[test]
fn dyn_enums_try_match_llvm_natively() {
    let knob = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    run_family("dyn_enums_try_match_llvm_natively", "dyn_enums_try", &knob);
}

/// Box/Vec/String heap values and drops, Vec at -O3, sorts, BTreeMap, HashMap.
#[test]
fn heap_collections_match_llvm_natively() {
    let knob = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    run_family(
        "heap_collections_match_llvm_natively",
        "heap_collections",
        &knob,
    );
}

/// Format fallback, Box payload drop and aggregate array-element stores.
#[test]
fn slice_capabilities_match_llvm_natively() {
    let knob = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    run_family(
        "slice_capabilities_match_llvm_natively",
        "slice_capabilities",
        &knob,
    );
}

/// `str` copies, `to_vec`/`String::from`, integer formatting and `println!`.
#[test]
fn strings_format_match_llvm_natively() {
    let knob = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    run_family(
        "strings_format_match_llvm_natively",
        "strings_format",
        &knob,
    );
}

/// std `fn main`, std breadth, statics, the memory model and interior mutability.
#[test]
fn std_main_statics_memory_match_llvm_natively() {
    let knob = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    run_family(
        "std_main_statics_memory_match_llvm_natively",
        "std_main_statics_memory",
        &knob,
    );
}

/// Slices and fat pointers, by-value aggregates, bit manipulation, rounding.
#[test]
fn slices_aggregates_numerics_match_llvm_natively() {
    let knob = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    run_family(
        "slices_aggregates_numerics_match_llvm_natively",
        "slices_aggregates_numerics",
        &knob,
    );
}

/// Panics that unwind and are raised, and `#[track_caller]` unwraps.
#[test]
fn panics_unwind_match_llvm_natively() {
    let knob = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    run_family("panics_unwind_match_llvm_natively", "panics_unwind", &knob);
}
