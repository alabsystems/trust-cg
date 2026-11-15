// trust-cg-cli/tests/must_refuse_corpus.rs — trust-ir's must-refuse corpus,
// handed to the REAL `trust-cg` binary (KIND 4 part 2, 2026-09-24).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The in-process lanes live in trust-cg-codegen `tests/must_refuse_corpus.rs`
//! (module docs there). This target is the CLI PATH: every artifact row of the
//! pinned trust-ir's corpus is written to disk as a `.tmbc` and compiled by
//! the `trust-cg` binary, recognizing the corpus's structural license
//! authority for the run (`--recognize-authority`), on three lanes:
//!
//! | lane          | invocation                                              |
//! |---------------|---------------------------------------------------------|
//! | `native`      | `--target <row's triple> -c -o <row>.o <row>.tmbc`      |
//! | `wasm-module` | `--target wasm32-unknown-unknown -o <row>.wasm <row>.tmbc` (the closed module) |
//! | `wasm-object` | `--target wasm32-unknown-unknown -c -o <row>.o <row>.tmbc` (the relocatable object) |
//!
//! A wasm lane's input is the row RETARGETED to wasm32 as the codegen
//! target's wasm lanes retarget it (a row declaring no target or the
//! canonical one takes the wasm32 machine shape and keeps its
//! `struct_passing` claim; a row pinned elsewhere stays pinned), re-encoded by
//! trust-cg's own tMBC writer, and checked to read back as exactly that
//! module, so the bytes differ from the row only by the retargeting. A row
//! trust-cg's reader refuses has no module to retarget and is handed over
//! unchanged (the reader refuses it before any target is read). A must-refuse
//! row must exit non-zero AND leave no output; the control row must exit zero
//! and write one. A row the corpus adds fails by name (`uncovered`).
//!
//! Each lane's known-accepted list is exact in both directions (see the
//! codegen target's docs) and is expected to agree with that target's
//! in-process lane behind the same entry: `native` with `aot-compiler`
//! (`compile_one`), `wasm-module` and `wasm-object` with the lanes of those
//! names.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;
use std::process::Command;

use trust_cg_codegen::pipeline::{encode_tmbc, load_module_from_bytes};
use trust_ir::Module;
use trust_ir_conformance::refuse::{Report, Row, STRUCTURAL_LICENSE_AUTHORITY, corpus};

const CANONICAL_TARGET: &str = "aarch64-apple-darwin";

/// Must-refuse rows the CLI compiles today on every lane, with the reason.
/// Exact, and the same rows the in-process `aot-compiler` and wasm lanes
/// accept, each defended there (`COMPILER_LANES_ACCEPT` in the codegen
/// target): `compile_one` is the `aot-compiler` lane behind argument parsing
/// and file I/O.
/// The two recorded format/backend disagreements (`dealloc_instruction`, the
/// retired `vector_unsigned_cmp_wide_lanes_x86`) left this table when trust-ir
/// and this backend came to state and enforce one rule each (trust-ir
/// `7b0947ee`).
const KNOWN_ACCEPTED: &[(&str, &str)] = &[
    (
        "completeness_unclaimed",
        "no completeness need; None is no claim, every Some refused",
    ),
    (
        "trusted_status_row",
        "no codegen decision from an obligation's status",
    ),
];

/// One CLI lane: how the row is handed to the binary, and what it accepts.
struct CliLane {
    name: &'static str,
    /// `None`: the row's own target (`native`); `Some`: the wasm32 lane, with
    /// `-c` (the object) or without (the closed module).
    wasm_compile_only: Option<bool>,
    known_accepted: &'static [(&'static str, &'static str)],
}

const LANES: &[CliLane] = &[
    CliLane {
        name: "native",
        wasm_compile_only: None,
        known_accepted: KNOWN_ACCEPTED,
    },
    CliLane {
        name: "wasm-module",
        wasm_compile_only: Some(false),
        known_accepted: KNOWN_ACCEPTED,
    },
    CliLane {
        name: "wasm-object",
        wasm_compile_only: Some(true),
        known_accepted: KNOWN_ACCEPTED,
    },
];

/// The codegen target's `retarget_to_wasm32`, over the module trust-cg's
/// reader produced.
fn retarget_to_wasm32(mut module: Module) -> Module {
    let wasm32 = trust_cg_codegen::wasm::wasm32_target_info();
    module.target_info = match module.target_info.take() {
        None => Some(wasm32),
        Some(info) if info.triple == CANONICAL_TARGET => Some(trust_ir::TargetInfo {
            struct_passing: info.struct_passing,
            ..wasm32
        }),
        pinned => pinned,
    };
    module
}

/// The bytes a wasm lane hands the binary for `row` (module docs).
fn wasm_input(row: &Row) -> Vec<u8> {
    let Ok(module) = load_module_from_bytes(row.wire_bytes()) else {
        return row.wire_bytes().to_vec();
    };
    let retargeted = retarget_to_wasm32(module);
    let bytes = encode_tmbc(&retargeted)
        .unwrap_or_else(|error| panic!("{}: the retargeted module has no tMBC: {error}", row.id()));
    let reread = load_module_from_bytes(&bytes)
        .unwrap_or_else(|error| panic!("{}: the retargeted tMBC does not read: {error}", row.id()));
    assert!(
        reread == retargeted,
        "{}: the retargeted tMBC reads back as a different module",
        row.id()
    );
    bytes
}

fn admit(directory: &Path, lane: &CliLane, row: &Row) -> Result<(), String> {
    let input = format!("{}-{}.tmbc", lane.name, row.id());
    let (bytes, mut args) = match lane.wasm_compile_only {
        None => {
            let triple = row
                .module()
                .and_then(|m| m.target_info.as_ref())
                .map_or(CANONICAL_TARGET, |t| t.triple.as_str())
                .to_string();
            (
                row.wire_bytes().to_vec(),
                vec!["--target".to_string(), triple, "-c".to_string()],
            )
        }
        Some(compile_only) => {
            let mut args = vec![
                "--target".to_string(),
                trust_cg_codegen::wasm::WASM32_TRIPLE.to_string(),
            ];
            if compile_only {
                args.push("-c".to_string());
            }
            (wasm_input(row), args)
        }
    };
    let output_name = format!(
        "{}-{}.{}",
        lane.name,
        row.id(),
        if lane.wasm_compile_only == Some(false) {
            "wasm"
        } else {
            "o"
        }
    );
    fs::write(directory.join(&input), bytes).expect("write row");
    args.extend([
        "--recognize-authority".to_string(),
        STRUCTURAL_LICENSE_AUTHORITY.to_string(),
        "-o".to_string(),
        output_name.clone(),
        input,
    ]);
    let output = Command::new(env!("CARGO_BIN_EXE_trust-cg"))
        .current_dir(directory)
        .args(&args)
        .output()
        .expect("run trust-cg");
    let wrote_output = directory.join(&output_name).exists();
    if output.status.success() {
        assert!(
            wrote_output,
            "{}: {}: trust-cg exited 0 but wrote no output",
            lane.name,
            row.id()
        );
        return Ok(());
    }
    assert!(
        !wrote_output,
        "{}: {}: trust-cg failed yet left an output behind",
        lane.name,
        row.id()
    );
    Err(format!(
        "exit {:?}: {}",
        output.status.code(),
        String::from_utf8_lossy(&output.stderr).trim()
    ))
}

#[test]
fn the_trust_cg_binary_refuses_every_must_refuse_row_and_compiles_the_control() {
    let rows =
        corpus().expect("the pinned must-refuse corpus loads (a vacuous one is a typed error)");
    let handled: Vec<&str> = rows.iter().map(Row::id).collect();
    assert!(
        rows.uncovered(&handled).is_empty(),
        "{:?}",
        rows.uncovered(&handled)
    );
    let directory = tempfile::tempdir().expect("tempdir");
    let mut failures: Vec<String> = Vec::new();
    for lane in LANES {
        let report = Report::run(&rows, |row| admit(directory.path(), lane, row));
        check_lane(lane, &rows, &report, &mut failures);
    }
    assert!(
        failures.is_empty(),
        "must-refuse corpus via the trust-cg binary ({} lanes): {} finding(s)\n  {}",
        LANES.len(),
        failures.len(),
        failures.join("\n  ")
    );
}

/// Each pinned row is refused by the arm that states its rule, not by an
/// unrelated license or lowering failure, on every lane, and names a row of
/// the PINNED corpus: a row retired at the pin fails by name, whichever group
/// it is in. The accepted lists may shrink when a formerly admitted route now
/// refuses faithfully; adding waivers is not a migration strategy.
///
/// The formula rows reach their own admission refusal. The owner decisions
/// (trust-ir 7b0947ee) are the ones that still have a corpus row. The x86-64
/// per-cell vector-compare rule has none at this pin: its last row,
/// `vector_unsigned_cmp_bytes_x86`, retired upstream with the four unsigned
/// `v16_i8` cells it named (trust-ir 72dee4b6), and the rule is a `none` row
/// there (`vector_icmp_fail_closed_cell_x86`). The license-evidence rows and
/// the body and ABI rows below are refused on the wasm32 lanes by the same
/// rules, decided in the same words, as on the native lane.
const FORMULA: &str = "formula states two SMT-LIB texts";
const PINNED_REASONS: &[(&str, &str)] = &[
    ("formula_smtlib_rendering_disagrees", FORMULA),
    ("summary_clause_smtlib_rendering_disagrees", FORMULA),
    ("spec_carrier_smtlib_rendering_disagrees", FORMULA),
    ("pred_citation_rendering_disagrees", FORMULA),
    ("dealloc_instruction", "[TCG-DEALLOC]"),
    ("assert_panic_kind_unspecified", "unspecified panic kind"),
    (
        "struct_passing_unclassified_refined_aggregate",
        "unclassified",
    ),
    (
        "struct_passing_unclassified_vector_by_value",
        "unclassified",
    ),
    (
        "struct_passing_unclassified_closure_by_value",
        "unclassified",
    ),
    (
        "struct_passing_unclassified_by_value_aggregate",
        "unclassified",
    ),
    (
        "struct_passing_always_memory_by_value_aggregate",
        "AlwaysMemory",
    ),
    (
        "body_gate_kernel_tv_without_certificate",
        "without the evidence it names",
    ),
    ("body_gate_refuted_by_failed_tv", "revokes the license"),
    // trust-ir v61 license evidence (the codegen target's lanes name both).
    (
        "body_gate_evidence_stale_body_digest",
        "GateEvidence does not hold",
    ),
    (
        "body_gate_kernel_tv_evidence_unrecorded",
        "evidence-bound gate authority \"clean-kernel-tv\" with no GateEvidence",
    ),
    ("region_havoc_store", "RegionHavocStore"),
    (
        "undef_fresh_havoc_feeds_assume",
        "FreshSymbolicHavoc-marked undef",
    ),
    (
        "narrow_arg_ext_unrecorded_darwin",
        "no recorded argument extension",
    ),
    ("array_splat_non_array_type", "InvalidArraySplat"),
    // The incoming selector-type case rule, reached on all three CLI lanes.
    ("switch_case_negative_at_unsigned", "const type mismatch"),
    ("switch_case_above_signed_max", "const type mismatch"),
    // WS7.3: every ingestion entry runs trust-ir's validator first, so the
    // row is refused by the corpus's own verdict
    // (`validate_module=Validation:PointerOpInvalid`), before the adapter's
    // later "requires a pointer-like type" arm is reached.
    ("ptr_data_of_non_pointer", "PointerOpInvalid: bb0: ptr_data"),
    // WS7.3: every ingestion entry validates under the authority tier's
    // import policy, so a proved summary `backed_by` an import this entry
    // cannot authenticate is refused at its subject on all three lanes
    // (`validate_module_with_authority=Validation:UnauthenticatedImport`).
    (
        "import_backed_summary_unauthenticated",
        "UnauthenticatedImport: import #0 (backed_by)",
    ),
    // A level-S template blob (amendment S) is refused by its magic, by name.
    (
        "template_blob_is_not_a_module",
        trust_cg_codegen::pipeline::TEMPLATE_IS_NOT_A_MODULE,
    ),
];

fn check_lane(lane: &CliLane, rows: &[Row], report: &Report, failures: &mut Vec<String>) {
    let name = lane.name;
    for (id, outcome) in report.outcomes() {
        eprintln!("cli {name}: {id}: {outcome:?}");
    }
    for id in report.controls_refused(rows) {
        failures.push(format!(
            "{name}: control row `{id}` REFUSED: {}",
            report.message(id).unwrap_or("")
        ));
    }
    for id in report.uncovered(rows) {
        failures.push(format!("{name}: row `{id}` not dispatched"));
    }
    for id in report.refused() {
        let message = report.message(id).unwrap_or("");
        if message.contains(STRUCTURAL_LICENSE_AUTHORITY) {
            failures.push(format!(
                "{name}: `{id}` refused by the license layer, not its subject: {message}"
            ));
        }
    }
    let accepted: BTreeSet<&str> = report.must_refuse_accepted(rows).into_iter().collect();
    let known: BTreeSet<&str> = lane
        .known_accepted
        .iter()
        .map(|(id, _)| {
            assert!(
                rows.iter()
                    .any(|row| row.id() == *id && row.manifest.must_refuse()),
                "{name}: KNOWN_ACCEPTED names `{id}`, not a must-refuse corpus row"
            );
            *id
        })
        .collect();
    for id in accepted.difference(&known) {
        failures.push(format!(
            "{name}: must-refuse row `{id}` COMPILED by trust-cg; refuse it or list it in the \
             lane's KNOWN_ACCEPTED with the reason"
        ));
    }
    for id in known.difference(&accepted) {
        failures.push(format!(
            "{name}: `{id}` is listed KNOWN_ACCEPTED but is now refused: delete its line"
        ));
    }
    for (row, needle) in PINNED_REASONS {
        if !rows.iter().any(|candidate| candidate.id() == *row) {
            failures.push(format!(
                "`{row}` is pinned with `{needle}` but is not a corpus row at the pinned \
                 trust-ir (retired at the pin? delete its line)"
            ));
            continue;
        }
        match report.message(row) {
            Some(message) if message.contains(needle) => {}
            Some(message) => failures.push(format!(
                "{name}: `{row}` refused, but not by `{needle}`: {message}"
            )),
            None => failures.push(format!(
                "{name}: `{row}` expected refused with `{needle}` but was accepted"
            )),
        }
    }
}
