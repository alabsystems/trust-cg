// Symbolic execution: fixture-backed real-function corpus gate
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Fixture-backed fsym corpus gate for #862 / #377.
//!
//! The fixtures are serialized `trust_ir::Module` values generated from embedded
//! LLVM IR snippets through `trust_cg_llvm_import::import_text`. The test keeps
//! importer provenance and scanner/solver accounting pinned in the manifest.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use serde::Deserialize;
use trust_cg_verify::fsym_summary::{FsymSolverEscalationConfig, FsymSummary};
use trust_cg_verify::fsym_trust_ir::{FsymTrustIrDiagnosticKind, FsymTrustIrSkipReason};
use trust_ir::Module;

const FIXTURE_DIR: &str = "tests/fixtures/fsym_real_function_corpus";
const MANIFEST: &str = include_str!("fixtures/fsym_real_function_corpus/manifest.json");

#[derive(Debug, Deserialize)]
struct Manifest {
    issue: u32,
    parent_issue: u32,
    description: String,
    generated_with: GeneratedWith,
    acceptance: Acceptance,
    totals: CorpusTotals,
    fixtures: Vec<FixtureManifest>,
}

#[derive(Debug, Deserialize)]
struct GeneratedWith {
    import_api: String,
    fixture_format: String,
    source_commit: String,
}

#[derive(Debug, Deserialize)]
struct Acceptance {
    min_imported_functions: usize,
    min_scanned: usize,
    max_false_positive_basis_points: usize,
    safe_corpus: bool,
}

#[derive(Debug, Clone, Default, Deserialize, PartialEq, Eq)]
struct CorpusTotals {
    imported_functions: usize,
    module_functions: usize,
    scanned: usize,
    skipped: usize,
    unknown: usize,
    concrete_ub: usize,
    false_positive_basis_points: usize,
    solver: SolverCounts,
}

#[derive(Debug, Clone, Default, Deserialize, PartialEq, Eq)]
struct SolverCounts {
    results: usize,
    proven_safe: usize,
    concrete_ub: usize,
    remaining_unknown: usize,
}

#[derive(Debug, Deserialize)]
struct FixtureManifest {
    file: String,
    module: String,
    source_family: String,
    provenance: Vec<String>,
    imported_functions: Vec<String>,
    module_functions: usize,
    module_function_names: Vec<String>,
    scanned: usize,
    skipped: usize,
    unknown: usize,
    concrete_ub: usize,
    false_positive_basis_points: usize,
    skips: Vec<SkipPin>,
    unknowns: Vec<UnknownPin>,
    diagnostics: Vec<DiagnosticPin>,
    solver: SolverCounts,
    solver_statuses: Vec<SolverStatusPin>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
struct SkipPin {
    function: String,
    reason: String,
    detail: String,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
struct UnknownPin {
    function: String,
    kind: String,
    reason: String,
    candidate_expression: bool,
    solver_candidate: bool,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
struct DiagnosticPin {
    function: String,
    kind: String,
    block: u32,
    inst_index: usize,
    message: String,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
struct SolverStatusPin {
    function: String,
    kind: String,
    status: String,
    detail: String,
}

#[test]
fn fsym_real_function_corpus_matches_fixture_manifest() {
    let manifest: Manifest = serde_json::from_str(MANIFEST).expect("manifest should parse");
    assert_eq!(manifest.issue, 862);
    assert_eq!(manifest.parent_issue, 377);
    assert!(
        manifest
            .description
            .contains("real/imported-function corpus gate")
    );
    assert_eq!(
        manifest.generated_with.import_api,
        "trust_cg_llvm_import::import_text"
    );
    assert_eq!(
        manifest.generated_with.fixture_format,
        "serde_json::to_string_pretty::<trust_ir::Module>"
    );
    assert!(looks_like_git_sha(&manifest.generated_with.source_commit));
    assert!(manifest.acceptance.safe_corpus);

    let mut actual_totals = CorpusTotals::default();
    let mut families = BTreeSet::new();
    let fixture_root = fixture_root();

    for fixture in &manifest.fixtures {
        assert_manifest_fixture_hygiene(fixture);
        families.insert(fixture.source_family.as_str());

        let module = load_fixture_module(&fixture_root, &fixture.file);
        assert_eq!(module.name, fixture.module, "fixture {}", fixture.file);

        let module_function_names = module
            .functions
            .iter()
            .map(|function| function.name.clone())
            .collect::<Vec<_>>();
        assert_eq!(
            module_function_names, fixture.module_function_names,
            "module function list drifted for {}",
            fixture.file
        );
        assert_eq!(module.functions.len(), fixture.module_functions);

        let imported_functions = module
            .functions
            .iter()
            .filter(|function| !function.blocks.is_empty())
            .map(|function| function.name.clone())
            .collect::<Vec<_>>();
        assert_eq!(
            imported_functions, fixture.imported_functions,
            "imported function list drifted for {}",
            fixture.file
        );

        let summary = FsymSummary::scan_trust_ir_module(&module);
        let counters = summary.counters();
        let fp_bps = false_positive_basis_points(counters.scanned, counters.concrete_ub);

        println!(
            "fsym real fixture={} imported_functions={} module_functions={} scanned={} skipped={} unknown={} concrete_ub={} fp_bps={}",
            fixture.file,
            imported_functions.len(),
            module.functions.len(),
            counters.scanned,
            counters.skipped,
            counters.unknown,
            counters.concrete_ub,
            fp_bps
        );

        assert_eq!(counters.scanned, fixture.scanned, "{}", fixture.file);
        assert_eq!(counters.skipped, fixture.skipped, "{}", fixture.file);
        assert_eq!(counters.unknown, fixture.unknown, "{}", fixture.file);
        assert_eq!(
            counters.concrete_ub,
            fixture.concrete_ub,
            "fixture {} concrete UB details:\n{}",
            fixture.file,
            concrete_ub_details(&summary)
        );
        assert_eq!(
            fp_bps, fixture.false_positive_basis_points,
            "{}",
            fixture.file
        );

        assert_eq!(
            sorted(actual_skips(&summary)),
            sorted(fixture.skips.clone()),
            "skip pins drifted for {}",
            fixture.file
        );
        assert_eq!(
            sorted(actual_unknowns(&summary)),
            sorted(fixture.unknowns.clone()),
            "unknown pins drifted for {}",
            fixture.file
        );
        assert_eq!(
            sorted(actual_diagnostics(&summary)),
            sorted(fixture.diagnostics.clone()),
            "diagnostic pins drifted for {}",
            fixture.file
        );
        assert_unknowns_have_solver_handoffs(&summary, &fixture.file);

        let solver_report =
            summary.escalate_unknown_obligations_locally(&FsymSolverEscalationConfig::enabled());
        assert!(
            solver_report.enabled,
            "solver disabled for {}",
            fixture.file
        );
        assert_eq!(
            solver_report.concrete_ub_count(),
            0,
            "solver found concrete UB in safe fixture {}",
            fixture.file
        );
        let solver_counts = SolverCounts {
            results: solver_report.results.len(),
            proven_safe: solver_report.proven_safe_count(),
            concrete_ub: solver_report.concrete_ub_count(),
            remaining_unknown: solver_report.remaining_unknown_count(),
        };
        assert_eq!(
            solver_counts, fixture.solver,
            "solver accounting drifted for {}",
            fixture.file
        );
        assert_eq!(
            sorted(actual_solver_statuses(&solver_report)),
            sorted(fixture.solver_statuses.clone()),
            "solver status pins drifted for {}",
            fixture.file
        );

        actual_totals.imported_functions += imported_functions.len();
        actual_totals.module_functions += module.functions.len();
        actual_totals.scanned += counters.scanned;
        actual_totals.skipped += counters.skipped;
        actual_totals.unknown += counters.unknown;
        actual_totals.concrete_ub += counters.concrete_ub;
        actual_totals.solver.results += solver_counts.results;
        actual_totals.solver.proven_safe += solver_counts.proven_safe;
        actual_totals.solver.concrete_ub += solver_counts.concrete_ub;
        actual_totals.solver.remaining_unknown += solver_counts.remaining_unknown;
    }

    actual_totals.false_positive_basis_points =
        false_positive_basis_points(actual_totals.scanned, actual_totals.concrete_ub);

    println!(
        "fsym real corpus: imported_functions={} module_functions={} scanned={} skipped={} unknown={} concrete_ub={} fp_bps={} solver_results={} solver_concrete_ub={}",
        actual_totals.imported_functions,
        actual_totals.module_functions,
        actual_totals.scanned,
        actual_totals.skipped,
        actual_totals.unknown,
        actual_totals.concrete_ub,
        actual_totals.false_positive_basis_points,
        actual_totals.solver.results,
        actual_totals.solver.concrete_ub
    );

    assert_source_families_cover_scout_list(&families);
    assert_eq!(actual_totals, manifest.totals);
    assert!(
        actual_totals.imported_functions >= manifest.acceptance.min_imported_functions,
        "imported real function count below acceptance floor"
    );
    assert!(
        actual_totals.scanned >= manifest.acceptance.min_scanned,
        "scanned function count below acceptance floor"
    );
    assert_eq!(actual_totals.concrete_ub, 0);
    assert!(
        actual_totals.false_positive_basis_points
            <= manifest.acceptance.max_false_positive_basis_points,
        "false-positive basis points above acceptance threshold"
    );
    assert_eq!(
        actual_totals.solver.concrete_ub, 0,
        "local solver must not find concrete UB in safe fixtures"
    );
}

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_DIR)
}

fn load_fixture_module(root: &Path, file: &str) -> Module {
    let path = root.join(file);
    let json = fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("read fixture {}: {error}", path.display()));
    serde_json::from_str(&json)
        .unwrap_or_else(|error| panic!("parse fixture {}: {error}", path.display()))
}

fn assert_manifest_fixture_hygiene(fixture: &FixtureManifest) {
    assert!(
        fixture.file.ends_with(".trust_ir.json"),
        "fixture has non-trust_ir extension: {}",
        fixture.file
    );
    assert!(!fixture.source_family.is_empty());
    assert!(
        !fixture.provenance.is_empty(),
        "missing provenance for {}",
        fixture.file
    );
    for provenance in &fixture.provenance {
        assert!(
            provenance.contains(".rs::"),
            "weak provenance `{provenance}` for {}",
            fixture.file
        );
    }
    assert!(
        !fixture.imported_functions.is_empty(),
        "fixture {} has no real imported functions",
        fixture.file
    );
}

fn assert_source_families_cover_scout_list(families: &BTreeSet<&str>) {
    for required in [
        "divtest",
        "switch dispatch",
        "switch narrow widths",
        "cast tests",
        "printf globals",
        "nottest",
        "fp core/binops",
        "objectsize intrinsic",
        "bitreverse intrinsic",
    ] {
        assert!(
            families.contains(required),
            "missing source family {required}"
        );
    }
}

fn actual_skips(summary: &FsymSummary) -> Vec<SkipPin> {
    summary
        .functions
        .iter()
        .filter_map(|function| function.skip.as_ref())
        .map(|skip| SkipPin {
            function: skip.function.clone(),
            reason: skip_reason_tag(skip.reason).to_string(),
            detail: skip.detail.clone(),
        })
        .collect()
}

fn actual_unknowns(summary: &FsymSummary) -> Vec<UnknownPin> {
    summary
        .functions
        .iter()
        .flat_map(|function| function.unknown_obligations.iter())
        .map(|unknown| UnknownPin {
            function: unknown.function.clone(),
            kind: kind_tag(unknown.kind).to_string(),
            reason: unknown.reason.clone(),
            candidate_expression: unknown.candidate_expression.is_some(),
            solver_candidate: unknown.solver_candidate.is_some(),
        })
        .collect()
}

fn actual_diagnostics(summary: &FsymSummary) -> Vec<DiagnosticPin> {
    summary
        .functions
        .iter()
        .flat_map(|function| function.diagnostics.iter())
        .map(|diagnostic| DiagnosticPin {
            function: diagnostic.function.clone(),
            kind: kind_tag(diagnostic.kind).to_string(),
            block: diagnostic.block,
            inst_index: diagnostic.inst_index,
            message: diagnostic.message.clone(),
        })
        .collect()
}

fn actual_solver_statuses(
    solver_report: &trust_cg_verify::fsym_summary::FsymSolverEscalationReport,
) -> Vec<SolverStatusPin> {
    solver_report
        .results
        .iter()
        .map(|result| SolverStatusPin {
            function: result.function.clone(),
            kind: kind_tag(result.kind).to_string(),
            status: result.status.as_str().to_string(),
            detail: result.detail.clone(),
        })
        .collect()
}

fn assert_unknowns_have_solver_handoffs(summary: &FsymSummary, fixture: &str) {
    for unknown in summary
        .functions
        .iter()
        .flat_map(|function| function.unknown_obligations.iter())
    {
        assert!(
            unknown.candidate_expression.is_some(),
            "missing candidate expression for {} in {}",
            unknown.function,
            fixture
        );
        if matches!(
            unknown.kind,
            FsymTrustIrDiagnosticKind::NullDeref
                | FsymTrustIrDiagnosticKind::Arithmetic
                | FsymTrustIrDiagnosticKind::OutOfBounds
        ) {
            assert!(
                unknown.solver_candidate.is_some(),
                "missing typed solver candidate for {} in {}",
                unknown.function,
                fixture
            );
        }
    }
}

fn concrete_ub_details(summary: &FsymSummary) -> String {
    summary
        .functions
        .iter()
        .flat_map(|function| function.diagnostics.iter())
        .map(|diagnostic| {
            format!(
                "kind={:?} function={} bb{} inst{} message={}",
                diagnostic.kind,
                diagnostic.function,
                diagnostic.block,
                diagnostic.inst_index,
                diagnostic.message
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn false_positive_basis_points(scanned: usize, concrete_ub: usize) -> usize {
    if scanned == 0 {
        return 10_000;
    }
    concrete_ub * 10_000 / scanned
}

fn sorted<T: Ord>(mut values: Vec<T>) -> Vec<T> {
    values.sort();
    values
}

fn looks_like_git_sha(value: &str) -> bool {
    value.len() == 40 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn skip_reason_tag(reason: FsymTrustIrSkipReason) -> &'static str {
    match reason {
        FsymTrustIrSkipReason::Loop => "loop",
        FsymTrustIrSkipReason::Switch => "switch",
        FsymTrustIrSkipReason::TooLarge => "too-large",
        FsymTrustIrSkipReason::MalformedCfg => "malformed-cfg",
        FsymTrustIrSkipReason::UnsupportedTerminator => "unsupported-terminator",
        FsymTrustIrSkipReason::UnsupportedInstruction => "unsupported-instruction",
    }
}

fn kind_tag(kind: FsymTrustIrDiagnosticKind) -> &'static str {
    match kind {
        FsymTrustIrDiagnosticKind::NullDeref => "null-deref",
        FsymTrustIrDiagnosticKind::Arithmetic => "arithmetic",
        FsymTrustIrDiagnosticKind::OutOfBounds => "bounds",
        FsymTrustIrDiagnosticKind::UseAfterFree => "use-after-free",
    }
}
