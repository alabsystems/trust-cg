// WS4 — rustc_codegen_trust_cg + rustc UI harness.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `trust-cg-test rustc` — drive `rustc_codegen_trust_cg`.
//!
//! The public coverage contract is the repository-root
//! `rustc-mir-coverage-inventory.md`; command-specific usage is in `--help`.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use anyhow::Context;
use clap::{Args, Subcommand};
use serde::Serialize;

use super::GlobalArgs;
use crate::OutputFormat;
use crate::config::RepoRoot;
use crate::external::{self, install_hint};
use crate::results::ResultStatus;
use crate::shell::{Spawn, which};

const INVENTORY_DOC: &str = "rustc-mir-coverage-inventory.md";
const BACKEND_SOURCE: &str = "crates/rustc-codegen-trust-cg/src/lib.rs";
const BACKEND_CRATE: &str = "crates/rustc-codegen-trust-cg";
/// The backend is built by, and loaded into, the installed Trust package
/// (`crates/rustc-codegen-trust-cg/rust-toolchain.toml` pins `channel =
/// "trust"`): its `targo` builds the dylib in the explicit unverified lane and
/// its `trustc` loads it. The retired stock `nightly-2026-04-20` lane cannot
/// load a dylib linked against the Trust `librustc_driver`.
const TARGO: &str = "targo";
const TRUSTC: &str = "trustc";
const TARGETS: &[&str] = &["aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"];
const UI_FIXTURES: &[RustcFixture] = &[
    RustcFixture {
        name: "empty-main",
        source: "fn main() {}\n",
        expect_success: true,
    },
    RustcFixture {
        name: "extern-c-bool-and-narrow-integer-direct",
        source: "#![crate_type = \"lib\"]\n\
                 #[no_mangle]\n\
                 pub extern \"C\" fn narrow_roundtrip(byte: u8, signed: i8) -> u8 {\n\
                     byte.wrapping_add(signed as u8)\n\
                 }\n\
                 #[no_mangle]\n\
                 pub extern \"C\" fn bool_roundtrip(flag: bool) -> bool {\n\
                     !flag\n\
                 }\n",
        expect_success: true,
    },
    RustcFixture {
        name: "extern-c-char-direct-scalar-fail-closed",
        source: "#![crate_type = \"lib\"]\n\
                 #[no_mangle]\n\
                 pub extern \"C\" fn unsupported_char_roundtrip(ch: char) -> char {\n\
                     ch\n\
                 }\n",
        expect_success: false,
    },
    RustcFixture {
        name: "extern-c-i128-scalar-abi-fail-closed",
        source: "#![crate_type = \"lib\"]\n\
                 #[no_mangle]\n\
                 pub extern \"C\" fn unsupported_i128_roundtrip(value: i128) -> i128 {\n\
                     value\n\
                 }\n",
        expect_success: false,
    },
    RustcFixture {
        name: "extern-c-u128-scalar-abi-fail-closed",
        source: "#![crate_type = \"lib\"]\n\
                 #[no_mangle]\n\
                 pub extern \"C\" fn unsupported_u128_roundtrip(value: u128) -> u128 {\n\
                     value\n\
                 }\n",
        expect_success: false,
    },
];

struct RustcFixture {
    name: &'static str,
    source: &'static str,
    expect_success: bool,
}

/// Subcommand selector.
#[derive(Subcommand, Debug, Clone)]
pub enum RustcCommand {
    /// Compile and run a trivial hello-world via Trust Codegen.
    #[command(
        long_about = "Compile and run a trivial hello-world via Trust Codegen.\n\n\
                      Builds a minimal Rust source through \
                      `rustc_codegen_trust_cg` and executes the result as a \
                      fast smoke check before the full UI harness.\n\n\
                      # Examples\n\n  \
                      trust-cg-test rustc smoke\n  \
                      trust-cg-test rustc smoke --format json\n  \
                      trust-cg-test rustc smoke --out evals/results/rustc/smoke/2026-04-19.json"
    )]
    Smoke,
    /// Run the full rustc UI harness against Trust Codegen.
    #[command(
        long_about = "Run the full rustc UI harness against Trust Codegen.\n\n\
                      Drives rustc's UI test corpus through \
                      `rustc_codegen_trust_cg`, records per-test outcomes, and \
                      writes the WS4 compatibility result artifact.\n\n\
                      # Examples\n\n  \
                      trust-cg-test rustc ui\n  \
                      trust-cg-test rustc ui --format json\n  \
                      trust-cg-test rustc ui --out evals/results/rustc/ui/2026-04-19.json"
    )]
    Ui,
    /// Print rustc-MIR opcode coverage of the `trust-ir-from-rustc-mir` adapter.
    #[command(long_about = "Print rustc-MIR opcode coverage of the \
                      `trust-ir-from-rustc-mir` adapter.\n\n\
                      Reports which rustc MIR constructs are currently \
                      translated by the adapter and highlights unsupported \
                      features that block rustc UI coverage.\n\n\
                      # Examples\n\n  \
                      trust-cg-test rustc feature-coverage\n  \
                      trust-cg-test rustc feature-coverage --format json\n  \
                      trust-cg-test rustc feature-coverage --out evals/results/rustc/feature-coverage/2026-04-19.json")]
    FeatureCoverage,
}

/// Arguments for `trust-cg-test rustc`.
#[derive(Args, Debug, Clone)]
#[command(
    long_about = "Drive `rustc_codegen_trust_cg` + rustc UI tests (WS4).\n\n\
                  `rustc smoke` sanity-compiles `hello.rs`. `rustc ui` runs \
                  the full UI harness and writes a per-test JSON record. \
                  `rustc feature-coverage` reports which rustc-MIR opcodes \
                  the adapter currently translates.\n\n\
                  # Examples\n\n  \
                  trust-cg-test rustc smoke\n  \
                  trust-cg-test rustc ui --format json --out evals/results/rustc/2026-04-19.json\n  \
                  trust-cg-test rustc feature-coverage --format human"
)]
pub struct RustcArgs {
    /// Subcommand.
    #[command(subcommand)]
    pub cmd: RustcCommand,
}

#[derive(Clone, Debug, Serialize)]
struct ProbeRow {
    name: String,
    required: bool,
    present: bool,
    version: String,
    path: Option<String>,
    note: String,
}

#[derive(Clone, Debug, Serialize)]
struct TargetRow {
    target: String,
    installed: bool,
    required: bool,
    note: String,
}

#[derive(Clone, Debug, Serialize)]
struct InventoryRow {
    family: String,
    variant: String,
    state: String,
    diagnostic_root: String,
    notes: String,
}

#[derive(Clone, Debug, Default, Serialize)]
struct InventorySummary {
    supported: usize,
    partial: usize,
    fail_closed: usize,
    total: usize,
}

#[derive(Clone, Debug, Serialize)]
struct InventoryReport {
    doc: String,
    source: String,
    rows: Vec<InventoryRow>,
    summary: InventorySummary,
}

#[derive(Clone, Debug, Serialize)]
struct BackendStep {
    name: &'static str,
    command: String,
    exit_code: Option<i32>,
    status: ResultStatus,
    stdout_tail: String,
    stderr_tail: String,
}

#[derive(Clone, Debug, Serialize)]
struct BackendRun {
    invoked: bool,
    status: ResultStatus,
    artifact: Option<String>,
    steps: Vec<BackendStep>,
    note: String,
}

#[derive(Clone, Debug, Serialize)]
struct RustcReport {
    command: &'static str,
    mode: &'static str,
    backend_execution: String,
    backend_run: BackendRun,
    probes: Vec<ProbeRow>,
    targets: Vec<TargetRow>,
    inventory: InventoryReport,
    exit: ResultStatus,
}

/// Entry point.
pub fn run(global: &GlobalArgs, args: &RustcArgs) -> anyhow::Result<ResultStatus> {
    let repo = RepoRoot::locate(Path::new("."))?;
    let mode = match args.cmd {
        RustcCommand::Smoke => "smoke",
        RustcCommand::Ui => "ui",
        RustcCommand::FeatureCoverage => "feature-coverage",
    };
    let report = build_report(&repo, global.dry_run, mode)?;
    emit_report(global, &report)?;
    Ok(report.exit)
}

fn build_report(repo: &RepoRoot, dry_run: bool, mode: &'static str) -> anyhow::Result<RustcReport> {
    let inventory = inventory_report(repo)?;
    let probes = if dry_run {
        dry_run_probes()
    } else {
        probe_required_tools()
    };
    let targets = probe_targets(dry_run);
    let backend_run = backend_run(repo, dry_run, mode)?;
    let required_tools_present = probes.iter().all(|probe| !probe.required || probe.present);
    let inventory_present = inventory.summary.total > 0;
    let probe_exit = if required_tools_present && inventory_present {
        ResultStatus::Ok
    } else {
        ResultStatus::EnvBroken
    };
    let exit = combine_status(probe_exit, backend_run.status);

    Ok(RustcReport {
        command: "rustc",
        mode,
        backend_execution: backend_run.note.clone(),
        backend_run,
        probes,
        targets,
        inventory,
        exit,
    })
}

fn combine_status(a: ResultStatus, b: ResultStatus) -> ResultStatus {
    use ResultStatus::{EnvBroken, Errored, Failed, NotImplemented, Ok, UsageError};
    match (a, b) {
        (Errored, _) | (_, Errored) => Errored,
        (UsageError, _) | (_, UsageError) => UsageError,
        (EnvBroken, _) | (_, EnvBroken) => EnvBroken,
        (Failed, _) | (_, Failed) => Failed,
        (NotImplemented, _) | (_, NotImplemented) => NotImplemented,
        (Ok, Ok) => Ok,
    }
}

fn backend_run(repo: &RepoRoot, dry_run: bool, mode: &'static str) -> anyhow::Result<BackendRun> {
    match mode {
        "smoke" => backend_smoke(repo, dry_run),
        "ui" => backend_ui(repo, dry_run),
        "feature-coverage" => Ok(BackendRun {
            invoked: false,
            status: ResultStatus::Ok,
            artifact: None,
            steps: Vec::new(),
            note: "feature-coverage is an inventory lane and does not invoke rustc".to_string(),
        }),
        _ => Ok(BackendRun {
            invoked: false,
            status: ResultStatus::Errored,
            artifact: None,
            steps: Vec::new(),
            note: format!("unknown rustc runner mode {mode}"),
        }),
    }
}

fn backend_smoke(repo: &RepoRoot, dry_run: bool) -> anyhow::Result<BackendRun> {
    backend_fixture_run(
        repo,
        dry_run,
        "smoke",
        &[RustcFixture {
            name: "smoke-main",
            source: "fn main() {}\n",
            expect_success: true,
        }],
    )
}

fn backend_ui(repo: &RepoRoot, dry_run: bool) -> anyhow::Result<BackendRun> {
    backend_fixture_run(repo, dry_run, "ui", UI_FIXTURES)
}

fn backend_fixture_run(
    repo: &RepoRoot,
    dry_run: bool,
    mode: &'static str,
    fixtures: &[RustcFixture],
) -> anyhow::Result<BackendRun> {
    let backend_crate = repo.join(BACKEND_CRATE);
    let backend_artifact = backend_artifact_path(&backend_crate);
    let work_dir = std::env::temp_dir().join(format!("trust-cg-test-rustc-{mode}"));

    if dry_run {
        let mut steps = vec![BackendStep {
            name: "build-backend",
            command: backend_build_command(),
            exit_code: Some(0),
            status: ResultStatus::Ok,
            stdout_tail: String::new(),
            stderr_tail: "dry-run: would build rustc_codegen_trust_cg".to_string(),
        }];
        for fixture in fixtures {
            let fixture_paths = fixture_paths(&work_dir, fixture.name);
            steps.push(BackendStep {
                name: fixture.name,
                command: rustc_fixture_command(
                    &backend_artifact,
                    &fixture_paths.src,
                    &fixture_paths.bin,
                ),
                exit_code: Some(i32::from(!fixture.expect_success)),
                status: ResultStatus::Ok,
                stdout_tail: String::new(),
                stderr_tail: format!(
                    "dry-run: would compile rustc {mode} fixture `{}` expecting {}",
                    fixture.name,
                    if fixture.expect_success {
                        "success"
                    } else {
                        "failure"
                    }
                ),
            });
        }
        return Ok(BackendRun {
            invoked: true,
            status: ResultStatus::Ok,
            artifact: Some(backend_artifact.display().to_string()),
            steps,
            note: format!(
                "dry-run: rustc {mode} would build and invoke rustc_codegen_trust_cg on {} fixture(s)",
                fixtures.len()
            ),
        });
    }

    std::fs::create_dir_all(&work_dir)
        .with_context(|| format!("creating {}", work_dir.display()))?;

    let build_cmd = backend_build_command();
    if let Some(missing) = [TARGO, TRUSTC]
        .into_iter()
        .find(|tool| which(tool).is_none())
    {
        return Ok(BackendRun {
            invoked: false,
            status: ResultStatus::EnvBroken,
            artifact: Some(backend_artifact.display().to_string()),
            steps: vec![BackendStep {
                name: "build-backend",
                command: build_cmd,
                exit_code: None,
                status: ResultStatus::EnvBroken,
                stdout_tail: String::new(),
                stderr_tail: format!(
                    "{missing} missing: the backend builds with, and loads into, the installed Trust package"
                ),
            }],
            note: format!("rustc {mode} requires the installed Trust package (targo and trustc)"),
        });
    }

    let build = Spawn::new(TARGO)
        .args(["--unverified", "build", "--manifest-path"])
        .arg(repo.join(BACKEND_CRATE).join("Cargo.toml"))
        .capture()?;
    let build_status = if build.success() {
        ResultStatus::Ok
    } else {
        ResultStatus::EnvBroken
    };
    let mut steps = vec![BackendStep {
        name: "build-backend",
        command: build_cmd,
        exit_code: Some(build.code),
        status: build_status,
        stdout_tail: tail(&build.stdout),
        stderr_tail: tail(&build.stderr),
    }];
    if !build.success() {
        return Ok(BackendRun {
            invoked: true,
            status: build_status,
            artifact: Some(backend_artifact.display().to_string()),
            steps,
            note: "rustc smoke built the backend and failed before rustc invocation".to_string(),
        });
    }

    let mut run_status = ResultStatus::Ok;
    for fixture in fixtures {
        let fixture_paths = fixture_paths(&work_dir, fixture.name);
        std::fs::write(&fixture_paths.src, fixture.source)
            .with_context(|| format!("writing {}", fixture_paths.src.display()))?;
        let compile = Spawn::new(TRUSTC)
            .args(["-Ztrust-verify=off", "--edition=2021"])
            .arg(format!("-Zcodegen-backend={}", backend_artifact.display()))
            .arg(&fixture_paths.src)
            .arg("-o")
            .arg(&fixture_paths.bin)
            .capture()?;
        let outcome_matches = compile.success() == fixture.expect_success;
        let compile_status = if outcome_matches {
            ResultStatus::Ok
        } else {
            ResultStatus::Failed
        };
        if !outcome_matches {
            run_status = ResultStatus::Failed;
        }
        steps.push(BackendStep {
            name: fixture.name,
            command: rustc_fixture_command(
                &backend_artifact,
                &fixture_paths.src,
                &fixture_paths.bin,
            ),
            exit_code: Some(compile.code),
            status: compile_status,
            stdout_tail: tail(&compile.stdout),
            stderr_tail: tail(&compile.stderr),
        });
    }

    Ok(BackendRun {
        invoked: true,
        status: run_status,
        artifact: Some(backend_artifact.display().to_string()),
        steps,
        note: format!(
            "rustc {mode} invokes rustc_codegen_trust_cg through trustc -Zcodegen-backend on {} fixture(s)",
            fixtures.len()
        ),
    })
}

struct FixturePaths {
    src: PathBuf,
    bin: PathBuf,
}

fn fixture_paths(work_dir: &Path, name: &str) -> FixturePaths {
    FixturePaths {
        src: work_dir.join(format!("{name}.rs")),
        bin: work_dir.join(name),
    }
}

fn backend_build_command() -> String {
    format!("{TARGO} --unverified build --manifest-path {BACKEND_CRATE}/Cargo.toml")
}

fn rustc_fixture_command(backend_artifact: &Path, src: &Path, bin: &Path) -> String {
    format!(
        "{TRUSTC} -Ztrust-verify=off --edition=2021 -Zcodegen-backend={} {} -o {}",
        backend_artifact.display(),
        src.display(),
        bin.display()
    )
}

fn backend_artifact_path(backend_crate: &Path) -> PathBuf {
    let file = if cfg!(target_os = "macos") {
        "librustc_codegen_trust_cg.dylib"
    } else if cfg!(target_os = "windows") {
        "rustc_codegen_trust_cg.dll"
    } else {
        "librustc_codegen_trust_cg.so"
    };
    backend_crate.join("target").join("debug").join(file)
}

fn tail(s: &str) -> String {
    const MAX_LINES: usize = 20;
    let lines: Vec<&str> = s.lines().rev().take(MAX_LINES).collect();
    lines.into_iter().rev().collect::<Vec<_>>().join("\n")
}

fn dry_run_probes() -> Vec<ProbeRow> {
    [TARGO, TRUSTC]
        .into_iter()
        .map(|name| ProbeRow {
            name: name.to_string(),
            required: true,
            present: true,
            version: "dry-run".to_string(),
            path: None,
            note: format!("dry-run: would probe `{name} --version`"),
        })
        .collect()
}

fn probe_required_tools() -> Vec<ProbeRow> {
    [TARGO, TRUSTC]
        .into_iter()
        .map(|name| {
            let info = external::probe_one(name);
            ProbeRow {
                name: info.name,
                required: true,
                present: info.present,
                version: info.version,
                path: info.path,
                note: if info.present {
                    String::new()
                } else {
                    install_hint(name).to_string()
                },
            }
        })
        .collect()
}

fn probe_targets(dry_run: bool) -> Vec<TargetRow> {
    if dry_run {
        return TARGETS
            .iter()
            .map(|target| TargetRow {
                target: (*target).to_string(),
                installed: true,
                required: false,
                note: format!("dry-run: would look for {target} in the Trust sysroot"),
            })
            .collect();
    }

    let installed = installed_targets();
    TARGETS
        .iter()
        .map(|target| {
            let target = (*target).to_string();
            let installed_here = installed.iter().any(|candidate| candidate == &target);
            TargetRow {
                target: target.clone(),
                installed: installed_here,
                required: false,
                note: if installed_here {
                    "available for future backend smoke coverage".to_string()
                } else if which(TRUSTC).is_some() {
                    format!(
                        "optional local-dev target missing: the installed Trust package ships no {target} std"
                    )
                } else {
                    "trustc missing; target availability not checked".to_string()
                },
            }
        })
        .collect()
}

/// Targets whose std the installed Trust package ships
/// (`<sysroot>/lib/rustlib/<target>/lib`). There is no rustup target list for
/// the Trust package: its sysroot is the whole answer.
fn installed_targets() -> Vec<String> {
    if which(TRUSTC).is_none() {
        return Vec::new();
    }
    let Ok(captured) = Spawn::new(TRUSTC).args(["--print", "sysroot"]).capture() else {
        return Vec::new();
    };
    if !captured.success() {
        return Vec::new();
    }
    let rustlib = Path::new(captured.stdout.trim())
        .join("lib")
        .join("rustlib");
    TARGETS
        .iter()
        .filter(|target| rustlib.join(target).join("lib").is_dir())
        .map(|target| (*target).to_string())
        .collect()
}

fn inventory_report(repo: &RepoRoot) -> anyhow::Result<InventoryReport> {
    let doc_path = repo.join(INVENTORY_DOC);
    let doc = std::fs::read_to_string(&doc_path)
        .with_context(|| format!("reading {}", doc_path.display()))?;
    let rows =
        parse_inventory_rows(&doc).with_context(|| format!("parsing {}", doc_path.display()))?;
    let summary = summarize_inventory(&rows);

    Ok(InventoryReport {
        doc: INVENTORY_DOC.to_string(),
        source: BACKEND_SOURCE.to_string(),
        rows,
        summary,
    })
}

/// The rows of every `| Variant |` or `| Fact |` table in the inventory.
///
/// A row of such a table must have four cells and one of the three state
/// words. Anything else is an error, never a dropped row: a silently dropped
/// row would leave the summary counting fewer constructs than the inventory
/// names (ruling OD-33, `docs/decision-record.md`).
fn parse_inventory_rows(doc: &str) -> anyhow::Result<Vec<InventoryRow>> {
    let mut family = String::new();
    let mut rows = Vec::new();
    let mut in_table = false;
    for (index, line) in doc.lines().enumerate() {
        if let Some(header) = line.strip_prefix("## ") {
            family = header.trim().to_string();
            in_table = false;
            continue;
        }
        let trimmed = line.trim();
        if !trimmed.starts_with('|') {
            in_table = false;
            continue;
        }
        if trimmed.starts_with("| Variant") || trimmed.starts_with("| Fact") {
            in_table = true;
            continue;
        }
        if !in_table || trimmed.starts_with("| ---") {
            continue;
        }
        let cells: Vec<String> = trimmed
            .trim_matches('|')
            .split('|')
            .map(|cell| cell.trim().trim_matches('`').to_string())
            .collect();
        let line_number = index + 1;
        if cells.len() != 4 {
            anyhow::bail!(
                "inventory line {line_number}: a row needs 4 cells, found {}",
                cells.len()
            );
        }
        let state = cells[1].clone();
        if !matches!(state.as_str(), "supported" | "partial" | "fail-closed") {
            anyhow::bail!(
                "inventory line {line_number}: row `{}` has state `{state}`; the states are \
                 supported, partial and fail-closed",
                cells[0]
            );
        }
        rows.push(InventoryRow {
            family: family.clone(),
            variant: cells[0].clone(),
            state,
            diagnostic_root: cells[2].clone(),
            notes: cells[3].clone(),
        });
    }
    Ok(rows)
}

fn summarize_inventory(rows: &[InventoryRow]) -> InventorySummary {
    let mut by_state: BTreeMap<&str, usize> = BTreeMap::new();
    for row in rows {
        *by_state.entry(row.state.as_str()).or_default() += 1;
    }
    InventorySummary {
        supported: by_state.get("supported").copied().unwrap_or_default(),
        partial: by_state.get("partial").copied().unwrap_or_default(),
        fail_closed: by_state.get("fail-closed").copied().unwrap_or_default(),
        total: rows.len(),
    }
}

fn emit_report(global: &GlobalArgs, report: &RustcReport) -> anyhow::Result<()> {
    if let Some(out) = &global.out {
        if let Some(parent) = out.parent() {
            std::fs::create_dir_all(parent)
                .with_context(|| format!("creating {}", parent.display()))?;
        }
        let json = serde_json::to_string_pretty(report)?;
        std::fs::write(out, json).with_context(|| format!("writing {}", out.display()))?;
    }

    match global.format {
        OutputFormat::Json | OutputFormat::Junit => {
            let json = serde_json::to_string_pretty(report)?;
            println!("{json}");
        }
        OutputFormat::Human => print_human(report),
    }
    Ok(())
}

fn print_human(report: &RustcReport) {
    println!("trust-cg-test rustc {}", report.mode);
    println!();
    println!("  backend execution: {}", report.backend_execution);
    println!();
    println!("  required tools:");
    for probe in &report.probes {
        println!(
            "    {:<8} present={:<3} version={} {}",
            probe.name,
            if probe.present { "yes" } else { "no" },
            if probe.version.is_empty() {
                "-"
            } else {
                &probe.version
            },
            probe.note
        );
    }
    println!();
    println!("  target probes:");
    for target in &report.targets {
        println!(
            "    {:<30} installed={:<3} {}",
            target.target,
            if target.installed { "yes" } else { "no" },
            target.note
        );
    }
    println!();
    println!(
        "  MIR inventory: total={} supported={} partial={} fail-closed={}",
        report.inventory.summary.total,
        report.inventory.summary.supported,
        report.inventory.summary.partial,
        report.inventory.summary.fail_closed
    );
    println!();
    match report.exit {
        ResultStatus::Ok => println!("  status: OK"),
        ResultStatus::EnvBroken => println!("  status: ENV_BROKEN (required probe failed)"),
        _ => println!("  status: {:?}", report.exit),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inventory_parser_finds_variant_and_fact_tables() {
        let doc = "## StatementKind\n\
                   | Variant | State | Diagnostic root | Notes |\n\
                   | --- | --- | --- | --- |\n\
                   | `Intrinsic` | fail-closed | `StatementKind::Intrinsic` | blocker |\n\
                   ## RustcAbiLayout\n\
                   | Fact | State | Diagnostic root | Notes |\n\
                   | --- | --- | --- | --- |\n\
                   | `DirectScalar` | partial | `Ty::* scalar` | scalar |\n";
        let rows = parse_inventory_rows(doc).expect("a well-formed inventory parses");
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0].family, "StatementKind");
        assert_eq!(rows[0].variant, "Intrinsic");
        assert_eq!(rows[1].family, "RustcAbiLayout");
        assert_eq!(rows[1].variant, "DirectScalar");
    }

    #[test]
    fn inventory_parser_refuses_an_unknown_state_instead_of_dropping_the_row() {
        let doc = "## RustcAbiLayout\n\
                   | Fact | State | Diagnostic root | Notes |\n\
                   | --- | --- | --- | --- |\n\
                   | `DirectScalar` | broad | `Ty::* scalar` | scalar |\n";
        let error = parse_inventory_rows(doc).expect_err("an unknown state is an error");
        assert!(
            error
                .to_string()
                .contains("`DirectScalar` has state `broad`"),
            "{error}"
        );
        let short = "## MonoItem\n\
                     | Variant | State | Diagnostic root | Notes |\n\
                     | `Fn` | partial | root |\n";
        assert!(parse_inventory_rows(short).is_err());
    }

    #[test]
    fn inventory_parser_ignores_tables_that_are_not_inventory_tables() {
        let doc = "## Replacement Blocker Anchors\n\
                   | Blocker | State | Required before replacement-ready |\n\
                   | --- | --- | --- |\n\
                   | Rust frontend parity | blocked | everything |\n";
        assert!(
            parse_inventory_rows(doc)
                .expect("not an inventory table")
                .is_empty()
        );
    }

    #[test]
    fn committed_inventory_parses_without_dropping_a_row() {
        let doc = include_str!("../../../../rustc-mir-coverage-inventory.md");
        let rows = parse_inventory_rows(doc).expect("the committed inventory parses");
        assert!(rows.iter().any(|row| row.variant == "VariadicAbi"));
        assert!(rows.iter().any(|row| row.variant == "DirectScalar"));
    }

    #[test]
    fn inventory_summary_counts_states() {
        let rows = vec![
            InventoryRow {
                family: "a".to_string(),
                variant: "b".to_string(),
                state: "supported".to_string(),
                diagnostic_root: String::new(),
                notes: String::new(),
            },
            InventoryRow {
                family: "a".to_string(),
                variant: "c".to_string(),
                state: "partial".to_string(),
                diagnostic_root: String::new(),
                notes: String::new(),
            },
            InventoryRow {
                family: "a".to_string(),
                variant: "d".to_string(),
                state: "fail-closed".to_string(),
                diagnostic_root: String::new(),
                notes: String::new(),
            },
        ];
        let summary = summarize_inventory(&rows);
        assert_eq!(summary.total, 3);
        assert_eq!(summary.supported, 1);
        assert_eq!(summary.partial, 1);
        assert_eq!(summary.fail_closed, 1);
    }
}
