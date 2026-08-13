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
const BACKEND_TOOLCHAIN: &str = "nightly-2026-04-20";
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
    source_guards: Vec<ProbeRow>,
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
    let source_guards_passed = inventory
        .source_guards
        .iter()
        .all(|probe| !probe.required || probe.present);
    let inventory_present = inventory.summary.total > 0;
    let probe_exit = if required_tools_present && source_guards_passed && inventory_present {
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
            command: format!(
                "rustup run {BACKEND_TOOLCHAIN} cargo build --manifest-path {BACKEND_CRATE}/Cargo.toml"
            ),
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

    let build_cmd = format!(
        "rustup run {BACKEND_TOOLCHAIN} cargo build --manifest-path {BACKEND_CRATE}/Cargo.toml"
    );
    if which("rustup").is_none() {
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
                stderr_tail: "rustup missing; cannot enter pinned rustc backend toolchain"
                    .to_string(),
            }],
            note: format!("rustc {mode} requires rustup to enter the pinned backend toolchain"),
        });
    }

    let build = Spawn::new("rustup")
        .args([
            "run",
            BACKEND_TOOLCHAIN,
            "cargo",
            "build",
            "--manifest-path",
        ])
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
        let compile = Spawn::new("rustup")
            .args(["run", BACKEND_TOOLCHAIN, "rustc", "--edition=2021"])
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
            "rustc {mode} invokes rustc_codegen_trust_cg through rustc -Zcodegen-backend on {} fixture(s)",
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

fn rustc_fixture_command(backend_artifact: &Path, src: &Path, bin: &Path) -> String {
    format!(
        "rustup run {BACKEND_TOOLCHAIN} rustc --edition=2021 -Zcodegen-backend={} {} -o {}",
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
    ["cargo", "rustc"]
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
    ["cargo", "rustc"]
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
                note: format!("dry-run: would query rustup target list for {target}"),
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
                } else if which("rustup").is_some() {
                    format!("optional local-dev target missing; run: rustup target add {target}")
                } else {
                    "rustup missing; target availability not checked".to_string()
                },
            }
        })
        .collect()
}

fn installed_targets() -> Vec<String> {
    if which("rustup").is_none() {
        return Vec::new();
    }
    let Ok(captured) = Spawn::new("rustup")
        .arg("target")
        .arg("list")
        .arg("--installed")
        .capture()
    else {
        return Vec::new();
    };
    if !captured.success() {
        return Vec::new();
    }
    captured
        .stdout
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_string)
        .collect()
}

fn inventory_report(repo: &RepoRoot) -> anyhow::Result<InventoryReport> {
    let doc_path = repo.join(INVENTORY_DOC);
    let source_path = repo.join(BACKEND_SOURCE);
    let doc = std::fs::read_to_string(&doc_path)
        .with_context(|| format!("reading {}", doc_path.display()))?;
    let source = std::fs::read_to_string(&source_path)
        .with_context(|| format!("reading {}", source_path.display()))?;
    let rows = parse_inventory_rows(&doc);
    let summary = summarize_inventory(&rows);
    let source_guards = source_guards(&source);

    Ok(InventoryReport {
        doc: INVENTORY_DOC.to_string(),
        source: BACKEND_SOURCE.to_string(),
        rows,
        summary,
        source_guards,
    })
}

fn parse_inventory_rows(doc: &str) -> Vec<InventoryRow> {
    let mut family = String::new();
    let mut rows = Vec::new();
    for line in doc.lines() {
        if let Some(header) = line.strip_prefix("## ") {
            family = header.trim().to_string();
            continue;
        }
        let trimmed = line.trim();
        if !trimmed.starts_with('|')
            || trimmed.starts_with("| ---")
            || trimmed.starts_with("| Variant")
            || trimmed.starts_with("| Fact")
        {
            continue;
        }
        let cells: Vec<String> = trimmed
            .trim_matches('|')
            .split('|')
            .map(|cell| cell.trim().trim_matches('`').to_string())
            .collect();
        if cells.len() != 4 {
            continue;
        }
        let state = cells[1].clone();
        if !matches!(state.as_str(), "supported" | "partial" | "fail-closed") {
            continue;
        }
        rows.push(InventoryRow {
            family: family.clone(),
            variant: cells[0].clone(),
            state,
            diagnostic_root: cells[2].clone(),
            notes: cells[3].clone(),
        });
    }
    rows
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

fn static_const_identity_guard_present(source: &str) -> bool {
    let Some(emit_const_alloc_global) = source
        .split("fn emit_const_alloc_global(")
        .nth(1)
        .and_then(|tail| tail.split("\nfn emit_thread_local_global(").next())
    else {
        return false;
    };
    let Some(static_arm) = emit_const_alloc_global
        .split("GlobalAlloc::Static(def_id) => {")
        .nth(1)
        .and_then(|tail| tail.split("GlobalAlloc::VTable(..)").next())
    else {
        return false;
    };
    let Some(mutable_arm) = static_arm
        .split("if global_alloc.mutability")
        .nth(1)
        .and_then(|tail| tail.split("\n            let evaluated =").next())
    else {
        return false;
    };
    let Some(local_immutable_arm) = static_arm
        .split("if def_id.is_local() {")
        .nth(1)
        .and_then(|tail| tail.split("\n                return Ok(canonical);").next())
    else {
        return false;
    };

    // A TLS address cannot be represented by the ordinary const-allocation
    // global path, so that path must reject it explicitly. Mutable and local
    // immutable statics, on the other hand, are admitted only by importing the
    // definition's canonical external symbol: no per-reader initializer may be
    // minted, and mutability must match the definition.
    static_arm.contains("if ctx.tcx.is_thread_local_static(def_id)")
        && static_arm.contains("const reference to thread-local static")
        && mutable_arm.contains("== rustc_hir::Mutability::Mut")
        && mutable_arm.contains("symbol_name(Instance::mono(ctx.tcx, def_id))")
        && mutable_arm.contains("mutable: true")
        && mutable_arm.contains("initializer: None")
        && mutable_arm.contains("linkage: Linkage::External")
        && mutable_arm.contains("return Ok(canonical);")
        && local_immutable_arm.contains("symbol_name(Instance::mono(ctx.tcx, def_id))")
        && local_immutable_arm.contains("mutable: false")
        && local_immutable_arm.contains("initializer: None")
        && local_immutable_arm.contains("linkage: Linkage::External")
}

fn source_guards(source: &str) -> Vec<ProbeRow> {
    [
        (
            "intrinsic-fail-closed",
            // `StatementKind::Intrinsic` is not in the handled arm of
            // `lower_statement`; it reaches the catch-all that returns
            // `Err(format!("StatementKind::{}", statement_kind_name(other)))`,
            // and `statement_kind_name` names it "Intrinsic". Together these
            // prove an unsupported intrinsic statement still fails closed (a
            // lowering `Err`, never a silent miscompile).
            source.contains(r#"StatementKind::Intrinsic(_) => "Intrinsic""#)
                && source.contains(
                    r#"other => Err(format!("StatementKind::{}", statement_kind_name(other)))"#,
                ),
            "StatementKind::Intrinsic must reach the lower_statement catch-all and fail closed",
        ),
        (
            "static-const-identity-safe",
            static_const_identity_guard_present(source),
            "const static references must preserve canonical mutable/local identity and reject TLS through the ordinary const-allocation path",
        ),
        (
            "asm-and-vtable-fail-closed",
            // Inline assembly reaches the terminator catch-all (named via
            // `terminator_kind_name`) and fails closed; vtable / type-id global
            // allocations have dedicated lowering and must not be materialized
            // as raw bytes here, so that arm fails closed too.
            source.contains(r#"TerminatorKind::InlineAsm { .. } => "InlineAsm""#)
                && source.contains("GlobalAlloc::VTable(..) | GlobalAlloc::TypeId { .. } =>")
                && source.contains("is a vtable / type-id global, which has a"),
            "inline-asm terminators and vtable/type-id globals must fail closed",
        ),
    ]
    .into_iter()
    .map(|(name, present, note)| ProbeRow {
        name: name.to_string(),
        required: true,
        present,
        version: String::new(),
        path: Some(BACKEND_SOURCE.to_string()),
        note: note.to_string(),
    })
    .collect()
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
        let rows = parse_inventory_rows(doc);
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0].family, "StatementKind");
        assert_eq!(rows[0].variant, "Intrinsic");
        assert_eq!(rows[1].family, "RustcAbiLayout");
        assert_eq!(rows[1].variant, "DirectScalar");
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
