// trust-cg-cli/main.rs - Command-line driver for Trust Codegen
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Usage:
//   trust-cg input.tmbc -o output.o -O2 --target aarch64   (single binary file, object)
//   trust-cg a.tmbc b.tmbc c.tmbc -O2 -o prog              (multi-file, linked)
//   trust-cg -c a.tmbc b.tmbc                               (compile only, a.o b.o)
//   trust-cg -g -O2 -o prog a.tmbc                          (with debug info)
//   trust-cg --format=json module.json -o output.o          (debug-only JSON wire format)
//   trust-cg --format=text module.trust_ir -o output.o          (human-readable .trust_ir debug text)
//   trust-cg --format=auto module.tmbc                      (legacy auto-detect behaviour)
//   trust-cg --input-json module.json -o output.o           (DEPRECATED alias; use --format=json)
//   trust-cg --emit-trust_ir module.trust_ir input.tmbc             (dump parsed module as .trust_ir text)
//   trust-cg --version
//   trust-cg --help
//
// Input format rules (#414, trust_ir transport architecture Layer 4):
//   - Binary `.tmbc` is the default and only accepted format by default.
//   - JSON is retained ONLY as a debug flag: pass `--format=json` to
//     enable it. The legacy `--input-json <FILE>` flag still works but
//     is deprecated and emits a warning.
//   - Pass `--format=auto` to restore the pre-#414 extension + magic
//     sniffing behaviour (useful for mixed-format test trees).
//
// Text format (.trust_ir, #413):
//   - `--format=text` reads a human-readable `.trust_ir` file via
//     `trust_ir::parser::parse_module`.
//   - `--emit-trust_ir <PATH>` writes the parsed module back out as
//     `.trust_ir` text (via `trust_ir::Module`'s Display impl), useful for
//     round-trip debugging. Like `--emit-json`, requires a single
//     input file.

use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{self, Command};

use clap::{Parser, ValueEnum};
use rayon::prelude::*;
use trust_cg_codegen::jit_diagnostics::sha256_hex;

use trust_cg_codegen::compiler::{CompilationResult, Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::jit::ProfileHookMode;
use trust_cg_codegen::resource_limits;
use trust_cg_codegen::{CompileArtifactCacheConfig, CompileArtifactCacheTelemetry};

mod emit_proofs;
use trust_cg_codegen::pipeline::{self, FormatMode, OptLevel};
use trust_cg_codegen::target::{
    Target, TargetOperatingSystem, TargetSpec, TargetSpecParseErrorKind,
};
use trust_cg_verify::AYConfig;
use trust_cg_verify::fsym_summary::{
    FsymSolverEscalationConfig, FsymSolverEscalationResult, FsymSolverStatus, FsymSummary,
};
use trust_cg_verify::fsym_trust_ir::{
    FsymTrustIrDiagnosticKind, FsymTrustIrReport, FsymTrustIrSeverity, FsymTrustIrSkipReason,
    scan_module as scan_fsym_trust_ir,
};

/// Input format selector for the CLI `--format` flag.
///
/// See `designs/2026-04-16-trust_ir-transport-architecture.md` Layer 4 for
/// the binary/JSON story, and Layer 3 for the human-readable `.trust_ir`
/// text format added in #413.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
enum InputFormatArg {
    /// Binary trust_ir bitcode (.tmbc). The default.
    Binary,
    /// JSON wire format (debug-only, opt-in).
    Json,
    /// Human-readable `.trust_ir` text format (debug-only, opt-in; #413).
    Text,
    /// Legacy auto-detect by extension + magic bytes.
    Auto,
}

impl InputFormatArg {
    fn to_mode(self) -> FormatMode {
        match self {
            InputFormatArg::Binary => FormatMode::Tmbc,
            InputFormatArg::Json => FormatMode::Json,
            InputFormatArg::Text => FormatMode::Text,
            InputFormatArg::Auto => FormatMode::Auto,
        }
    }
}

/// Bounded fsym trust_ir preflight mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
enum FsymModeArg {
    /// Disable fsym preflight diagnostics.
    Off,
    /// Emit warnings for concrete UB found by the bounded fsym preflight.
    Warn,
    /// Reject compilation when the bounded fsym preflight finds concrete UB.
    Error,
}

/// Solver backend used to escalate bounded fsym unknown obligations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
enum FsymSolverArg {
    /// Do not invoke solver escalation for fsym unknown obligations.
    Off,
    /// Use the deterministic bounded local solver adapter.
    Local,
    /// Use the ay-backed solver adapter.
    AY,
}

/// Trust Codegen -- proof-oriented compiler backend for trust_ir.
///
/// Compiles trust_ir modules to native object files and can emit verification
/// evidence for supported lowering paths. Supports multi-file compilation and
/// system linker invocation.
#[derive(Parser, Debug)]
#[command(
    name = "trust-cg",
    version = env!("CARGO_PKG_VERSION"),
    about = "Trust Codegen: proof-oriented backend -- trust_ir to machine code",
    long_about = "Proof-oriented compiler backend for the t* stack.\n\n\
        Compiles trust_ir modules to native object files and records the\n\
        available evidence for supported lowering and optimization paths.\n\n\
        Targets: aarch64 (primary), x86-64 (x86_64 only; no 32-bit x86/i686), \
        riscv64 (scaffold).\n\n\
        Input format: binary trust_ir bitcode (.tmbc) is the default.\n\
        JSON wire-format input is retained as a debug-only flag; pass\n\
        `--format=json` to enable it. Pass `--format=text` to read a\n\
        human-readable `.trust_ir` module (see issue #413). See issue #414\n\
        and the trust_ir transport architecture design.\n\n\
        Examples:\n  \
        trust-cg -O2 -o prog a.tmbc b.tmbc      # compile + link (binary default)\n  \
        trust-cg -c a.tmbc b.tmbc                # compile only (.o)\n  \
        trust-cg -g -O2 -o prog a.tmbc           # with debug info\n  \
        trust-cg --format=json module.json       # debug JSON input (opt-in)\n  \
        trust-cg --format=text module.trust_ir       # human-readable .trust_ir debug text\n  \
        trust-cg --emit-trust_ir out.trust_ir in.tmbc    # dump module as .trust_ir text\n  \
        trust-cg --format=auto legacy.trust_ir       # legacy extension/magic sniffing"
)]
struct Cli {
    /// Input trust_ir module files (positional). Default format is binary
    /// `.tmbc` bitcode; pass `--format=json` for the debug JSON wire
    /// format, or `--format=text` for human-readable `.trust_ir` text (#413).
    ///
    /// Multiple files are compiled in parallel and linked together.
    #[arg(value_name = "INPUT")]
    inputs: Vec<PathBuf>,

    /// Select the trust_ir input format (`binary` default, `json` debug-only,
    /// `text` human-readable `.trust_ir` (#413), `auto` legacy sniffing).
    ///
    /// Per the trust_ir transport architecture, binary `.tmbc` is the hot
    /// path for production tooling. JSON is retained solely for
    /// debugging and external-tool integration and must be enabled
    /// explicitly via `--format=json`. The human-readable `.trust_ir` text
    /// format is the canonical debug format for the t* stack and is
    /// enabled via `--format=text` (upstream `trust_ir::parser` feature).
    #[arg(long = "format", value_enum, default_value_t = InputFormatArg::Binary)]
    format: InputFormatArg,

    /// Run the bounded straight-line fsym trust_ir preflight (`off` default).
    ///
    /// `warn` emits `warning[fsym]` diagnostics and continues compilation.
    /// `error` emits `error[fsym]` diagnostics and exits before codegen if the
    /// scanner finds concrete UB. This preflight is intentionally narrow and
    /// only escalates unknown obligations when `--fsym-solver` is enabled.
    #[arg(long = "fsym", value_enum, default_value_t = FsymModeArg::Off)]
    fsym: FsymModeArg,

    /// Solver backend for fsym unknown obligations (`off` default).
    ///
    /// `local` uses the deterministic bounded local adapter. `ay` routes typed
    /// null/arithmetic/bounds obligations through ay. UAF obligations remain
    /// unsupported until symbolic lifetime solving lands.
    #[arg(long = "fsym-solver", value_enum, default_value_t = FsymSolverArg::Off)]
    fsym_solver: FsymSolverArg,

    /// Write a structured JSON report for the bounded fsym preflight.
    ///
    /// This is opt-in, single-input only, and preserves the existing stderr
    /// warning/error diagnostics.
    #[arg(long = "fsym-report-json")]
    fsym_report_json: Option<PathBuf>,

    /// DEPRECATED: read a single trust_ir module from a JSON wire format
    /// file. Prefer `--format=json <FILE>`. Retained for one release
    /// as an alias; emits a warning when used.
    ///
    /// Mutually exclusive with positional inputs.
    #[arg(long = "input-json", conflicts_with = "inputs")]
    input_json: Option<PathBuf>,

    /// Write the parsed trust_ir module as JSON to this path (for round-trip testing).
    /// Only valid with a single input file or --input-json.
    #[arg(long = "emit-json")]
    emit_json: Option<PathBuf>,

    /// Write the parsed trust_ir module as human-readable `.trust_ir` text to
    /// this path (for round-trip testing; #413).
    ///
    /// Uses `trust_ir::Module`'s `Display` impl (always on) to render the
    /// module. Only valid with a single input file. Complements
    /// `--emit-json` for quick diffing.
    #[arg(long = "emit-trust_ir")]
    emit_trust_ir: Option<PathBuf>,

    /// Output file path. For -c with a single input, this is the object file.
    /// Without -c, this is the linked executable.
    #[arg(short = 'o', long = "output")]
    output: Option<PathBuf>,

    /// Optimization level.
    #[arg(
        short = 'O',
        long = "opt-level",
        value_parser = parse_opt_level,
        default_value = "2"
    )]
    opt_level: OptLevel,

    /// Target architecture or triple. x86 support is x86_64 only:
    /// x86/i386/i486/i586/i686 aliases and triples are rejected.
    #[arg(long = "target", value_parser = parse_target, default_value = "aarch64")]
    target: TargetSpec,

    /// Compile only -- produce object files, do not link.
    #[arg(short = 'c')]
    compile_only: bool,

    /// Whole-program `panic=unwind` object emission (x86-64 Mach-O).
    ///
    /// Mirrors the rustc-bridge `CompilerConfig::panic_unwind` plumbing for
    /// the CLI front door: every frame-covered function in every emitted
    /// object gets full walkable FDE coverage (the all-filler "keep walking,
    /// never dispatch" LSDA for pass-through frames), so a panic raised in
    /// one object can unwind THROUGH sibling objects that carry no local
    /// landing pad. Without this, phase-1 unwind stops dead
    /// (`_URC_END_OF_STACK`) at the first pass-through frame on x86-64
    /// Mach-O, skipping every cleanup Drop and the `catch_unwind` handler.
    /// Read only by the x86-64 Mach-O emitter; AArch64 / ELF / COFF output
    /// is byte-identical with or without this flag (same contract as the
    /// config field). Default off: abort-model objects stay byte-identical.
    #[arg(long = "panic-unwind")]
    panic_unwind: bool,

    /// Emit DWARF debug info sections in the output.
    #[arg(short = 'g')]
    debug_info: bool,

    /// Library search paths passed to the linker (-L <dir>).
    #[arg(short = 'L', value_name = "DIR")]
    lib_paths: Vec<PathBuf>,

    /// Libraries to link (-l <name>).
    #[arg(short = 'l', value_name = "LIB")]
    libs: Vec<String>,

    /// Emit proof certificates to the given directory (issue #421).
    ///
    /// When set, the compiler requires proof promotion for every instruction
    /// and every emitted object relocation. If that full authority gate passes,
    /// it writes one `.smt2` (SMT-LIB2 query) plus one `.cert` (JSON metadata)
    /// file per verified rule, organised under
    /// `<dir>/<ProofCategory>/<proof_name>.{smt2,cert}`. It also writes
    /// per-function `.lowering.json` and `.trust-proof-cert.json` sidecars.
    /// Missing object-relocation authority fails closed before object or
    /// sidecar publication.
    ///
    /// Example:
    ///   trust-cg -c --emit-proofs=proofs/ module.tmbc
    ///
    /// Consumers: `ty` and `tRust` (issues #260, #269).
    /// Design: epic #407, task 6.
    #[arg(long = "emit-proofs", value_name = "DIR")]
    emit_proofs: Option<PathBuf>,

    /// Enable compilation trace output (per-phase timing).
    #[arg(long = "trace")]
    trace: bool,

    /// Print compilation metrics as JSON to stderr.
    #[arg(long = "metrics")]
    metrics: bool,

    /// Disable parallel per-function compilation within each module.
    ///
    /// By default, functions within a module are compiled in parallel using
    /// rayon. This flag disables that, compiling functions sequentially.
    /// Useful for debugging or when thread-safety issues are suspected.
    #[arg(long = "no-parallel")]
    no_parallel: bool,

    /// Enable CEGIS superoptimization with the given per-function budget
    /// in seconds (e.g. `--cegis-superopt=5`). Off by default.
    ///
    /// When set, the compiler runs the CEGIS-based superoptimization pass
    /// on each function with the given wall-clock budget. Results are keyed
    /// into a compilation cache so repeat compilations reuse proven
    /// rewrites. See issue #395 and
    /// `designs/2026-04-18-cache-and-cegis.md`.
    #[arg(long = "cegis-superopt", value_name = "SECS")]
    cegis_superopt: Option<u64>,

    /// Enable the offline local filesystem compile artifact cache.
    #[arg(long = "compile-artifact-cache", value_name = "DIR")]
    compile_artifact_cache: Option<PathBuf>,

    /// Profile-generate mode: instrument the compiled module with
    /// basic-block counters and designate `<PATH>` as the destination
    /// for the resulting `.profdata` file.
    ///
    /// The current CLI surface is the host JIT canary path: the module is
    /// compiled through `Compiler` with block-counter hooks, a simple scalar
    /// entry point is executed, and the captured counters are written to
    /// `<PATH>`. AArch64 uses the raw JIT block trampoline path; x86-64 uses
    /// compiler-pipeline counter injection. Full AOT exit-time runtime dumping
    /// remains a later PGO phase.
    #[arg(
        long = "profile-generate",
        value_name = "PATH",
        conflicts_with = "profile_use"
    )]
    profile_generate: Option<PathBuf>,

    /// Comma-separated u64 canary inputs for `--profile-generate`.
    ///
    /// For scalar JIT profile targets, each value invokes the selected
    /// `(u64)` entry once. For the TY parent-loop run shape, the values
    /// are passed as the bounded parent vector for the single JIT call.
    /// When omitted, the CLI keeps its built-in scalar/TY defaults.
    #[arg(
        long = "profile-generate-inputs",
        value_name = "U64_CSV",
        requires = "profile_generate"
    )]
    profile_generate_inputs: Option<String>,

    /// Profile-use mode: load `<PATH>` as a `.profdata` file and stash
    /// the profile into the compilation pipeline at O2/O3. At O0/O1 the
    /// CLI still validates profile freshness, but warns that profile-use
    /// has no optimization effect.
    #[arg(long = "profile-use", value_name = "PATH")]
    profile_use: Option<PathBuf>,
}

fn parse_opt_level(s: &str) -> Result<OptLevel, String> {
    match s {
        "0" => Ok(OptLevel::O0),
        "1" => Ok(OptLevel::O1),
        "2" => Ok(OptLevel::O2),
        "3" => Ok(OptLevel::O3),
        _ => Err(format!(
            "invalid optimization level '{}': expected 0, 1, 2, or 3",
            s
        )),
    }
}

fn parse_target(s: &str) -> Result<TargetSpec, String> {
    TargetSpec::parse(s).map_err(|err| match err.kind() {
        TargetSpecParseErrorKind::UnsupportedX86ThirtyTwo => format!(
            "{err}; use x86_64, x86-64, x64, or an x86_64 triple such as \
             x86_64-unknown-linux-gnu, x86_64-pc-windows-msvc, \
             x86_64-apple-darwin"
        ),
        _ => format!(
            "{err}; supported targets include aarch64, x86_64 (64-bit x86 only; \
             aliases x86-64 and x64), riscv64, x86_64-unknown-linux-gnu, \
             x86_64-pc-windows-msvc, x86_64-apple-darwin"
        ),
    })
}

/// The result of compiling a single input file.
struct FileCompilationResult {
    /// Path to the generated .o file.
    object_path: PathBuf,
    /// Whether this is a temp file that should be cleaned up after linking.
    is_temp: bool,
    /// Canonical tMBC bytes for the loaded input module.
    trust_ir_bytes: Vec<u8>,
    /// The compilation result from the compiler.
    result: CompilationResult,
}

/// Resolve the list of input file paths from CLI arguments.
fn resolve_inputs(cli: &Cli) -> Vec<PathBuf> {
    match (&cli.inputs.is_empty(), &cli.input_json) {
        (false, None) => cli.inputs.clone(),
        (true, Some(p)) => vec![p.clone()],
        (true, None) => {
            eprintln!("trust-cg: error: no input files specified");
            eprintln!(
                "  usage: trust-cg [OPTIONS] <INPUT>...                # binary .tmbc (default)"
            );
            eprintln!("  usage: trust-cg [OPTIONS] --format=json <FILE>...   # JSON debug input");
            process::exit(1);
        }
        (false, Some(_)) => unreachable!("clap conflicts_with prevents this"),
    }
}

/// Resolve the effective input format.
///
/// `--input-json <FILE>` (deprecated) implies `--format=json` and
/// emits a one-line warning so existing callers learn the new flag.
/// Explicit `--format=<auto|binary|json>` always wins for positional
/// inputs; the two flags cannot be combined because clap marks
/// `--input-json` as `conflicts_with = inputs`, and the deprecated
/// path always means JSON.
fn resolve_format(cli: &Cli) -> FormatMode {
    if cli.input_json.is_some() {
        eprintln!(
            "trust-cg: warning: `--input-json <FILE>` is deprecated; use \
             `--format=json <FILE>` instead (see issue #414)."
        );
        return FormatMode::Json;
    }
    cli.format.to_mode()
}

/// Compute the output .o path for a given input file in compile-only mode.
fn object_path_for(input: &Path, output: Option<&Path>, single: bool) -> PathBuf {
    if single && let Some(out) = output {
        return out.to_path_buf();
    }
    let mut p = input.to_path_buf();
    p.set_extension("o");
    p
}

/// Compute a temporary .o path for linking mode.
fn temp_object_path(input: &Path, index: usize) -> PathBuf {
    let stem = input
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| format!("trust_cg_input_{}", index));
    std::env::temp_dir().join(format!("trust_cg_{}_{}.o", stem, std::process::id()))
}

/// Validate and echo the PGO flags.
///
/// Returns the parsed `.profdata` for `--profile-use`, if any. Terminates
/// the process with a clear error message if the file cannot be read or
/// fails header validation.
///
/// `--profile-generate` validates that the destination can be written and
/// later routes the module through the host JIT block-counter capture path.
/// `--profile-use` fully loads and validates the file header so the CLI
/// fails early on bad inputs.
fn handle_pgo_flags(cli: &Cli) -> Option<trust_cg_opt::pgo::ProfData> {
    if let Some(ref out) = cli.profile_generate {
        validate_profile_generate_path(out);
        eprintln!("trust-cg: --profile-generate: will write {}", out.display());
    }
    if let Some(ref path) = cli.profile_use {
        match trust_cg_opt::pgo::read_from_path(path) {
            Ok(p) => {
                eprintln!(
                    "trust-cg: --profile-use: loaded {} function(s) from {}",
                    p.functions.len(),
                    path.display(),
                );
                if !profile_use_enables_optimization(cli.opt_level) {
                    warn_profile_use_below_o2(cli.opt_level);
                }
                return Some(p);
            }
            Err(e) => {
                eprintln!(
                    "trust-cg: error: cannot load profile '{}': {}",
                    path.display(),
                    e,
                );
                process::exit(1);
            }
        }
    }
    None
}

fn profile_use_enables_optimization(level: OptLevel) -> bool {
    matches!(level, OptLevel::O2 | OptLevel::O3)
}

fn warn_profile_use_below_o2(level: OptLevel) {
    eprintln!(
        "trust-cg: warning: --profile-use has no optimization effect below O2; \
         validating profile freshness but not scheduling profile-guided optimization at {}",
        opt_level_name(level),
    );
}

fn run_fsym_preflight(
    input: &Path,
    module: &trust_ir::Module,
    mode: FsymModeArg,
    solver: FsymSolverArg,
    report_json: Option<&Path>,
) {
    if mode == FsymModeArg::Off {
        return;
    }

    let report = scan_fsym_trust_ir(module);
    let severity = match mode {
        FsymModeArg::Off => return,
        FsymModeArg::Warn => FsymTrustIrSeverity::Warning,
        FsymModeArg::Error => FsymTrustIrSeverity::Error,
    };

    for diagnostic in &report.diagnostics {
        eprintln!("{}", diagnostic.render(severity, Some(input)));
    }

    // Fail-closed deref-coverage invariant: a reachable pointer dereference
    // that recorded no verdict means the scanner dropped an obligation (it
    // would be asserting a safety it never proved). These are always surfaced
    // and are fatal under `--fsym=error`, mirroring the opcode coverage_gate.
    for coverage_error in &report.coverage_errors {
        eprintln!("{}", coverage_error.render(Some(input)));
    }

    if mode == FsymModeArg::Warn {
        for skipped in &report.skipped_functions {
            eprintln!("{}", skipped.render(Some(input)));
        }
        for unknown in &report.unknown_obligations {
            eprintln!("{}", unknown.render(Some(input)));
        }
        if solver == FsymSolverArg::Off && !report.unknown_obligations.is_empty() {
            eprintln!(
                "warning[fsym]: {} unknown obligation(s) require solver-backed fsym; no solver was invoked",
                report.unknown_obligations.len()
            );
        }
    }

    let solver_results = if solver == FsymSolverArg::Off {
        Vec::new()
    } else {
        let summary = FsymSummary::from_trust_ir_report(report.clone());
        let config = FsymSolverEscalationConfig::enabled();
        let solver_report = match solver {
            FsymSolverArg::Off => unreachable!("off solver handled above"),
            FsymSolverArg::Local => summary.escalate_unknown_obligations_locally(&config),
            FsymSolverArg::AY => {
                summary.escalate_unknown_obligations_with_ay(&config, AYConfig::default())
            }
        };

        for result in &solver_report.results {
            eprintln!(
                "{}",
                render_fsym_solver_result(input, result, fsym_solver_result_severity(mode, result))
            );
        }
        solver_report.results
    };
    let solver_concrete_ub = solver_results
        .iter()
        .filter(|result| result.status == FsymSolverStatus::ConcreteUb)
        .count();
    let rejected = mode == FsymModeArg::Error
        && (report.has_concrete_ub() || solver_concrete_ub > 0 || report.has_coverage_error());

    if let Some(path) = report_json {
        write_fsym_preflight_report(
            path,
            &fsym_preflight_report_json(
                input,
                &module.name,
                mode,
                solver,
                &report,
                &solver_results,
                rejected,
            ),
        );
    }

    if rejected {
        if solver_concrete_ub == 0 {
            eprintln!(
                "trust-cg: error: --fsym=error rejected '{}' before codegen ({} concrete UB diagnostic(s), {} deref-coverage error(s))",
                input.display(),
                report.diagnostics.len(),
                report.coverage_errors.len(),
            );
        } else {
            eprintln!(
                "trust-cg: error: --fsym=error rejected '{}' before codegen ({} concrete UB diagnostic(s), {} solver concrete UB result(s), {} deref-coverage error(s))",
                input.display(),
                report.diagnostics.len(),
                solver_concrete_ub,
                report.coverage_errors.len(),
            );
        }
        process::exit(1);
    }
}

fn write_fsym_preflight_report(path: &Path, report: &serde_json::Value) {
    match serde_json::to_string_pretty(report)
        .map_err(|e| e.to_string())
        .and_then(|json| fs::write(path, json).map_err(|e| e.to_string()))
    {
        Ok(()) => {}
        Err(e) => {
            eprintln!(
                "trust-cg: error: failed to write fsym preflight JSON report to '{}': {}",
                path.display(),
                e,
            );
            process::exit(1);
        }
    }
}

fn fsym_preflight_report_json(
    input: &Path,
    module_name: &str,
    mode: FsymModeArg,
    solver: FsymSolverArg,
    report: &FsymTrustIrReport,
    solver_results: &[FsymSolverEscalationResult],
    rejected: bool,
) -> serde_json::Value {
    let solver_concrete_ub = solver_results
        .iter()
        .filter(|result| result.status == FsymSolverStatus::ConcreteUb)
        .count();

    serde_json::json!({
        "schema": "trust-cg.fsym_preflight.v1",
        "input": input.display().to_string(),
        "mode": fsym_mode_name(mode),
        "solver": fsym_solver_name(solver),
        "enabled": true,
        "summary": {
            "scanned_functions": report.scanned_functions,
            "skipped_functions": report.skipped_functions.len(),
            "unknown_obligations": report.unknown_obligations.len(),
            "concrete_ub_diagnostics": report.diagnostics.len(),
            "coverage_errors": report.coverage_errors.len(),
            "solver_results": solver_results.len(),
            "solver_concrete_ub_results": solver_concrete_ub,
            "rejected": rejected,
        },
        "functions": fsym_preflight_function_statuses(module_name, report),
        "diagnostics": report.diagnostics.iter().map(|diagnostic| {
            serde_json::json!({
                "kind": fsym_diagnostic_kind_name(diagnostic.kind),
                "module": &diagnostic.module,
                "function": &diagnostic.function,
                "block": diagnostic.block,
                "inst_index": diagnostic.inst_index,
                "message": &diagnostic.message,
                "span": diagnostic.span.map(|span| {
                    serde_json::json!({
                        "file": span.file,
                        "line": span.line,
                        "col": span.col,
                    })
                }),
                "witness": diagnostic.witness.iter().map(|(name, value)| {
                    serde_json::json!({
                        "name": name,
                        "value": value,
                    })
                }).collect::<Vec<_>>(),
            })
        }).collect::<Vec<_>>(),
        "skipped_functions": report.skipped_functions.iter().map(|skipped| {
            serde_json::json!({
                "function": &skipped.function,
                "reason": fsym_skip_reason_name(skipped.reason),
                "detail": &skipped.detail,
            })
        }).collect::<Vec<_>>(),
        "unknown_obligations": report.unknown_obligations.iter().map(|unknown| {
            serde_json::json!({
                "kind": fsym_diagnostic_kind_name(unknown.kind),
                "label": &unknown.label,
                "module": &unknown.module,
                "function": &unknown.function,
                "block": unknown.block,
                "inst_index": unknown.inst_index,
                "reason": &unknown.reason,
                "path_guards": &unknown.path_guards,
                "candidate_expression": &unknown.candidate_expression,
                "has_solver_candidate": unknown.solver_candidate.is_some(),
            })
        }).collect::<Vec<_>>(),
        "solver_results": solver_results.iter().map(|result| {
            serde_json::json!({
                "status": result.status.as_str(),
                "kind": fsym_diagnostic_kind_name(result.kind),
                "label": &result.label,
                "module": &result.module,
                "function": &result.function,
                "block": result.block,
                "inst_index": result.inst_index,
                "detail": &result.detail,
                "witness": result.witness.iter().map(|(name, value)| {
                    serde_json::json!({
                        "name": name,
                        "value": value,
                    })
                }).collect::<Vec<_>>(),
            })
        }).collect::<Vec<_>>(),
    })
}

fn fsym_preflight_function_statuses(
    module_name: &str,
    report: &FsymTrustIrReport,
) -> Vec<serde_json::Value> {
    let mut functions = BTreeMap::<String, serde_json::Value>::new();

    for function in &report.scanned_function_names {
        functions.insert(
            function.clone(),
            serde_json::json!({
                "module": module_name,
                "function": function,
                "status": "clean_scanned",
            }),
        );
    }

    for skipped in &report.skipped_functions {
        functions.insert(
            skipped.function.clone(),
            serde_json::json!({
                "module": module_name,
                "function": &skipped.function,
                "status": "skipped",
                "reason": fsym_skip_reason_name(skipped.reason),
                "detail": &skipped.detail,
            }),
        );
    }

    for unknown in &report.unknown_obligations {
        functions.insert(
            unknown.function.clone(),
            serde_json::json!({
                "module": &unknown.module,
                "function": &unknown.function,
                "status": "unknown",
            }),
        );
    }

    for diagnostic in &report.diagnostics {
        functions.insert(
            diagnostic.function.clone(),
            serde_json::json!({
                "module": &diagnostic.module,
                "function": &diagnostic.function,
                "status": "concrete_ub",
            }),
        );
    }

    functions.into_values().collect()
}

fn fsym_solver_result_severity(
    mode: FsymModeArg,
    result: &FsymSolverEscalationResult,
) -> FsymTrustIrSeverity {
    if mode == FsymModeArg::Error && result.status == FsymSolverStatus::ConcreteUb {
        FsymTrustIrSeverity::Error
    } else {
        FsymTrustIrSeverity::Warning
    }
}

fn render_fsym_solver_result(
    input: &Path,
    result: &FsymSolverEscalationResult,
    severity: FsymTrustIrSeverity,
) -> String {
    let mut out = format!(
        "{}[fsym-solver]: {}: status={} kind={} label `{}` in module `{}` function `{}` bb{} inst{}: {}",
        fsym_severity_name(severity),
        input.display(),
        result.status.as_str(),
        fsym_diagnostic_kind_name(result.kind),
        result.label,
        result.module,
        result.function,
        result.block,
        result.inst_index,
        result.detail,
    );

    if !result.witness.is_empty() {
        let witness = result
            .witness
            .iter()
            .map(|(name, value)| format!("{name}={value}"))
            .collect::<Vec<_>>()
            .join(", ");
        out.push_str(&format!("; witness: {witness}"));
    }

    out
}

fn fsym_severity_name(severity: FsymTrustIrSeverity) -> &'static str {
    match severity {
        FsymTrustIrSeverity::Warning => "warning",
        FsymTrustIrSeverity::Error => "error",
    }
}

fn fsym_diagnostic_kind_name(kind: FsymTrustIrDiagnosticKind) -> &'static str {
    match kind {
        FsymTrustIrDiagnosticKind::NullDeref => "null-deref",
        FsymTrustIrDiagnosticKind::Arithmetic => "arithmetic",
        FsymTrustIrDiagnosticKind::OutOfBounds => "bounds",
        FsymTrustIrDiagnosticKind::UseAfterFree => "use-after-free",
    }
}

fn fsym_skip_reason_name(reason: FsymTrustIrSkipReason) -> &'static str {
    match reason {
        FsymTrustIrSkipReason::Loop => "loop",
        FsymTrustIrSkipReason::Switch => "switch",
        FsymTrustIrSkipReason::TooLarge => "too-large",
        FsymTrustIrSkipReason::MalformedCfg => "malformed-cfg",
        FsymTrustIrSkipReason::UnsupportedTerminator => "unsupported-terminator",
        FsymTrustIrSkipReason::UnsupportedInstruction => "unsupported-instruction",
    }
}

fn fsym_mode_name(mode: FsymModeArg) -> &'static str {
    match mode {
        FsymModeArg::Off => "off",
        FsymModeArg::Warn => "warn",
        FsymModeArg::Error => "error",
    }
}

fn fsym_solver_name(solver: FsymSolverArg) -> &'static str {
    match solver {
        FsymSolverArg::Off => "off",
        FsymSolverArg::Local => "local",
        FsymSolverArg::AY => "ay",
    }
}

fn validate_profile_generate_path(path: &Path) {
    if let Some(parent) = path.parent()
        && !parent.as_os_str().is_empty()
        && !parent.is_dir()
    {
        eprintln!(
            "trust-cg: error: cannot write profile '{}': parent directory '{}' does not exist",
            path.display(),
            parent.display(),
        );
        process::exit(1);
    }

    match fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(false)
        .open(path)
    {
        Ok(_) => {}
        Err(e) => {
            eprintln!(
                "trust-cg: error: cannot write profile '{}': {}",
                path.display(),
                e,
            );
            process::exit(1);
        }
    }
}

const DEFAULT_I64_PROFILE_INPUTS: &[u64] = &[1, 2, 3, 4, 5, 6, 7, 0, 0, 0];
const DEFAULT_TY_PARENT_PROFILE_INPUTS: &[u64] = &[2, 5, 8, 13, 21, 34];
const TY_PARENT_SUMMARY_SLOTS: usize = 5;

#[allow(clippy::enum_variant_names)]
#[derive(Clone, Copy)]
enum ProfileRunShape {
    NoArgsNoReturn,
    NoArgsI64Return,
    I64ArgNoReturn,
    I64ArgI64Return,
    TyParentLoopU64Return,
}

struct ProfileRunTarget {
    name: String,
    shape: ProfileRunShape,
    inputs: Vec<u64>,
}

impl ProfileRunTarget {
    fn call_count(&self) -> usize {
        match self.shape {
            ProfileRunShape::NoArgsNoReturn
            | ProfileRunShape::NoArgsI64Return
            | ProfileRunShape::TyParentLoopU64Return => 1,
            ProfileRunShape::I64ArgNoReturn | ProfileRunShape::I64ArgI64Return => self.inputs.len(),
        }
    }

    fn shape_name(&self) -> &'static str {
        match self.shape {
            ProfileRunShape::NoArgsNoReturn => "no_args_no_return",
            ProfileRunShape::NoArgsI64Return => "no_args_i64_return",
            ProfileRunShape::I64ArgNoReturn => "i64_arg_no_return",
            ProfileRunShape::I64ArgI64Return => "i64_arg_i64_return",
            ProfileRunShape::TyParentLoopU64Return => "ty_parent_loop_u64_return",
        }
    }
}

struct ProfileCanaryObservation {
    return_value: Option<u64>,
    ty_summary: Option<[u64; TY_PARENT_SUMMARY_SLOTS]>,
}

impl ProfileCanaryObservation {
    fn empty() -> Self {
        Self {
            return_value: None,
            ty_summary: None,
        }
    }
}

#[derive(Debug)]
struct ProfileCounterSummary {
    function_count: usize,
    block_count: usize,
    edge_count: usize,
    total_call_count: u64,
    total_block_hits: u64,
    max_block_hits: u64,
}

impl ProfileCounterSummary {
    fn from_profile(profile: &trust_cg_opt::pgo::ProfData) -> Self {
        let block_count = profile.functions.iter().map(|f| f.blocks.len()).sum();
        let edge_count = profile.functions.iter().map(|f| f.edges.len()).sum();
        let total_call_count = profile.functions.iter().map(|f| f.call_count).sum();
        let total_block_hits = profile
            .functions
            .iter()
            .flat_map(|f| f.blocks.iter())
            .map(|b| b.hits)
            .sum();
        let max_block_hits = profile
            .functions
            .iter()
            .flat_map(|f| f.blocks.iter())
            .map(|b| b.hits)
            .max()
            .unwrap_or(0);

        Self {
            function_count: profile.functions.len(),
            block_count,
            edge_count,
            total_call_count,
            total_block_hits,
            max_block_hits,
        }
    }
}

fn parse_profile_generate_inputs(csv: &str) -> Result<Vec<u64>, String> {
    if csv.trim().is_empty() {
        return Err("--profile-generate-inputs requires at least one u64 value".to_string());
    }

    csv.split(',')
        .enumerate()
        .map(|(idx, raw)| {
            let value = raw.trim();
            if value.is_empty() {
                return Err(format!(
                    "--profile-generate-inputs has an empty value at position {}",
                    idx + 1
                ));
            }
            value.parse::<u64>().map_err(|e| {
                format!(
                    "--profile-generate-inputs value '{}' at position {} is not a u64: {}",
                    value,
                    idx + 1,
                    e
                )
            })
        })
        .collect()
}

fn default_profile_inputs(shape: ProfileRunShape) -> Vec<u64> {
    match shape {
        ProfileRunShape::NoArgsNoReturn | ProfileRunShape::NoArgsI64Return => Vec::new(),
        ProfileRunShape::I64ArgNoReturn | ProfileRunShape::I64ArgI64Return => {
            DEFAULT_I64_PROFILE_INPUTS.to_vec()
        }
        ProfileRunShape::TyParentLoopU64Return => DEFAULT_TY_PARENT_PROFILE_INPUTS.to_vec(),
    }
}

fn apply_supplied_profile_inputs(
    mut target: ProfileRunTarget,
    supplied_inputs: Option<&[u64]>,
) -> Result<ProfileRunTarget, String> {
    let Some(inputs) = supplied_inputs else {
        return Ok(target);
    };

    match target.shape {
        ProfileRunShape::I64ArgNoReturn
        | ProfileRunShape::I64ArgI64Return
        | ProfileRunShape::TyParentLoopU64Return => {
            target.inputs = inputs.to_vec();
            Ok(target)
        }
        ProfileRunShape::NoArgsNoReturn | ProfileRunShape::NoArgsI64Return => Err(format!(
            "--profile-generate-inputs cannot be used with selected no-argument target '{}'",
            target.name
        )),
    }
}

fn is_i64_abi_ty(ty: &trust_ir::Ty) -> bool {
    matches!(ty, trust_ir::Ty::I64 | trust_ir::Ty::U64)
}

fn is_no_return(returns: &[trust_ir::Ty]) -> bool {
    returns.is_empty() || matches!(returns, [trust_ir::Ty::Unit])
}

fn profile_shape(ft: &trust_ir::FuncTy) -> Option<ProfileRunShape> {
    match (ft.params.as_slice(), ft.returns.as_slice()) {
        ([], returns) if is_no_return(returns) => Some(ProfileRunShape::NoArgsNoReturn),
        ([], [ret]) if is_i64_abi_ty(ret) => Some(ProfileRunShape::NoArgsI64Return),
        ([trust_ir::Ty::Ptr, trust_ir::Ty::U64, trust_ir::Ty::Ptr], [trust_ir::Ty::U64]) => {
            Some(ProfileRunShape::TyParentLoopU64Return)
        }
        ([param], returns) if is_i64_abi_ty(param) && is_no_return(returns) => {
            Some(ProfileRunShape::I64ArgNoReturn)
        }
        ([param], [ret]) if is_i64_abi_ty(param) && is_i64_abi_ty(ret) => {
            Some(ProfileRunShape::I64ArgI64Return)
        }
        _ => None,
    }
}

fn select_profile_run_target(
    module: &trust_ir::Module,
    supplied_inputs: Option<&[u64]>,
) -> Result<ProfileRunTarget, String> {
    let mut candidates = module.functions.iter().filter_map(|func| {
        let ft = module.func_types.get(func.ty.as_usize())?;
        let shape = profile_shape(ft)?;
        Some(ProfileRunTarget {
            name: func.name.clone(),
            shape,
            inputs: default_profile_inputs(shape),
        })
    });

    let first = candidates.next().ok_or_else(|| {
        "no JIT profile-generate entry with supported signature; \
         expected () -> (), () -> i64, (i64) -> (), (i64) -> i64, \
         or TY parent loop (ptr, u64, ptr) -> u64"
            .to_string()
    })?;

    let target = if first.name == "main" || first.name == "_main" {
        first
    } else {
        candidates
            .find(|target| target.name == "main" || target.name == "_main")
            .unwrap_or(first)
    };

    apply_supplied_profile_inputs(target, supplied_inputs)
}

fn invoke_profile_target(
    buffer: &trust_cg_codegen::jit::ExecutableBuffer,
    target: &ProfileRunTarget,
) -> Result<ProfileCanaryObservation, String> {
    let mut observation = ProfileCanaryObservation::empty();
    match target.shape {
        ProfileRunShape::NoArgsNoReturn => {
            let func = unsafe { buffer.get_fn_bound::<extern "C" fn()>(&target.name) }
                .ok_or_else(|| format!("JIT symbol '{}' was not emitted", target.name))?;
            (*func.as_ref())();
        }
        ProfileRunShape::NoArgsI64Return => {
            let func = unsafe { buffer.get_fn_bound::<extern "C" fn() -> u64>(&target.name) }
                .ok_or_else(|| format!("JIT symbol '{}' was not emitted", target.name))?;
            observation.return_value = Some((*func.as_ref())());
        }
        ProfileRunShape::I64ArgNoReturn => {
            let func = unsafe { buffer.get_fn_bound::<extern "C" fn(u64)>(&target.name) }
                .ok_or_else(|| format!("JIT symbol '{}' was not emitted", target.name))?;
            for input in &target.inputs {
                (*func.as_ref())(*input);
            }
        }
        ProfileRunShape::I64ArgI64Return => {
            let func = unsafe { buffer.get_fn_bound::<extern "C" fn(u64) -> u64>(&target.name) }
                .ok_or_else(|| format!("JIT symbol '{}' was not emitted", target.name))?;
            for input in &target.inputs {
                observation.return_value = Some((*func.as_ref())(*input));
            }
        }
        ProfileRunShape::TyParentLoopU64Return => {
            let func = unsafe {
                buffer.get_fn_bound::<extern "C" fn(*const u64, u64, *mut u64) -> u64>(&target.name)
            }
            .ok_or_else(|| format!("JIT symbol '{}' was not emitted", target.name))?;
            let mut summary = [u64::MAX; TY_PARENT_SUMMARY_SLOTS];
            observation.return_value = Some((*func.as_ref())(
                target.inputs.as_ptr(),
                target.inputs.len() as u64,
                summary.as_mut_ptr(),
            ));
            observation.ty_summary = Some(summary);
        }
    }
    Ok(observation)
}

fn profile_sha256_from_path(path: &Path) -> Option<String> {
    fs::read(path)
        .ok()
        .map(|bytes| format!("sha256:{}", sha256_hex(&bytes)))
}

fn profile_report_key_json(profile: &trust_cg_opt::pgo::ProfData) -> serde_json::Value {
    serde_json::json!({
        "profile_key_digest": profile.profile_key_digest.clone(),
        "module_hash": profile.module_hash.clone(),
        "target_triple": profile.target_triple.clone(),
        "target_cpu": profile.target_cpu.clone(),
        "target_features": profile.target_features.clone(),
        "opt_level": profile.opt_level.clone(),
        "opt_level_num": profile.opt_level_num,
        "cache_key_version": profile.cache_key_version,
    })
}

fn profile_counter_summary_json(profile: &trust_cg_opt::pgo::ProfData) -> serde_json::Value {
    let summary = ProfileCounterSummary::from_profile(profile);
    serde_json::json!({
        "function_count": summary.function_count,
        "block_count": summary.block_count,
        "edge_count": summary.edge_count,
        "total_call_count": summary.total_call_count,
        "total_block_hits": summary.total_block_hits,
        "max_block_hits": summary.max_block_hits,
    })
}

fn emit_profile_generate_report(
    profile: &trust_cg_opt::pgo::ProfData,
    profile_path: &Path,
    target: &ProfileRunTarget,
    observation: &ProfileCanaryObservation,
) {
    let profile_sha256 = profile_sha256_from_path(profile_path);
    let report = serde_json::json!({
        "schema": "trust-cg.profile_report.v1",
        "mode": "profile-generate",
        "capture": {
            "kind": "host-jit-canary",
            "hook_mode": "block-counts",
            "entry": target.name.clone(),
            "entry_shape": target.shape_name(),
            "call_count": target.call_count(),
            "inputs": target.inputs.clone(),
            "window": {
                "kind": "bounded-input-window",
                "start_index": 0,
                "count": target.inputs.len(),
            },
            "return_value": observation.return_value,
            "ty_summary": observation.ty_summary.map(|summary| {
                serde_json::json!({
                    "state_count": summary[0],
                    "generated_count": summary[1],
                    "parent_digest": summary[2],
                    "fingerprint": summary[3],
                    "status": summary[4],
                })
            }),
        },
        "profile_key": profile_report_key_json(profile),
        "profile": {
            "path": profile_path.display().to_string(),
            "sha256": profile_sha256,
        },
        "counters": profile_counter_summary_json(profile),
        "profile_use": {
            "fresh": true,
            "consumer": "not-run-in-profile-generate",
            "scheduled": false,
        },
    });
    eprintln!("trust-cg: profile-report: {}", report);
}

fn emit_profile_use_report(
    profile: &trust_cg_opt::pgo::ProfData,
    profile_path: Option<&Path>,
    scheduled: bool,
) {
    let hotness = trust_cg_opt::pgo::ProfileHotness::from_profile(profile);
    let stats = hotness.stats();
    let profile_sha256 = profile_path.and_then(profile_sha256_from_path);
    let report = serde_json::json!({
        "schema": "trust-cg.profile_report.v1",
        "mode": "profile-use",
        "profile_key": profile_report_key_json(profile),
        "profile": {
            "path": profile_path.map(|path| path.display().to_string()),
            "sha256": profile_sha256,
        },
        "counters": profile_counter_summary_json(profile),
        "profile_use": {
            "fresh": true,
            "consumer": "optimization-pipeline",
            "scheduled": scheduled,
            "pass": if scheduled { Some("profile-use") } else { None },
            "reason": if scheduled {
                "opt-level-enables-profile-use"
            } else {
                "opt-level-below-o2"
            },
            "summary": {
                "profiled_blocks": stats.profiled_blocks,
                "hot_functions": stats.hot_functions,
                "warm_functions": stats.warm_functions,
                "cold_functions": stats.cold_functions,
                "hot_blocks": stats.hot_blocks,
                "warm_blocks": stats.warm_blocks,
                "cold_blocks": stats.cold_blocks,
                "max_function_count": stats.max_function_count,
                "total_function_count": stats.total_function_count,
            },
        },
    });
    eprintln!("trust-cg: profile-report: {}", report);
}

fn run_profile_generate_jit(
    module: &trust_ir::Module,
    trust_ir_bytes: &[u8],
    config: &CompilerConfig,
    target_spec: TargetSpec,
    out: &Path,
    supplied_inputs: Option<&[u64]>,
) {
    if config.target != Target::host() {
        eprintln!(
            "trust-cg: error: --profile-generate JIT capture requires target {} to match host {}",
            config.target.name(),
            Target::host().name(),
        );
        process::exit(1);
    }
    if target_spec.has_explicit_os_abi() && target_spec.with_default_os_abi() != TargetSpec::host()
    {
        eprintln!(
            "trust-cg: error: --profile-generate JIT capture requires target triple {} to match host triple {}",
            target_spec.with_default_os_abi().triple(),
            TargetSpec::host().triple(),
        );
        process::exit(1);
    }

    let target = match select_profile_run_target(module, supplied_inputs) {
        Ok(target) => target,
        Err(e) => {
            eprintln!("trust-cg: error: --profile-generate: {}", e);
            process::exit(1);
        }
    };

    let extern_symbols = std::collections::HashMap::new();
    let jit = match Compiler::new(config.clone()).compile_module_to_jit_with_profile_hooks(
        module,
        &extern_symbols,
        ProfileHookMode::BlockCounts,
    ) {
        Ok(jit) => jit,
        Err(e) => {
            eprintln!(
                "trust-cg: error: --profile-generate JIT capture failed: {}",
                e
            );
            process::exit(1);
        }
    };

    let observation = match invoke_profile_target(&jit.buffer, &target) {
        Ok(observation) => observation,
        Err(e) => {
            eprintln!("trust-cg: error: --profile-generate: {}", e);
            process::exit(1);
        }
    };

    let profile_key = pgo_cache_key(trust_ir_bytes, config, target_spec);
    let profile = jit.buffer.block_profdata_with_key(&profile_key);

    if let Err(e) = trust_cg_opt::pgo::write_to_path(&profile, out) {
        eprintln!(
            "trust-cg: error: cannot write profile '{}': {}",
            out.display(),
            e,
        );
        process::exit(1);
    }
    emit_profile_generate_report(&profile, out, &target, &observation);

    eprintln!(
        "trust-cg: --profile-generate: ran {} call(s) through '{}' and wrote {} function profile(s) -> {}",
        target.call_count(),
        target.name,
        profile.functions.len(),
        out.display(),
    );
}

/// Build a CompilerConfig from CLI flags.
fn build_config(cli: &Cli) -> CompilerConfig {
    CompilerConfig {
        opt_level: cli.opt_level,
        target: cli.target.architecture,
        emit_proofs: cli.emit_proofs.is_some(),
        trace_level: if cli.trace {
            CompilerTraceLevel::Full
        } else {
            CompilerTraceLevel::None
        },
        emit_debug: cli.debug_info,
        parallel: !cli.no_parallel,
        cegis_superopt_budget_sec: cli.cegis_superopt,
        enable_fsym_trust_ir_preflight: cli.fsym != FsymModeArg::Off,
        // AOT object compilation through the CLI keeps the full quality
        // regalloc. The latency-tuned JitFast profile is reserved for the
        // in-process JIT path (CompilerConfig::for_host_jit).
        enable_jit_fast_regalloc: false,
        // The CLI is an AOT front door; it never opts JIT execution out of
        // the per-arch default validation mode. None = fail-closed default.
        jit_validation_mode_override: None,
        // Whole-program panic=unwind: default abort model; `--panic-unwind`
        // opts the x86-64 Mach-O emitter into full walkable FDE coverage for
        // pass-through frames (the rustc bridge derives the same bit from
        // `tcx.sess.panic_strategy()`).
        panic_unwind: cli.panic_unwind,
    }
}

fn build_config_for_input_count(cli: &Cli, input_count: usize) -> CompilerConfig {
    let mut config = build_config(cli);
    if input_count > 1 {
        // Multi-file CLI compilation already fans out across files. Keep each
        // module internally sequential so large modules do not multiply peak
        // prepared-function/proof memory across nested Rayon work.
        config.parallel = false;
    }
    config
}

fn compile_artifact_cache_config(
    cli: &Cli,
    config: &CompilerConfig,
) -> Option<CompileArtifactCacheConfig> {
    cli.compile_artifact_cache.as_ref().map(|root| {
        CompileArtifactCacheConfig::production_default(
            root.clone(),
            config.compile_artifact_proof_policy(),
        )
    })
}

fn opt_level_name(level: OptLevel) -> &'static str {
    match level {
        OptLevel::O0 => "O0",
        OptLevel::O1 => "O1",
        OptLevel::O2 => "O2",
        OptLevel::O3 => "O3",
    }
}

fn opt_level_num(level: OptLevel) -> u8 {
    match level {
        OptLevel::O0 => 0,
        OptLevel::O1 => 1,
        OptLevel::O2 => 2,
        OptLevel::O3 => 3,
    }
}

fn target_triple_for(target_spec: TargetSpec) -> String {
    target_spec.with_default_os_abi().triple()
}

fn target_cpu_for(target: Target) -> &'static str {
    match target {
        Target::Aarch64 => "generic-aarch64",
        Target::X86_64 => "generic-x86_64",
        Target::Riscv64 => "generic-riscv64",
    }
}

fn target_features_for(target: Target) -> Vec<String> {
    match target {
        Target::Aarch64 => vec!["+neon".to_string()],
        Target::X86_64 => vec!["+sse2".to_string()],
        Target::Riscv64 => Vec::new(),
    }
}

fn pgo_cache_key(
    trust_ir_bytes: &[u8],
    config: &CompilerConfig,
    target_spec: TargetSpec,
) -> trust_cg_opt::CacheKey {
    trust_cg_opt::CacheKey::new(
        trust_cg_opt::stable_hash(trust_ir_bytes),
        opt_level_num(config.opt_level),
        target_triple_for(target_spec),
        target_cpu_for(config.target).to_string(),
        target_features_for(config.target),
    )
}

fn canonical_compiler_config_bytes(config: &CompilerConfig, target_spec: TargetSpec) -> Vec<u8> {
    let target_spec = target_spec.with_default_os_abi();
    let json = serde_json::json!({
        "schema": "trust-cg.compiler_config.v2",
        "target": config.target.name(),
        "target_triple": target_spec.triple(),
        "target_vendor": target_spec.vendor.triple_component(),
        "target_os": target_spec.operating_system.triple_component(),
        "target_environment": target_spec.environment.triple_component(),
        "opt_level": opt_level_name(config.opt_level),
        "emit_proofs": config.emit_proofs,
        "emit_debug": config.emit_debug,
        "parallel": config.parallel,
        "cegis_superopt_budget_sec": config.cegis_superopt_budget_sec,
    });
    serde_json::to_vec(&json).expect("compiler config JSON serialization should not fail")
}

/// Compile a single input file and return the result.
#[allow(clippy::too_many_arguments)]
fn compile_one(
    input: &Path,
    config: &CompilerConfig,
    target_spec: TargetSpec,
    format: FormatMode,
    obj_path: &Path,
    is_temp: bool,
    fsym_mode: FsymModeArg,
    fsym_solver: FsymSolverArg,
    fsym_report_json: Option<&Path>,
    profile_use: Option<&trust_cg_opt::pgo::ProfData>,
    profile_use_path: Option<&Path>,
    profile_generate: Option<&Path>,
    profile_generate_inputs: Option<&[u64]>,
    compile_artifact_cache: Option<&CompileArtifactCacheConfig>,
) -> FileCompilationResult {
    // Load the trust_ir module using the explicit format selection (#414).
    let module: trust_ir::Module = match pipeline::load_module_as(input, format) {
        Ok(m) => m,
        Err(e) => {
            eprintln!(
                "trust-cg: error: failed to read trust_ir module from '{}': {}",
                input.display(),
                e,
            );
            process::exit(1);
        }
    };
    run_fsym_preflight(input, &module, fsym_mode, fsym_solver, fsym_report_json);

    let trust_ir_bytes = match pipeline::encode_tmbc(&module) {
        Ok(bytes) => bytes,
        Err(e) => {
            eprintln!(
                "trust-cg: error: failed to encode canonical tMBC for '{}': {}",
                input.display(),
                e,
            );
            process::exit(1);
        }
    };

    if let Some(profile) = profile_use {
        let profile_key = pgo_cache_key(&trust_ir_bytes, config, target_spec);
        if let Err(e) = trust_cg_opt::pgo::enforce_fresh(profile, &profile_key) {
            eprintln!(
                "trust-cg: error: --profile-use is stale for '{}': {}",
                input.display(),
                e,
            );
            process::exit(1);
        }
        emit_profile_use_report(
            profile,
            profile_use_path,
            profile_use_enables_optimization(config.opt_level),
        );
    }

    // Compile.
    let mut compiler = Compiler::new_for_target_spec(config.clone(), target_spec);
    if let Some(profile) =
        profile_use.filter(|_| profile_use_enables_optimization(config.opt_level))
    {
        compiler = compiler.with_profile_use(profile.clone());
    }
    if let Some(cache) = compile_artifact_cache {
        compiler = compiler.with_compile_artifact_cache(cache.clone());
    }
    let result = match compiler.compile(&module) {
        Ok(r) => r,
        Err(e) => {
            eprintln!(
                "trust-cg: error: compilation of '{}' failed: {}",
                input.display(),
                e,
            );
            process::exit(1);
        }
    };

    // Write the .o file.
    if let Err(e) = fs::write(obj_path, &result.object_code) {
        eprintln!(
            "trust-cg: error: cannot write '{}': {}",
            obj_path.display(),
            e,
        );
        process::exit(1);
    }

    if let Some(out) = profile_generate {
        run_profile_generate_jit(
            &module,
            &trust_ir_bytes,
            config,
            target_spec,
            out,
            profile_generate_inputs,
        );
    }

    FileCompilationResult {
        object_path: obj_path.to_path_buf(),
        is_temp,
        trust_ir_bytes,
        result,
    }
}

/// Print trace information for a compilation result.
fn print_trace(result: &CompilationResult) {
    if let Some(ref trace) = result.trace {
        eprintln!("--- compilation trace ---");
        for entry in &trace.entries {
            let detail = entry.detail.as_deref().unwrap_or("");
            eprintln!(
                "  {:20} {:>8.2}ms  {}",
                entry.phase,
                entry.duration.as_secs_f64() * 1000.0,
                detail,
            );
        }
        eprintln!(
            "  {:20} {:>8.2}ms",
            "TOTAL",
            trace.total_duration.as_secs_f64() * 1000.0,
        );
        eprintln!("--- end trace ---");
    }
}

/// Emit per-proof SMT-LIB2 + certificate files for a compilation result.
///
/// Implements the core of `--emit-proofs=<dir>` (issue #421). Errors are
/// missing compiler certificates are reported on stderr, but sidecar
/// certification errors are propagated so `--emit-proofs` is fail-closed.
fn emit_proof_artifacts(
    dir: &Path,
    result: &CompilationResult,
    target_spec: TargetSpec,
    trust_ir_bytes: &[u8],
    compiler_config_bytes: &[u8],
) -> io::Result<Option<emit_proofs::EmitSummary>> {
    let certs = match &result.proofs {
        Some(c) => c,
        None => {
            eprintln!("trust-cg: warning: --emit-proofs set but compiler produced no certificates");
            return Ok(None);
        }
    };

    let target_triple = target_spec.with_default_os_abi().triple();
    emit_proofs::emit_proof_files_with_lowering_sidecars(
        dir,
        certs.as_slice(),
        emit_proofs::LoweringSidecarInputs {
            target: &target_triple,
            trust_ir_bytes,
            machine_code_bytes: &result.object_code,
            compiler_config_bytes,
        },
    )
    .map(Some)
}

/// Print proof certificates for a compilation result.
fn print_proofs(result: &CompilationResult) {
    if let Some(ref proofs) = result.proofs {
        if proofs.is_empty() {
            eprintln!(
                "trust-cg: note: proof emission enabled but no certificates produced (ay not yet integrated)"
            );
        } else {
            eprintln!("--- proof certificates ---");
            for cert in proofs {
                let status = if cert.verified {
                    "VERIFIED"
                } else {
                    "UNVERIFIED"
                };
                eprintln!("  {} [{}]", cert.rule_name, status);
            }
            eprintln!("--- end proofs ---");
        }
    }
}

/// Print compilation metrics for a compilation result.
fn print_metrics(result: &CompilationResult) {
    let metrics_json = serde_json::json!({
        "code_size_bytes": result.metrics.code_size_bytes,
        "instruction_count": result.metrics.instruction_count,
        "function_count": result.metrics.function_count,
        "optimization_passes_run": result.metrics.optimization_passes_run,
        "compile_artifact_cache": cache_telemetry_json(
            &result.compile_artifact_cache_telemetry
        ),
    });
    eprintln!("{}", serde_json::to_string_pretty(&metrics_json).unwrap());
}

fn cache_telemetry_json(events: &[CompileArtifactCacheTelemetry]) -> Vec<serde_json::Value> {
    events
        .iter()
        .map(|event| {
            serde_json::json!({
                "boundary": event.boundary.as_str(),
                "status": event.status.as_str(),
                "key_sha256": &event.key_sha256,
                "artifact_sha256": event.artifact_sha256.as_deref(),
                "cache_path": event.cache_path.display().to_string(),
                "reason": event.reason.as_deref(),
                "elapsed_micros": event.elapsed_micros,
            })
        })
        .collect()
}

/// Map target architecture to linker -arch flag value.
fn linker_arch(target: Target) -> &'static str {
    match target {
        Target::Aarch64 => "arm64",
        Target::X86_64 => "x86_64",
        Target::Riscv64 => "riscv64",
    }
}

/// Add target-specific arguments understood by the host `cc` driver.
fn configure_linker_target(cmd: &mut Command, target_spec: TargetSpec) {
    if target_spec.operating_system == TargetOperatingSystem::Darwin {
        cmd.arg("-arch").arg(linker_arch(target_spec.architecture));
    }
}

/// Invoke the system linker to combine object files into an executable.
fn link(
    object_files: &[PathBuf],
    output: &PathBuf,
    target_spec: TargetSpec,
    lib_paths: &[PathBuf],
    libs: &[String],
) {
    let mut cmd = Command::new("cc");
    let target_spec = target_spec.with_default_os_abi();

    cmd.arg("-o").arg(output);
    configure_linker_target(&mut cmd, target_spec);

    for obj in object_files {
        cmd.arg(obj);
    }

    for dir in lib_paths {
        cmd.arg(format!("-L{}", dir.display()));
    }

    for lib in libs {
        cmd.arg(format!("-l{}", lib));
    }

    eprintln!(
        "trust-cg: linking {} object file(s) -> {}",
        object_files.len(),
        output.display(),
    );

    match cmd.status() {
        Ok(status) if status.success() => {}
        Ok(status) => {
            eprintln!(
                "trust-cg: error: linker exited with status {}",
                status.code().unwrap_or(-1),
            );
            process::exit(1);
        }
        Err(e) => {
            eprintln!("trust-cg: error: failed to invoke linker 'cc': {}", e);
            if target_spec.operating_system == TargetOperatingSystem::Darwin {
                eprintln!(
                    "  hint: ensure Xcode command line tools are installed (xcode-select --install)"
                );
            } else {
                eprintln!(
                    "  hint: install a C toolchain capable of linking {} objects",
                    target_spec.triple()
                );
            }
            process::exit(1);
        }
    }
}

/// Clean up temporary object files.
fn cleanup_temps(files: &[FileCompilationResult]) {
    for f in files {
        if f.is_temp {
            let _ = fs::remove_file(&f.object_path);
        }
    }
}

fn main() {
    let cli = Cli::parse();
    let inputs = resolve_inputs(&cli);
    let format = resolve_format(&cli);

    // Validate: --emit-json / --emit-trust_ir only make sense with a single input.
    if cli.emit_json.is_some() && inputs.len() > 1 {
        eprintln!("trust-cg: error: --emit-json requires exactly one input file");
        process::exit(1);
    }
    if cli.emit_trust_ir.is_some() && inputs.len() > 1 {
        eprintln!("trust-cg: error: --emit-trust_ir requires exactly one input file");
        process::exit(1);
    }
    if cli.fsym_report_json.is_some() && inputs.len() > 1 {
        eprintln!("trust-cg: error: --fsym-report-json requires exactly one input file");
        process::exit(1);
    }
    if cli.fsym_report_json.is_some() && cli.fsym == FsymModeArg::Off {
        eprintln!("trust-cg: error: --fsym-report-json requires --fsym=warn or --fsym=error");
        process::exit(1);
    }
    if cli.profile_generate.is_some() && inputs.len() > 1 {
        eprintln!(
            "trust-cg: error: --profile-generate JIT capture currently requires exactly one input file"
        );
        process::exit(1);
    }
    if cli.profile_use.is_some() && inputs.len() > 1 {
        eprintln!(
            "trust-cg: error: --profile-use currently requires exactly one input file until multi-module profdata is supported"
        );
        process::exit(1);
    }

    // Emit JSON round-trip output if requested (single input only).
    if let Some(ref emit_path) = cli.emit_json {
        let module: trust_ir::Module = match pipeline::load_module_as(&inputs[0], format) {
            Ok(m) => m,
            Err(e) => {
                eprintln!(
                    "trust-cg: error: failed to read trust_ir module from '{}': {}",
                    inputs[0].display(),
                    e,
                );
                process::exit(1);
            }
        };
        match serde_json::to_string_pretty(&module)
            .map_err(|e| e.to_string())
            .and_then(|json| fs::write(emit_path, json).map_err(|e| e.to_string()))
        {
            Ok(()) => {
                eprintln!("trust-cg: wrote trust_ir JSON to {}", emit_path.display());
            }
            Err(e) => {
                eprintln!(
                    "trust-cg: error: failed to write trust_ir JSON to '{}': {}",
                    emit_path.display(),
                    e,
                );
                process::exit(1);
            }
        }
    }

    // Emit .trust_ir text round-trip output if requested (#413, single input only).
    if let Some(ref emit_path) = cli.emit_trust_ir {
        let module: trust_ir::Module = match pipeline::load_module_as(&inputs[0], format) {
            Ok(m) => m,
            Err(e) => {
                eprintln!(
                    "trust-cg: error: failed to read trust_ir module from '{}': {}",
                    inputs[0].display(),
                    e,
                );
                process::exit(1);
            }
        };
        match pipeline::save_module_to_trust_ir_text(&module, emit_path) {
            Ok(()) => {
                eprintln!("trust-cg: wrote trust_ir text to {}", emit_path.display());
            }
            Err(e) => {
                eprintln!(
                    "trust-cg: error: failed to write trust_ir text to '{}': {}",
                    emit_path.display(),
                    e,
                );
                process::exit(1);
            }
        }
    }

    // Parse PGO flags. `--profile-use` is header-validated here and then
    // checked against each input module's stable hash before compilation.
    let loaded_profile = handle_pgo_flags(&cli);
    let profile_generate_inputs = match cli.profile_generate_inputs.as_deref() {
        Some(csv) => match parse_profile_generate_inputs(csv) {
            Ok(inputs) => Some(inputs),
            Err(e) => {
                eprintln!("trust-cg: error: {}", e);
                process::exit(1);
            }
        },
        None => None,
    };

    let config = build_config_for_input_count(&cli, inputs.len());
    let compiler_config_bytes = canonical_compiler_config_bytes(&config, cli.target);
    let compile_artifact_cache = compile_artifact_cache_config(&cli, &config);

    // Determine whether we need temp files (linking mode) or permanent files
    // (compile-only mode).
    let compile_only = cli.compile_only;

    let file_results: Vec<FileCompilationResult> = if inputs.len() == 1 {
        // Single file: no need for rayon overhead.
        let input = &inputs[0];
        let obj_path = if compile_only {
            object_path_for(input, cli.output.as_deref(), true)
        } else {
            temp_object_path(input, 0)
        };
        let is_temp = !compile_only;
        vec![compile_one(
            input,
            &config,
            cli.target,
            format,
            &obj_path,
            is_temp,
            cli.fsym,
            cli.fsym_solver,
            cli.fsym_report_json.as_deref(),
            loaded_profile.as_ref(),
            cli.profile_use.as_deref(),
            cli.profile_generate.as_deref(),
            profile_generate_inputs.as_deref(),
            compile_artifact_cache.as_ref(),
        )]
    } else if let Some(worker_count) = resource_limits::worker_count_for_items(inputs.len()) {
        // Multiple files: bounded parallel compilation via a local Rayon pool.
        let pool = resource_limits::build_rayon_pool(worker_count).unwrap_or_else(|err| {
            eprintln!("trust-cg: error: failed to create bounded worker pool: {err}");
            process::exit(1);
        });
        pool.install(|| {
            inputs
                .par_iter()
                .enumerate()
                .map(|(i, input)| {
                    let obj_path = if compile_only {
                        object_path_for(input, None, false)
                    } else {
                        temp_object_path(input, i)
                    };
                    let is_temp = !compile_only;
                    compile_one(
                        input,
                        &config,
                        cli.target,
                        format,
                        &obj_path,
                        is_temp,
                        cli.fsym,
                        cli.fsym_solver,
                        None,
                        loaded_profile.as_ref(),
                        cli.profile_use.as_deref(),
                        None,
                        None,
                        compile_artifact_cache.as_ref(),
                    )
                })
                .collect()
        })
    } else {
        inputs
            .iter()
            .enumerate()
            .map(|(i, input)| {
                let obj_path = if compile_only {
                    object_path_for(input, None, false)
                } else {
                    temp_object_path(input, i)
                };
                let is_temp = !compile_only;
                compile_one(
                    input,
                    &config,
                    cli.target,
                    format,
                    &obj_path,
                    is_temp,
                    cli.fsym,
                    cli.fsym_solver,
                    None,
                    loaded_profile.as_ref(),
                    cli.profile_use.as_deref(),
                    None,
                    None,
                    compile_artifact_cache.as_ref(),
                )
            })
            .collect()
    };

    // Print per-file diagnostics.
    let mut total_functions = 0usize;
    let mut total_code_bytes = 0usize;
    let mut total_emit_summary = emit_proofs::EmitSummary::default();

    for fr in &file_results {
        print_trace(&fr.result);
        print_proofs(&fr.result);
        if cli.metrics {
            print_metrics(&fr.result);
        }

        // Emit per-proof SMT-LIB2 + certificate files (#421).
        if let Some(ref dir) = cli.emit_proofs {
            match emit_proof_artifacts(
                dir,
                &fr.result,
                cli.target,
                &fr.trust_ir_bytes,
                &compiler_config_bytes,
            ) {
                Ok(Some(s)) => total_emit_summary.merge(s),
                Ok(None) => {}
                Err(e) => {
                    eprintln!(
                        "trust-cg: error: failed to emit proof files to '{}': {}",
                        dir.display(),
                        e,
                    );
                    process::exit(1);
                }
            }
        }

        total_functions += fr.result.metrics.function_count;
        total_code_bytes += fr.result.metrics.code_size_bytes;

        if compile_only {
            eprintln!(
                "trust-cg: compiled {} function(s), {} bytes -> {}",
                fr.result.metrics.function_count,
                fr.result.metrics.code_size_bytes,
                fr.object_path.display(),
            );
        }
    }

    if let Some(emit_proofs) = &cli.emit_proofs {
        eprintln!(
            "trust-cg: wrote {} .smt2 + {} .cert + {} lowering + {} trust-proof-cert file(s) to {} ({} certs had no obligation in the database)",
            total_emit_summary.smt2_written,
            total_emit_summary.cert_written,
            total_emit_summary.lowering_written,
            total_emit_summary.trust_proof_cert_written,
            emit_proofs.display(),
            total_emit_summary.skipped_no_obligation,
        );
    }

    if compile_only {
        // Done -- object files are in place.
        return;
    }

    // Linking mode: combine all .o files into an executable.
    let output_path = cli.output.unwrap_or_else(|| PathBuf::from("a.out"));

    let object_paths: Vec<PathBuf> = file_results.iter().map(|f| f.object_path.clone()).collect();

    link(
        &object_paths,
        &output_path,
        cli.target,
        &cli.lib_paths,
        &cli.libs,
    );

    // Clean up temp .o files.
    cleanup_temps(&file_results);

    eprintln!(
        "trust-cg: linked {} file(s), {} function(s), {} code bytes -> {}",
        file_results.len(),
        total_functions,
        total_code_bytes,
        output_path.display(),
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_target_accepts_requested_x86_triples() {
        let windows = parse_target("x86_64-pc-windows-msvc").unwrap();
        assert_eq!(windows.triple(), "x86_64-pc-windows-msvc");

        let linux = parse_target("x86_64-unknown-linux-gnu").unwrap();
        assert_eq!(linux.triple(), "x86_64-unknown-linux-gnu");

        let darwin = parse_target("x86_64-apple-darwin").unwrap();
        assert_eq!(darwin.triple(), "x86_64-apple-darwin");

        assert_ne!(windows, linux);
        assert_ne!(linux, darwin);
        assert_ne!(windows, darwin);
    }

    #[test]
    fn linker_uses_apple_arch_flag_only_for_darwin() {
        let linux = parse_target("x86_64-unknown-linux-gnu").unwrap();
        let darwin = parse_target("x86_64-apple-darwin").unwrap();

        let mut linux_command = Command::new("cc");
        configure_linker_target(&mut linux_command, linux);
        let linux_args: Vec<_> = linux_command.get_args().collect();
        assert!(linux_args.is_empty());

        let mut darwin_command = Command::new("cc");
        configure_linker_target(&mut darwin_command, darwin);
        let darwin_args: Vec<_> = darwin_command.get_args().collect();
        assert_eq!(darwin_args, ["-arch", "x86_64"]);
    }

    #[test]
    fn parse_target_arch_aliases_stay_architecture_only() {
        let x86_64 = parse_target("x86_64").unwrap();
        assert_eq!(x86_64.architecture, Target::X86_64);
        assert!(!x86_64.has_explicit_os_abi());
        assert_eq!(x86_64.triple(), "x86_64-unknown-unknown");

        let x86 = parse_target("x64").unwrap();
        assert_eq!(x86.architecture, Target::X86_64);
        assert!(!x86.has_explicit_os_abi());
        assert_eq!(x86.triple(), "x86_64-unknown-unknown");

        let aarch64 = parse_target("aarch64").unwrap();
        assert_eq!(aarch64.architecture, Target::Aarch64);
        assert!(!aarch64.has_explicit_os_abi());
        assert_eq!(aarch64.triple(), "aarch64-unknown-unknown");
    }

    #[test]
    fn parse_target_rejects_unsupported_x86_32_aliases_and_triples() {
        for target in [
            "x86",
            "i386",
            "i486",
            "i586",
            "i686",
            "i686-unknown-linux-gnu",
            "i686-pc-windows-msvc",
            "i386-apple-darwin",
        ] {
            let error = match parse_target(target) {
                Ok(spec) => panic!("{target} unexpectedly parsed as {spec}"),
                Err(error) => error,
            };
            assert!(
                error.contains("unsupported 32-bit x86 target"),
                "{target} error should name 32-bit x86 rejection: {error}"
            );
            assert!(
                error.contains("x86_64") && error.contains("x86_64 triple"),
                "{target} error should point to x86_64-only support: {error}"
            );
        }
    }

    #[test]
    fn multi_input_cli_config_disables_inner_function_parallelism() {
        let single = Cli::parse_from(["trust-cg", "one.tmbc"]);
        assert!(build_config_for_input_count(&single, 1).parallel);

        let multiple = Cli::parse_from(["trust-cg", "one.tmbc", "two.tmbc"]);
        assert!(!build_config_for_input_count(&multiple, 2).parallel);

        let explicit_serial = Cli::parse_from(["trust-cg", "--no-parallel", "one.tmbc"]);
        assert!(!build_config_for_input_count(&explicit_serial, 1).parallel);
    }

    #[test]
    fn pgo_cache_key_distinguishes_x86_os_abi_triples() {
        let config = CompilerConfig {
            target: Target::X86_64,
            ..CompilerConfig::default()
        };
        let trust_ir_bytes = b"unit-test-module";
        let windows = parse_target("x86_64-pc-windows-msvc").unwrap();
        let linux = parse_target("x86_64-unknown-linux-gnu").unwrap();

        let windows_key = pgo_cache_key(trust_ir_bytes, &config, windows);
        let linux_key = pgo_cache_key(trust_ir_bytes, &config, linux);

        assert_eq!(windows_key.target_triple(), "x86_64-pc-windows-msvc");
        assert_eq!(linux_key.target_triple(), "x86_64-unknown-linux-gnu");
        assert_ne!(windows_key, linux_key);
    }

    #[test]
    fn canonical_compiler_config_records_requested_target_spec() {
        let target_spec = parse_target("x86_64-pc-windows-msvc").unwrap();
        let config = CompilerConfig {
            target: target_spec.architecture,
            ..CompilerConfig::default()
        };
        let bytes = canonical_compiler_config_bytes(&config, target_spec);
        let value: serde_json::Value = serde_json::from_slice(&bytes).unwrap();

        assert_eq!(value["schema"], "trust-cg.compiler_config.v2");
        assert_eq!(value["target"], "x86_64");
        assert_eq!(value["target_triple"], "x86_64-pc-windows-msvc");
        assert_eq!(value["target_os"], "windows");
        assert_eq!(value["target_environment"], "msvc");
    }
}
