// trust-cg-ws2-import — WS2 driver helper.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reads a `.ll` file, imports it to `trust_ir::Module`, and compiles through
// `trust-cg-codegen` to a Mach-O object file.
//
// Contract (consumed by `scripts/run_llvm_test_suite.sh`):
//
//   trust-cg-ws2-import <input.ll> <output.o>
//   trust-cg-ws2-import --target aarch64-apple-darwin --opt-level 2 \
//       --emit-proofs proofs/ <input.ll> <output.o>
//
// Exit codes:
//   0 — object written successfully.
//   1 — importer or codegen error. On `Error::Unsupported(reason)` the
//       first stderr line is `unsupported: <reason>` so the driver can
//       classify the program as `unsupported` rather than `crash`.
//
// 2-pass AOT PGO (env-driven, default OFF — both vars unset leaves the
// compile path byte-identical to a build without this feature):
//
//   GEN:  TCG_PGO_GEN=<base> trust-cg-ws2-import --opt-level O2 a.ll a.o
//         -> instrumented a.o + <base>.sites sidecar (compatibility digest,
//            ordered-site checksum, and one `function\tblock_id` line per
//            counter slot).
//         cc a.o rt/tcg_pgo_rt.c -o bin -lm
//         TCG_PGO_OUT=<base>.raw ./bin ...   (destructor dumps raw LE u64s)
//   USE:  TCG_PGO_USE=<base> trust-cg-ws2-import --opt-level O2 a.ll a.o
//         -> reads <base>.sites + <base>.raw, fails CLOSED on compatibility
//            digest, site checksum, or length mismatch, and compiles with the
//            profile attached
//            (profile-use layout/inline/unroll/vectorize hotness + the
//            profile-gated latch-and-split).
//
// PGO compilation deliberately rejects every other `TCG_*` or `TRUST_CG_*`
// environment override. Those controls can change the generated CFG without
// appearing in `CompilerConfig`; accepting them would let GEN and USE silently
// disagree about the counter map. GEN and USE are supported only for AArch64
// AOT compilation at O2 or O3; every other target/level fails explicitly.

use std::collections::HashSet;
use std::env;
use std::ffi::OsString;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::{Arc, Mutex};

use trust_cg_codegen::compiler::{CompilationResult, Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pgo_runner::pgo_cache_key;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};
use trust_cg_llvm_import::{Error, import_text};
use trust_cg_opt::pgo::{CounterMap, CounterSite, ProfData, build_profdata_from_counters_with_key};

const WS2_APPLE_AARCH64_TARGET: &str = "aarch64-apple-darwin";
const MAX_LLVM_IR_INPUT_BYTES: u64 = 64 * 1024 * 1024;
// AArch64 AOT counter loads/stores use a scaled unsigned 12-bit offset, so
// the backend can address slots 0..=4095 and deliberately rejects larger maps.
const PGO_MAX_COUNTER_SITES: usize = 4096;
// Function names are line-oriented metadata rather than an input payload. A
// 4-KiB ceiling leaves ample room for generated LLVM symbols while preventing
// one corrupt row from dominating memory.
const PGO_MAX_FUNCTION_NAME_BYTES: usize = 4 * 1024;
// Independently cap the complete sidecar. Eight MiB is generous for 4096
// ordinary symbol names while keeping both GEN construction and USE parsing
// predictably bounded even when many names approach the per-name ceiling.
const PGO_MAX_SIDECAR_BYTES: u64 = 8 * 1024 * 1024;

/// Reproducible producer-release and sidecar-schema identity.
///
/// This identifier makes the on-disk contract explicit, binds the published
/// producer version and schema into the compatibility key, and lets readers
/// fail closed on every unknown format. The compatibility key separately binds
/// a stable compatibility digest of the bytes read from the current executable
/// path, because Cargo package metadata alone cannot distinguish locally
/// modified builds with the same version. This digest is not authentication.
const PGO_SIDECAR_FORMAT_ID: &str = concat!(
    "trust-cg-ws2-import/",
    env!("CARGO_PKG_VERSION"),
    "/pgo-sites-v3"
);

fn pgo_paths_from_os(
    generate: Option<OsString>,
    profile_use: Option<OsString>,
) -> Result<(Option<String>, Option<String>), String> {
    fn decode(name: &str, value: Option<OsString>) -> Result<Option<String>, String> {
        let Some(value) = value.filter(|value| !value.is_empty()) else {
            return Ok(None);
        };
        value
            .into_string()
            .map(Some)
            .map_err(|_| format!("{name} path is not valid UTF-8"))
    }

    let generate = decode("TCG_PGO_GEN", generate)?;
    let profile_use = decode("TCG_PGO_USE", profile_use)?;
    if generate.is_some() && profile_use.is_some() {
        return Err("set at most one of TCG_PGO_GEN / TCG_PGO_USE".to_owned());
    }
    Ok((generate, profile_use))
}

fn validate_pgo_compile_environment<I>(variables: I) -> Result<(), String>
where
    I: IntoIterator<Item = (OsString, OsString)>,
{
    let mut forbidden = variables
        .into_iter()
        .filter_map(|(name, _)| {
            let name = name.to_string_lossy();
            let is_trust_cg_control = name.starts_with("TCG_") || name.starts_with("TRUST_CG_");
            let is_pgo_mode = name == "TCG_PGO_GEN" || name == "TCG_PGO_USE";
            (is_trust_cg_control && !is_pgo_mode).then(|| name.into_owned())
        })
        .collect::<Vec<_>>();
    forbidden.sort_unstable();
    forbidden.dedup();

    if forbidden.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "PGO compilation requires default Trust-CG controls; unset: {}",
            forbidden.join(", ")
        ))
    }
}

fn validate_pgo_target_and_opt_level(
    target_spec: TargetSpec,
    opt_level: OptLevel,
) -> Result<(), String> {
    if target_spec.architecture != Target::Aarch64
        || !matches!(opt_level, OptLevel::O2 | OptLevel::O3)
    {
        return Err(format!(
            "profile generation and use require an AArch64 target at O2 or O3; \
             got target `{}` (architecture {}) at {}",
            target_spec.triple(),
            target_spec.architecture.name(),
            opt_level_name(opt_level)
        ));
    }
    Ok(())
}

fn current_executable_digest() -> Result<u128, String> {
    let executable = env::current_exe()
        .map_err(|error| format!("locating the producer executable path: {error}"))?;
    let bytes = fs::read(&executable).map_err(|error| {
        format!(
            "reading bytes at producer executable path '{}': {error}",
            executable.display()
        )
    })?;
    Ok(trust_cg_opt::stable_hash(&bytes))
}

fn pgo_key_material(
    input: &[u8],
    config: &CompilerConfig,
    producer_executable_digest: u128,
) -> Vec<u8> {
    let producer_identity = format!("producer-executable={producer_executable_digest:032x}");
    let cegis_budget = config
        .cegis_superopt_budget_sec
        .map_or_else(|| "none".to_owned(), |seconds| seconds.to_string());
    let config_identity = format!("cegis-superopt-budget-sec={cegis_budget}");
    let mut keyed = Vec::with_capacity(
        PGO_SIDECAR_FORMAT_ID.len()
            + producer_identity.len()
            + config_identity.len()
            + 3
            + input.len(),
    );
    keyed.extend_from_slice(PGO_SIDECAR_FORMAT_ID.as_bytes());
    keyed.push(0);
    keyed.extend_from_slice(producer_identity.as_bytes());
    keyed.push(0);
    keyed.extend_from_slice(config_identity.as_bytes());
    keyed.push(0);
    keyed.extend_from_slice(input);
    keyed
}

fn pgo_compatibility_key(
    input: &[u8],
    config: &CompilerConfig,
    target_spec: TargetSpec,
    producer_executable_digest: u128,
) -> trust_cg_opt::CacheKey {
    pgo_cache_key(
        &pgo_key_material(input, config, producer_executable_digest),
        config,
        target_spec,
    )
}

fn read_bytes_with_limit<R: Read>(reader: R, limit: u64) -> std::io::Result<(Vec<u8>, bool)> {
    let bounded_limit = limit.saturating_add(1);
    let initial_capacity = usize::try_from(bounded_limit.min(64 * 1024)).unwrap_or(64 * 1024);
    let mut bytes = Vec::with_capacity(initial_capacity);
    reader.take(bounded_limit).read_to_end(&mut bytes)?;
    let exceeded = bytes.len() as u64 > limit;
    Ok((bytes, exceeded))
}

fn read_and_import_module(path: &Path) -> Result<(String, trust_ir::Module), Error> {
    let input = fs::File::open(path)?;
    let (bytes, exceeded) = read_bytes_with_limit(input, MAX_LLVM_IR_INPUT_BYTES)?;
    if exceeded {
        return Err(Error::Unsupported(format!(
            "LLVM IR input '{}' exceeds importer limit {} while reading",
            path.display(),
            MAX_LLVM_IR_INPUT_BYTES
        )));
    }
    let text = String::from_utf8(bytes)
        .map_err(|error| Error::Io(std::io::Error::new(std::io::ErrorKind::InvalidData, error)))?;
    let module_name = path
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or("module");
    let module = import_text(&text, module_name)?;
    Ok((text, module))
}

fn main() -> ExitCode {
    let argv: Vec<String> = env::args().collect();
    let args = match parse_args(&argv) {
        Ok(ParseOutcome::Help) => {
            eprintln!(
                "{}",
                usage(argv.first().map_or("trust-cg-ws2-import", String::as_str))
            );
            return ExitCode::SUCCESS;
        }
        Ok(ParseOutcome::Run(args)) => args,
        Err(message) => {
            eprintln!("{message}");
            eprintln!(
                "{}",
                usage(argv.first().map_or("trust-cg-ws2-import", String::as_str))
            );
            return ExitCode::from(1);
        }
    };

    // PGO is deliberately a narrow, fail-closed AArch64 AOT mode. Validate
    // its controls before parsing or compiling the input so unsupported
    // target/optimization combinations cannot silently take the normal path.
    let (pgo_gen, pgo_use) =
        match pgo_paths_from_os(env::var_os("TCG_PGO_GEN"), env::var_os("TCG_PGO_USE")) {
            Ok(paths) => paths,
            Err(message) => {
                eprintln!("pgo: {message}");
                return ExitCode::from(1);
            }
        };
    let pgo_active = pgo_gen.is_some() || pgo_use.is_some();
    if pgo_active {
        if let Err(message) = validate_pgo_target_and_opt_level(args.target_spec, args.opt_level) {
            eprintln!("pgo: {message}");
            return ExitCode::from(1);
        }
        if let Err(message) = validate_pgo_compile_environment(env::vars_os()) {
            eprintln!("pgo: {message}");
            return ExitCode::from(1);
        }
    }

    let (input, module) = match read_and_import_module(&args.input) {
        Ok(imported) => imported,
        Err(Error::Unsupported(reason)) => {
            // Agreed prefix with scripts/run_llvm_test_suite.sh.
            eprintln!("unsupported: {reason}");
            return ExitCode::from(1);
        }
        Err(Error::Parse { line, message }) => {
            eprintln!("parse: line {line}: {message}");
            return ExitCode::from(1);
        }
        Err(Error::Io(e)) => {
            eprintln!("io: {e}");
            return ExitCode::from(1);
        }
    };

    // O0 matches clang -O0 on the reference side. Target is AArch64
    // because that's the fully functional backend on the host (Apple
    // Silicon). The supported target boundary is stated in LIMITATIONS.md.
    let cfg = CompilerConfig {
        opt_level: args.opt_level,
        target: args.target_spec.architecture,
        emit_proofs: false,
        trace_level: CompilerTraceLevel::None,
        emit_debug: false,
        parallel: false,
        cegis_superopt_budget_sec: args.cegis_superopt_budget_sec,
        enable_fsym_trust_ir_preflight: false,
        // AOT driver: the JIT knobs are irrelevant; match CompilerConfig's
        // conservative defaults (no fast regalloc, no validation override).
        enable_jit_fast_regalloc: false,
        jit_validation_mode_override: None,
        panic_unwind: false,
    };
    // 2-pass AOT PGO wiring (env-driven; both unset = today's exact path).
    let pgo_producer_digest = if pgo_active {
        match current_executable_digest() {
            Ok(digest) => Some(digest),
            Err(message) => {
                eprintln!("pgo: {message}");
                return ExitCode::from(1);
            }
        }
    } else {
        None
    };
    let pgo_key = if pgo_active {
        Some(pgo_compatibility_key(
            input.as_bytes(),
            &cfg,
            args.target_spec,
            pgo_producer_digest.expect("PGO producer digest computed for active mode"),
        ))
    } else {
        None
    };
    drop(input);

    let mut compiler = Compiler::new_for_target_spec(cfg.clone(), args.target_spec);
    let mut gen_sink: Option<Arc<Mutex<CounterMap>>> = None;
    if pgo_gen.is_some() {
        let sink = Arc::new(Mutex::new(CounterMap::new()));
        compiler = compiler.with_profile_generate(sink.clone());
        gen_sink = Some(sink);
    }
    if let Some(base) = &pgo_use {
        let key = pgo_key.as_ref().expect("pgo key computed for USE mode");
        match load_pgo_profile(base, key) {
            Ok(profile) => compiler = compiler.with_profile_use(profile),
            Err(message) => {
                eprintln!("pgo: {message}");
                return ExitCode::from(1);
            }
        }
    }

    let result = match compiler.compile(&module) {
        Ok(r) => r,
        Err(e) => {
            // The driver catalogues these as `unsupported` too — the
            // importer admitted the program but the codegen pipeline
            // could not finish lowering something. That's a truthful
            // signal ("we don't support this yet"), not a crash.
            eprintln!("unsupported: codegen: {e}");
            return ExitCode::from(1);
        }
    };

    if let Err(e) = fs::write(&args.output, &result.object_code) {
        eprintln!("io: writing {}: {}", args.output.display(), e);
        return ExitCode::from(1);
    }

    if let (Some(base), Some(sink)) = (&pgo_gen, &gen_sink) {
        let key = pgo_key.as_ref().expect("pgo key computed for GEN mode");
        if let Err(message) = write_pgo_sites(base, key, sink) {
            eprintln!("pgo: {message}");
            return ExitCode::from(1);
        }
    }

    if let Some(report_path) = args.proof_report_path()
        && let Err(e) = write_proof_report(&report_path, &args, &cfg, &result, &argv)
    {
        eprintln!("io: writing proof report {}: {}", report_path.display(), e);
        return ExitCode::from(1);
    }

    ExitCode::SUCCESS
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DriverArgs {
    input: PathBuf,
    output: PathBuf,
    opt_level: OptLevel,
    target_spec: TargetSpec,
    proof_destination: Option<ProofDestination>,
    cegis_superopt_budget_sec: Option<u64>,
}

impl DriverArgs {
    fn proof_report_path(&self) -> Option<PathBuf> {
        self.proof_destination
            .as_ref()
            .map(|destination| match destination {
                ProofDestination::ReportFile(path) => path.clone(),
                ProofDestination::ReportDirectory(path) => path.join("proof-report.json"),
            })
    }

    fn proof_destination_path(&self) -> Option<&Path> {
        self.proof_destination
            .as_ref()
            .map(|destination| match destination {
                ProofDestination::ReportFile(path) | ProofDestination::ReportDirectory(path) => {
                    path.as_path()
                }
            })
    }

    fn proof_destination_kind(&self) -> Option<&'static str> {
        self.proof_destination
            .as_ref()
            .map(|destination| match destination {
                ProofDestination::ReportFile(_) => "structured-report-file",
                ProofDestination::ReportDirectory(_) => "structured-report-directory",
            })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ProofDestination {
    ReportFile(PathBuf),
    ReportDirectory(PathBuf),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ParseOutcome {
    Help,
    Run(DriverArgs),
}

fn usage(program: &str) -> String {
    format!(
        "usage: {program} [--opt-level <0|1|2|3|O0|O1|O2|O3>] [--target <triple>] [--cegis-superopt <secs>] [--proof-report <file>|--emit-proofs <dir>] <input.ll> <output.o>"
    )
}

fn parse_args(argv: &[String]) -> Result<ParseOutcome, String> {
    let mut opt_level = OptLevel::O0;
    let mut target_spec = default_target_spec();
    let mut proof_destination = None;
    let mut cegis_superopt_budget_sec = None;
    let mut positionals = Vec::new();

    let mut index = 1;
    while index < argv.len() {
        let arg = &argv[index];
        match arg.as_str() {
            "-h" | "--help" => return Ok(ParseOutcome::Help),
            "--" => {
                positionals.extend(argv[index + 1..].iter().map(PathBuf::from));
                break;
            }
            "--opt-level" => {
                index += 1;
                let value = argv
                    .get(index)
                    .ok_or_else(|| "--opt-level requires a value".to_owned())?;
                opt_level = parse_opt_level(value)?;
            }
            "--proof-report" => {
                index += 1;
                let value = argv
                    .get(index)
                    .ok_or_else(|| "--proof-report requires a path".to_owned())?;
                set_proof_destination(
                    &mut proof_destination,
                    ProofDestination::ReportFile(PathBuf::from(value)),
                )?;
            }
            "--target" => {
                index += 1;
                let value = argv
                    .get(index)
                    .ok_or_else(|| "--target requires a value".to_owned())?;
                target_spec = parse_target_spec_flag(value)?;
            }
            "--emit-proofs" => {
                index += 1;
                let value = argv
                    .get(index)
                    .ok_or_else(|| "--emit-proofs requires a directory".to_owned())?;
                set_proof_destination(
                    &mut proof_destination,
                    ProofDestination::ReportDirectory(PathBuf::from(value)),
                )?;
            }
            "--cegis-superopt" => {
                index += 1;
                let value = argv
                    .get(index)
                    .ok_or_else(|| "--cegis-superopt requires a seconds value".to_owned())?;
                cegis_superopt_budget_sec = Some(parse_u64_flag("--cegis-superopt", value)?);
            }
            _ if arg.starts_with("--opt-level=") => {
                opt_level = parse_opt_level(&arg["--opt-level=".len()..])?;
            }
            _ if arg.starts_with("--proof-report=") => {
                set_proof_destination(
                    &mut proof_destination,
                    ProofDestination::ReportFile(PathBuf::from(&arg["--proof-report=".len()..])),
                )?;
            }
            _ if arg.starts_with("--target=") => {
                target_spec = parse_target_spec_flag(&arg["--target=".len()..])?;
            }
            _ if arg.starts_with("--emit-proofs=") => {
                set_proof_destination(
                    &mut proof_destination,
                    ProofDestination::ReportDirectory(PathBuf::from(
                        &arg["--emit-proofs=".len()..],
                    )),
                )?;
            }
            _ if arg.starts_with("--cegis-superopt=") => {
                cegis_superopt_budget_sec = Some(parse_u64_flag(
                    "--cegis-superopt",
                    &arg["--cegis-superopt=".len()..],
                )?);
            }
            _ if arg.starts_with('-') => return Err(format!("unknown option `{arg}`")),
            _ => positionals.push(PathBuf::from(arg)),
        }
        index += 1;
    }

    if positionals.len() != 2 {
        return Err(format!(
            "expected exactly <input.ll> and <output.o>, got {} positional argument(s)",
            positionals.len()
        ));
    }

    Ok(ParseOutcome::Run(DriverArgs {
        input: positionals.remove(0),
        output: positionals.remove(0),
        opt_level,
        target_spec,
        proof_destination,
        cegis_superopt_budget_sec,
    }))
}

fn default_target_spec() -> TargetSpec {
    if cfg!(target_os = "macos") {
        TargetSpec::parse(WS2_APPLE_AARCH64_TARGET)
            .expect("WS2 Apple AArch64 target must be supported")
    } else {
        TargetSpec::unknown_for_architecture(Target::Aarch64)
    }
}

fn set_proof_destination(
    proof_destination: &mut Option<ProofDestination>,
    next: ProofDestination,
) -> Result<(), String> {
    if proof_destination.is_some() {
        return Err("use only one of --proof-report or --emit-proofs".to_owned());
    }
    *proof_destination = Some(next);
    Ok(())
}

fn parse_opt_level(value: &str) -> Result<OptLevel, String> {
    match value {
        "0" | "O0" | "o0" => Ok(OptLevel::O0),
        "1" | "O1" | "o1" => Ok(OptLevel::O1),
        "2" | "O2" | "o2" => Ok(OptLevel::O2),
        "3" | "O3" | "o3" => Ok(OptLevel::O3),
        _ => Err(format!(
            "invalid --opt-level `{value}`; expected 0, 1, 2, 3, O0, O1, O2, or O3"
        )),
    }
}

fn parse_target_spec_flag(value: &str) -> Result<TargetSpec, String> {
    TargetSpec::parse(value).map_err(|err| err.to_string())
}

fn parse_u64_flag(flag: &str, value: &str) -> Result<u64, String> {
    value
        .parse()
        .map_err(|_| format!("{flag} requires an unsigned integer, got `{value}`"))
}

fn opt_level_name(opt_level: OptLevel) -> &'static str {
    match opt_level {
        OptLevel::O0 => "O0",
        OptLevel::O1 => "O1",
        OptLevel::O2 => "O2",
        OptLevel::O3 => "O3",
    }
}

fn is_lower_hex_u128(value: &str) -> bool {
    value.len() == 32
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn site_map_checksum(site_rows: &str) -> u128 {
    trust_cg_opt::stable_hash(site_rows.as_bytes())
}

/// Write the GEN-mode `<base>.sites` sidecar: line 1 is the explicit
/// producer/format identity, line 2 is the 32-hex-char profile compatibility
/// digest, line 3 is a stable-hash checksum of the exact canonical ordered site
/// rows, then one `function\tblock_id` row per counter slot.
///
/// The site-map checksum detects accidental corruption and incompatible row
/// ordering. It is a compatibility check, not authentication.
fn write_pgo_sites(
    base: &str,
    key: &trust_cg_opt::CacheKey,
    sink: &Arc<Mutex<CounterMap>>,
) -> Result<(), String> {
    let sites_path = format!("{base}.sites");
    let guard = match sink.lock() {
        Ok(guard) => guard,
        Err(poisoned) => poisoned.into_inner(),
    };
    if guard.sites.len() > PGO_MAX_COUNTER_SITES {
        return Err(format!(
            "{sites_path}: {} counter sites exceed the AArch64 AOT limit of \
             {PGO_MAX_COUNTER_SITES}",
            guard.sites.len()
        ));
    }
    let mut site_rows = String::with_capacity(guard.sites.len() * 24);
    let mut seen_sites = HashSet::new();
    for (index, site) in guard.sites.iter().enumerate() {
        let expected_index = u32::try_from(index).map_err(|_| {
            format!("{sites_path}: counter site {index} exceeds the representable u32 index range")
        })?;
        if site.counter_index != expected_index {
            return Err(format!(
                "{sites_path}: counter site {index} (`{}` block {}) has index {}, \
                 expected dense index {expected_index}",
                site.function, site.block_id, site.counter_index
            ));
        }
        if site.function.len() > PGO_MAX_FUNCTION_NAME_BYTES {
            return Err(format!(
                "{sites_path}: counter site {index} has a {}-byte function name, over the \
                 {PGO_MAX_FUNCTION_NAME_BYTES}-byte sidecar limit",
                site.function.len()
            ));
        }
        if site.function.is_empty() || site.function.chars().any(char::is_control) {
            return Err(format!(
                "{sites_path}: counter site {index} has a function name that cannot be represented \
                 in the line-oriented sidecar format"
            ));
        }
        if !seen_sites.insert((site.function.as_str(), site.block_id)) {
            return Err(format!(
                "{sites_path}: counter site {index} duplicates `{}` block {}",
                site.function, site.block_id
            ));
        }
        site_rows.push_str(&site.function);
        site_rows.push('\t');
        site_rows.push_str(&site.block_id.to_string());
        site_rows.push('\n');
    }

    let header_bytes = PGO_SIDECAR_FORMAT_ID
        .len()
        .checked_add(1 + 32 + 1 + 32 + 1)
        .ok_or_else(|| format!("{sites_path}: sidecar length overflow"))?;
    let sidecar_bytes = header_bytes
        .checked_add(site_rows.len())
        .ok_or_else(|| format!("{sites_path}: sidecar length overflow"))?;
    if sidecar_bytes as u64 > PGO_MAX_SIDECAR_BYTES {
        return Err(format!(
            "{sites_path}: {sidecar_bytes} bytes exceed the {PGO_MAX_SIDECAR_BYTES}-byte \
             sidecar limit"
        ));
    }

    let mut out = String::with_capacity(sidecar_bytes);
    out.push_str(PGO_SIDECAR_FORMAT_ID);
    out.push('\n');
    out.push_str(&format!("{:032x}\n", key.digest()));
    out.push_str(&format!("{:032x}\n", site_map_checksum(&site_rows)));
    out.push_str(&site_rows);
    debug_assert_eq!(out.len(), sidecar_bytes);
    fs::write(&sites_path, out).map_err(|e| format!("writing {sites_path}: {e}"))?;
    eprintln!(
        "pgo: wrote {} counter site(s) to {sites_path}",
        guard.sites.len()
    );
    Ok(())
}

/// Load `<base>.sites` + `<base>.raw` for USE mode and build the `ProfData`.
///
/// FAIL-CLOSED checks, in order:
///  1. `.sites` producer/format identity must be exactly the supported
///     published package version and sidecar schema.
///  2. `.sites` digest must equal the recomputed compatibility digest (same
///     imported `.ll` bytes, opt level, CEGIS budget, triple, cpu, features,
///     producer-executable compatibility digest, published producer release,
///     and sidecar schema).
///  3. `.sites` ordered rows must match their stable-hash checksum. This
///     detects accidental corruption or incompatible ordering; it does not
///     authenticate a profile.
///  4. `.raw` must decode to EXACTLY one u64 per `.sites` row — a short file
///     (abnormal canary exit skipped the dump destructor) or a stale pairing
///     with a different length is rejected, never partially applied. The
///     current naked-u64 raw format cannot authenticate a wrong same-length
///     file, so callers must manage each base-name artifact pair atomically.
fn load_pgo_profile(base: &str, key: &trust_cg_opt::CacheKey) -> Result<ProfData, String> {
    let sites_path = format!("{base}.sites");
    let raw_path = format!("{base}.raw");

    let sites_file =
        fs::File::open(&sites_path).map_err(|error| format!("reading {sites_path}: {error}"))?;
    let (sites_bytes, exceeded) = read_bytes_with_limit(sites_file, PGO_MAX_SIDECAR_BYTES)
        .map_err(|error| format!("reading {sites_path}: {error}"))?;
    if exceeded {
        return Err(format!(
            "{sites_path}: exceeds the {PGO_MAX_SIDECAR_BYTES}-byte sidecar limit"
        ));
    }
    let sites_text = String::from_utf8(sites_bytes)
        .map_err(|error| format!("{sites_path}: sidecar is not valid UTF-8: {error}"))?;
    if sites_text.is_empty() {
        return Err(format!("{sites_path}: empty sites file"));
    }

    let mut header_and_rows = sites_text.splitn(4, '\n');
    let format_id = header_and_rows
        .next()
        .expect("a non-empty string has a first split segment");
    if format_id != PGO_SIDECAR_FORMAT_ID {
        return Err(format!(
            "{sites_path}: unsupported sites format; expected `{PGO_SIDECAR_FORMAT_ID}`"
        ));
    }
    let digest = header_and_rows
        .next()
        .filter(|digest| !digest.is_empty())
        .ok_or_else(|| format!("{sites_path}: missing profile digest"))?;
    if !is_lower_hex_u128(digest) {
        return Err(format!(
            "{sites_path}:2: malformed profile digest; expected 32 lowercase hex characters"
        ));
    }
    let checksum = header_and_rows
        .next()
        .filter(|checksum| !checksum.is_empty())
        .ok_or_else(|| format!("{sites_path}: missing site-map checksum"))?;
    if !is_lower_hex_u128(checksum) {
        return Err(format!(
            "{sites_path}:3: malformed site-map checksum; expected 32 lowercase hex characters"
        ));
    }
    let site_rows = header_and_rows.next().ok_or_else(|| {
        format!("{sites_path}: missing newline after the site-map checksum header")
    })?;

    let expected = format!("{:032x}", key.digest());
    if digest != expected {
        return Err(format!(
            "{sites_path}: incompatible profile key (digest {digest} != expected {expected}); \
             re-run the TCG_PGO_GEN compile + canary with these imported input bytes, \
             the matching producer executable compatibility digest, published \
             producer release, and keyed target/optimization settings"
        ));
    }

    let expected_checksum = format!("{:032x}", site_map_checksum(site_rows));
    if checksum != expected_checksum {
        return Err(format!(
            "{sites_path}: corrupt or incompatible site map (checksum {checksum} != \
             expected {expected_checksum})"
        ));
    }
    if !site_rows.is_empty() && !site_rows.ends_with('\n') {
        return Err(format!(
            "{sites_path}: site rows are not canonical: final row lacks a newline"
        ));
    }

    let mut map = CounterMap::new();
    let mut seen_sites = HashSet::new();
    let canonical_rows = site_rows.strip_suffix('\n').unwrap_or(site_rows);
    for (index, line) in (!canonical_rows.is_empty())
        .then_some(canonical_rows)
        .into_iter()
        .flat_map(|rows| rows.split('\n'))
        .enumerate()
    {
        let line_number = index + 4;
        if index >= PGO_MAX_COUNTER_SITES {
            return Err(format!(
                "{sites_path}:{line_number}: more than {PGO_MAX_COUNTER_SITES} counter sites"
            ));
        }
        let (function, block) = line
            .split_once('\t')
            .ok_or_else(|| format!("{sites_path}:{line_number}: malformed site line"))?;
        if function.is_empty() {
            return Err(format!(
                "{sites_path}:{line_number}: malformed site line: empty function name"
            ));
        }
        if function.len() > PGO_MAX_FUNCTION_NAME_BYTES {
            return Err(format!(
                "{sites_path}:{line_number}: function name is {} bytes, over the \
                 {PGO_MAX_FUNCTION_NAME_BYTES}-byte sidecar limit",
                function.len()
            ));
        }
        if function.chars().any(char::is_control) {
            return Err(format!(
                "{sites_path}:{line_number}: malformed site line: \
                 function name contains a control character"
            ));
        }
        let block_id: u32 = block
            .parse()
            .map_err(|_| format!("{sites_path}:{line_number}: malformed block id `{block}`"))?;
        let canonical_block = block_id.to_string();
        if block != canonical_block {
            return Err(format!(
                "{sites_path}:{line_number}: non-canonical block id `{block}`; \
                 expected `{canonical_block}`"
            ));
        }
        if !seen_sites.insert((function.to_owned(), block_id)) {
            return Err(format!(
                "{sites_path}:{line_number}: duplicate site `{function}` block {block_id}"
            ));
        }
        let counter_index = u32::try_from(index).map_err(|_| {
            format!("{sites_path}:{line_number}: site index exceeds the representable u32 range")
        })?;
        map.sites.push(CounterSite {
            function: function.to_string(),
            block_id,
            counter_index,
            symbol: String::new(),
        });
    }

    let expected_raw_len = map
        .sites
        .len()
        .checked_mul(std::mem::size_of::<u64>())
        .ok_or_else(|| format!("{sites_path}: counter byte length overflow"))?;
    let read_limit = expected_raw_len
        .checked_add(1)
        .ok_or_else(|| format!("{sites_path}: counter read limit overflow"))?;
    let raw_file = fs::File::open(&raw_path).map_err(|e| format!("reading {raw_path}: {e}"))?;
    let raw_metadata = raw_file
        .metadata()
        .map_err(|e| format!("reading {raw_path}: {e}"))?;
    if raw_metadata.len() != expected_raw_len as u64 {
        return Err(format!(
            "{raw_path}: {} byte(s) but {sites_path} lists {} site(s) (expected {} bytes); \
             the profile artifacts are incomplete or do not belong together",
            raw_metadata.len(),
            map.sites.len(),
            expected_raw_len
        ));
    }
    let mut raw = Vec::with_capacity(expected_raw_len);
    raw_file
        .take(read_limit as u64)
        .read_to_end(&mut raw)
        .map_err(|e| format!("reading {raw_path}: {e}"))?;
    if raw.len() != expected_raw_len {
        return Err(format!(
            "{raw_path}: {} byte(s) but {sites_path} lists {} site(s) (expected {} bytes); \
             the profile artifacts are incomplete or do not belong together",
            raw.len(),
            map.sites.len(),
            expected_raw_len
        ));
    }
    let counters: Vec<u64> = raw
        .chunks_exact(8)
        .map(|chunk| u64::from_le_bytes(chunk.try_into().expect("chunks_exact(8)")))
        .collect();

    Ok(build_profdata_from_counters_with_key(key, &map, &counters))
}

fn write_proof_report(
    report_path: &Path,
    args: &DriverArgs,
    config: &CompilerConfig,
    result: &CompilationResult,
    argv: &[String],
) -> std::io::Result<()> {
    if let Some(parent) = report_path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::create_dir_all(parent)?;
    }
    let report = proof_report_json_value(args, config, result, argv);
    fs::write(
        report_path,
        serde_json::to_string_pretty(&report).expect("proof report JSON must serialize") + "\n",
    )
}

fn proof_report_json_value(
    args: &DriverArgs,
    config: &CompilerConfig,
    result: &CompilationResult,
    argv: &[String],
) -> serde_json::Value {
    let proof_optimizations = result.metrics.proof_optimizations;
    let proof_report_path = args.proof_report_path();
    let proof_certificates = result.proofs.as_ref().map(|proofs| {
        let verified = proofs.iter().filter(|proof| proof.verified).count();
        serde_json::json!({
            "certificate_count": proofs.len(),
            "verified_count": verified,
            "unverified_count": proofs.len().saturating_sub(verified),
        })
    });
    let proof_optimization_certificates: Vec<_> = result
        .proof_optimization_certificates
        .iter()
        .map(|certificate| certificate.to_json_value())
        .collect();

    serde_json::json!({
        "schema": "trust-cg.ws2_import.proof_report.v1",
        "schema_version": 1,
        "producer": "trust-cg-ws2-import",
        "provenance": {
            "argv": argv,
            "current_dir": env::current_dir()
                .ok()
                .map(|path| path.display().to_string()),
            "input_path": args.input.display().to_string(),
            "object_path": args.output.display().to_string(),
            "proof_destination_kind": args.proof_destination_kind(),
            "proof_destination_path": args
                .proof_destination_path()
                .map(|path| path.display().to_string()),
            "proof_report_path": proof_report_path
                .as_ref()
                .map(|path| path.display().to_string()),
        },
        "compiler_config": {
            "opt_level": opt_level_name(config.opt_level),
            "target": config.target.name(),
            "target_triple": args.target_spec.triple(),
            "emit_proofs": config.emit_proofs,
            "emit_debug": config.emit_debug,
            "parallel": config.parallel,
            "cegis_superopt_budget_sec": config.cegis_superopt_budget_sec,
            "enable_fsym_trust_ir_preflight": config.enable_fsym_trust_ir_preflight,
        },
        "object": {
            "path": args.output.display().to_string(),
            "bytes": result.object_code.len(),
            "machine_code_bytes": result.metrics.code_size_bytes,
            "static_instruction_count": result.metrics.instruction_count,
            "function_count": result.metrics.function_count,
            "optimization_passes_run": result.metrics.optimization_passes_run,
        },
        "proof_optimizations": {
            "certificate_count": proof_optimizations.certificate_count,
            "applied_count": proof_optimizations.applied_count,
            "rejected_count": proof_optimizations.rejected_count,
            "guard_eliminated_count": proof_optimizations.guard_eliminated_count,
            "guard_rejected_count": proof_optimizations.guard_rejected_count,
            "non_zero_divisor_guard_eliminated_count": proof_optimizations.non_zero_divisor_guard_eliminated_count,
            "valid_shift_guard_eliminated_count": proof_optimizations.valid_shift_guard_eliminated_count,
            "non_zero_divisor_guard_rejected_count": proof_optimizations.non_zero_divisor_guard_rejected_count,
            "valid_shift_guard_rejected_count": proof_optimizations.valid_shift_guard_rejected_count,
            "certificates": proof_optimization_certificates,
        },
        "lowering_proofs": proof_certificates,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};
    use trust_cg_codegen::compiler::{
        CompilationMetrics, FsymTrustIrMetrics, ProofOptimizationMetrics,
    };
    use trust_cg_codegen::pipeline::{
        ProofOptimizationCertificateCitation, ProofOptimizationConsumedFactCitation,
    };

    static NEXT_PGO_TEST_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    struct TestPgoFiles {
        directory: PathBuf,
        base: PathBuf,
    }

    impl TestPgoFiles {
        fn new(label: &str) -> Self {
            let sequence = NEXT_PGO_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed);
            let timestamp = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("test clock must be after the Unix epoch")
                .as_nanos();
            let directory = env::temp_dir().join(format!(
                "trust-cg-ws2-import-pgo-{label}-{}-{timestamp}-{sequence}",
                std::process::id()
            ));
            fs::create_dir(&directory).expect("create isolated PGO sidecar test directory");
            let base = directory.join("profile");
            Self { directory, base }
        }

        fn base(&self) -> &str {
            self.base
                .to_str()
                .expect("constructed PGO test path must be valid UTF-8")
        }

        fn sites_path(&self) -> PathBuf {
            PathBuf::from(format!("{}.sites", self.base()))
        }

        fn raw_path(&self) -> PathBuf {
            PathBuf::from(format!("{}.raw", self.base()))
        }
    }

    impl Drop for TestPgoFiles {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.directory);
        }
    }

    fn test_pgo_key(module_hash: u128) -> trust_cg_opt::CacheKey {
        trust_cg_opt::CacheKey::new(
            module_hash,
            2,
            WS2_APPLE_AARCH64_TARGET.to_owned(),
            "apple-m1".to_owned(),
            vec!["+neon".to_owned()],
        )
    }

    fn test_counter_map() -> CounterMap {
        CounterMap {
            sites: vec![
                CounterSite {
                    function: "hot".to_owned(),
                    block_id: 0,
                    counter_index: 0,
                    symbol: String::new(),
                },
                CounterSite {
                    function: "hot".to_owned(),
                    block_id: 7,
                    counter_index: 1,
                    symbol: String::new(),
                },
                CounterSite {
                    function: "cold".to_owned(),
                    block_id: 0,
                    counter_index: 2,
                    symbol: String::new(),
                },
            ],
        }
    }

    fn write_raw_counters(path: &Path, counters: &[u64]) {
        let bytes: Vec<u8> = counters
            .iter()
            .flat_map(|counter| counter.to_le_bytes())
            .collect();
        fs::write(path, bytes).expect("write PGO raw counter fixture");
    }

    fn sites_fixture(key: &trust_cg_opt::CacheKey, site_lines: &str) -> String {
        format!(
            "{PGO_SIDECAR_FORMAT_ID}\n{:032x}\n{:032x}\n{site_lines}",
            key.digest(),
            site_map_checksum(site_lines)
        )
    }

    fn argv(args: &[&str]) -> Vec<String> {
        args.iter().map(|arg| (*arg).to_owned()).collect()
    }

    fn test_config(opt_level: OptLevel, cegis_budget: Option<u64>) -> CompilerConfig {
        CompilerConfig {
            opt_level,
            target: Target::Aarch64,
            emit_proofs: false,
            trace_level: CompilerTraceLevel::None,
            emit_debug: false,
            parallel: false,
            cegis_superopt_budget_sec: cegis_budget,
            enable_fsym_trust_ir_preflight: false,
            enable_jit_fast_regalloc: false,
            jit_validation_mode_override: None,
            panic_unwind: false,
        }
    }

    #[test]
    fn pgo_key_material_binds_the_published_format_identity() {
        let input = b"define i64 @answer() { ret i64 42 }\n";
        let config = test_config(OptLevel::O2, None);
        let producer_digest = 0x1234_5678_9abc_def0_0123_4567_89ab_cdef;
        let material = pgo_key_material(input, &config, producer_digest);
        let identity_len = PGO_SIDECAR_FORMAT_ID.len() + 1;
        let producer_len = "producer-executable=123456789abcdef00123456789abcdef".len() + 1;
        let config_len = "cegis-superopt-budget-sec=none".len() + 1;
        let (identity, remainder) = material.split_at(identity_len);
        let (producer_identity, remainder) = remainder.split_at(producer_len);
        let (config_identity, source) = remainder.split_at(config_len);

        assert_eq!(
            identity,
            format!("{PGO_SIDECAR_FORMAT_ID}\0").as_bytes(),
            "the package-version/schema identity must be a delimited key prefix"
        );
        assert_eq!(
            producer_identity,
            b"producer-executable=123456789abcdef00123456789abcdef\0"
        );
        assert_eq!(config_identity, b"cegis-superopt-budget-sec=none\0");
        assert_eq!(source, input);
        assert!(PGO_SIDECAR_FORMAT_ID.ends_with("/pgo-sites-v3"));
        assert!(PGO_SIDECAR_FORMAT_ID.contains(env!("CARGO_PKG_VERSION")));

        let bound = pgo_compatibility_key(input, &config, default_target_spec(), producer_digest);
        let unbound = pgo_cache_key(input, &config, default_target_spec());
        assert_ne!(
            bound.digest(),
            unbound.digest(),
            "the sidecar identity must affect profile compatibility"
        );

        let with_cegis = test_config(OptLevel::O2, Some(7));
        assert_ne!(
            bound.digest(),
            pgo_compatibility_key(input, &with_cegis, default_target_spec(), producer_digest)
                .digest(),
            "the CEGIS budget changes compilation and must affect profile compatibility"
        );
        assert_ne!(
            bound.digest(),
            pgo_compatibility_key(input, &config, default_target_spec(), producer_digest ^ 1)
                .digest(),
            "the producer-executable compatibility digest must affect profile compatibility"
        );
    }

    #[test]
    fn pgo_environment_allows_only_mode_variables() {
        let allowed = vec![
            (OsString::from("PATH"), OsString::from("/bin")),
            (OsString::from("TCG_PGO_GEN"), OsString::from("profile")),
            (OsString::from("TCG_PGO_USE"), OsString::new()),
        ];
        assert_eq!(validate_pgo_compile_environment(allowed), Ok(()));

        let forbidden = vec![
            (
                OsString::from("TRUST_CG_DISABLE_PASSES"),
                OsString::from("licm"),
            ),
            (OsString::from("TCG_NO_INLINE"), OsString::from("1")),
            (OsString::from("TCG_PGO_OUT"), OsString::from("profile.raw")),
            (OsString::from("TCG_NO_INLINE"), OsString::new()),
        ];
        let error = validate_pgo_compile_environment(forbidden)
            .expect_err("all non-mode Trust-CG controls must fail closed during PGO");
        assert_eq!(
            error,
            "PGO compilation requires default Trust-CG controls; unset: \
             TCG_NO_INLINE, TCG_PGO_OUT, TRUST_CG_DISABLE_PASSES"
        );
    }

    #[test]
    fn pgo_target_and_opt_level_validation_matches_backend_support() {
        let aarch64 = TargetSpec::unknown_for_architecture(Target::Aarch64);
        assert_eq!(
            validate_pgo_target_and_opt_level(aarch64, OptLevel::O2),
            Ok(())
        );
        assert_eq!(
            validate_pgo_target_and_opt_level(aarch64, OptLevel::O3),
            Ok(())
        );

        for opt_level in [OptLevel::O0, OptLevel::O1] {
            let error = validate_pgo_target_and_opt_level(aarch64, opt_level)
                .expect_err("PGO must reject optimization levels without PGO lowering");
            assert_eq!(
                error,
                format!(
                    "profile generation and use require an AArch64 target at O2 or O3; \
                     got target `aarch64-unknown-unknown` (architecture aarch64) at {}",
                    opt_level_name(opt_level)
                )
            );
        }

        for target in [Target::X86_64, Target::Riscv64] {
            let target_spec = TargetSpec::unknown_for_architecture(target);
            let error = validate_pgo_target_and_opt_level(target_spec, OptLevel::O2)
                .expect_err("PGO must reject targets without AOT counter lowering");
            assert_eq!(
                error,
                format!(
                    "profile generation and use require an AArch64 target at O2 or O3; \
                     got target `{}` (architecture {}) at O2",
                    target_spec.triple(),
                    target.name()
                )
            );
        }
    }

    #[test]
    fn bounded_byte_read_stops_at_limit_plus_one() {
        let (bytes, exceeded) = read_bytes_with_limit(std::io::Cursor::new(b"abcdefghijk"), 4)
            .expect("bounded byte read");
        assert_eq!(bytes, b"abcde");
        assert!(exceeded);

        let (bytes, exceeded) =
            read_bytes_with_limit(std::io::Cursor::new(b"abcd"), 4).expect("exact-limit byte read");
        assert_eq!(bytes, b"abcd");
        assert!(!exceeded);
    }

    #[test]
    fn bounded_byte_read_reports_limit_before_invalid_utf8_at_limit_plus_one() {
        let input = [b'a', b'b', b'c', b'd', 0xff, b'e'];
        let (bytes, exceeded) =
            read_bytes_with_limit(std::io::Cursor::new(input), 4).expect("bounded byte read");
        assert_eq!(bytes, [b'a', b'b', b'c', b'd', 0xff]);
        assert!(exceeded);
    }

    #[test]
    fn pgo_path_parsing_treats_empty_as_unset_and_rejects_both_modes() {
        assert_eq!(pgo_paths_from_os(None, None), Ok((None, None)));
        assert_eq!(
            pgo_paths_from_os(Some(OsString::new()), Some(OsString::new())),
            Ok((None, None))
        );
        assert_eq!(
            pgo_paths_from_os(Some(OsString::from("gen")), None),
            Ok((Some("gen".to_owned()), None))
        );

        let error = pgo_paths_from_os(
            Some(OsString::from("gen")),
            Some(OsString::from("profile-use")),
        )
        .expect_err("GEN and USE must remain mutually exclusive");
        assert!(error.contains("at most one"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn pgo_path_parsing_rejects_non_utf8_gen_and_use_paths() {
        use std::os::unix::ffi::OsStringExt;

        let non_utf8 = OsString::from_vec(vec![b'p', b'g', b'o', 0xff]);
        let gen_error = pgo_paths_from_os(Some(non_utf8.clone()), None)
            .expect_err("non-UTF-8 GEN path must fail explicitly");
        assert!(gen_error.contains("TCG_PGO_GEN"), "{gen_error}");
        assert!(gen_error.contains("not valid UTF-8"), "{gen_error}");

        let use_error = pgo_paths_from_os(None, Some(non_utf8))
            .expect_err("non-UTF-8 USE path must fail explicitly");
        assert!(use_error.contains("TCG_PGO_USE"), "{use_error}");
        assert!(use_error.contains("not valid UTF-8"), "{use_error}");
    }

    #[test]
    fn pgo_sidecar_rejects_sparse_counter_indices_before_writing() {
        let files = TestPgoFiles::new("sparse-indices");
        let key = test_pgo_key(0x10);
        let mut map = test_counter_map();
        map.sites[1].counter_index = 2;
        map.sites[2].counter_index = 3;
        let sink = Arc::new(Mutex::new(map));

        let error = write_pgo_sites(files.base(), &key, &sink)
            .expect_err("a sparse counter map must fail closed");
        assert!(error.contains("counter site 1"), "{error}");
        assert!(error.contains("has index 2"), "{error}");
        assert!(error.contains("expected dense index 1"), "{error}");
        assert!(!files.sites_path().exists());
    }

    #[test]
    fn pgo_sidecar_rejects_reordered_counter_indices_before_writing() {
        let files = TestPgoFiles::new("reordered-indices");
        let key = test_pgo_key(0x11);
        let mut map = test_counter_map();
        map.sites[0].counter_index = 1;
        map.sites[1].counter_index = 0;
        let sink = Arc::new(Mutex::new(map));

        let error = write_pgo_sites(files.base(), &key, &sink)
            .expect_err("a reordered counter map must fail closed");
        assert!(error.contains("counter site 0"), "{error}");
        assert!(error.contains("has index 1"), "{error}");
        assert!(error.contains("expected dense index 0"), "{error}");
        assert!(!files.sites_path().exists());
    }

    #[test]
    fn pgo_sidecar_writer_rejects_unrepresentable_and_duplicate_sites() {
        let key = test_pgo_key(0x12);
        for (label, map, expected) in [
            (
                "unrepresentable-function",
                {
                    let mut map = test_counter_map();
                    map.sites[0].function = "hot\talias".to_owned();
                    map
                },
                "cannot be represented",
            ),
            (
                "duplicate-site",
                {
                    let mut map = test_counter_map();
                    map.sites[1].block_id = 0;
                    map
                },
                "duplicates `hot` block 0",
            ),
            (
                "oversized-function",
                {
                    let mut map = test_counter_map();
                    map.sites[0].function = "f".repeat(PGO_MAX_FUNCTION_NAME_BYTES + 1);
                    map
                },
                "over the 4096-byte sidecar limit",
            ),
        ] {
            let files = TestPgoFiles::new(label);
            let sink = Arc::new(Mutex::new(map));

            let error = write_pgo_sites(files.base(), &key, &sink)
                .expect_err("the writer must not emit an ambiguous sidecar");
            assert!(error.contains(expected), "{error}");
            assert!(!files.sites_path().exists());
        }
    }

    #[test]
    fn pgo_sidecar_writer_enforces_total_byte_limit() {
        let files = TestPgoFiles::new("writer-byte-limit");
        let key = test_pgo_key(0x16);
        // 2047 rows of 4099 bytes each exceed 8 MiB once the headers are
        // included, while every individual name remains exactly at its limit.
        let sites = (0..2047)
            .map(|index| {
                let prefix = format!("{index:04}");
                CounterSite {
                    function: prefix + &"f".repeat(PGO_MAX_FUNCTION_NAME_BYTES - 4),
                    block_id: 0,
                    counter_index: index,
                    symbol: String::new(),
                }
            })
            .collect();
        let sink = Arc::new(Mutex::new(CounterMap { sites }));

        let error = write_pgo_sites(files.base(), &key, &sink)
            .expect_err("writer must enforce the complete sidecar byte ceiling");
        assert!(
            error.contains(&format!("{PGO_MAX_SIDECAR_BYTES}-byte sidecar limit")),
            "{error}"
        );
        assert!(!files.sites_path().exists());
    }

    #[test]
    fn pgo_sidecar_rejects_more_than_the_backend_site_limit() {
        let key = test_pgo_key(0x13);
        let sites: Vec<_> = (0..=PGO_MAX_COUNTER_SITES)
            .map(|index| CounterSite {
                function: format!("function_{index}"),
                block_id: 0,
                counter_index: index as u32,
                symbol: String::new(),
            })
            .collect();
        let writer_files = TestPgoFiles::new("writer-site-limit");
        let sink = Arc::new(Mutex::new(CounterMap { sites }));
        let error = write_pgo_sites(writer_files.base(), &key, &sink)
            .expect_err("writer must enforce the backend counter ceiling");
        assert!(error.contains("4097 counter sites"), "{error}");
        assert!(error.contains("limit of 4096"), "{error}");
        assert!(!writer_files.sites_path().exists());

        let reader_files = TestPgoFiles::new("reader-site-limit");
        let mut lines = String::new();
        for index in 0..=PGO_MAX_COUNTER_SITES {
            lines.push_str(&format!("function_{index}\t0\n"));
        }
        fs::write(reader_files.sites_path(), sites_fixture(&key, &lines))
            .expect("write oversized sites fixture");
        let error = load_pgo_profile(reader_files.base(), &key)
            .expect_err("reader must enforce the backend counter ceiling");
        assert!(error.contains(":4100:"), "{error}");
        assert!(error.contains("more than 4096 counter sites"), "{error}");
    }

    #[test]
    fn pgo_sidecar_reader_enforces_byte_and_function_name_limits() {
        let key = test_pgo_key(0x15);

        let oversized_file = TestPgoFiles::new("reader-byte-limit");
        fs::write(
            oversized_file.sites_path(),
            vec![0xff; PGO_MAX_SIDECAR_BYTES as usize + 1],
        )
        .expect("write sidecar over byte limit");
        let error = load_pgo_profile(oversized_file.base(), &key)
            .expect_err("reader must stop at the sidecar byte ceiling");
        assert!(
            error.contains(&format!("{PGO_MAX_SIDECAR_BYTES}-byte sidecar limit")),
            "{error}"
        );
        assert!(
            !error.contains("UTF-8"),
            "size rejection must precede UTF-8 validation: {error}"
        );

        let oversized_name = TestPgoFiles::new("reader-function-name-limit");
        let rows = format!("{}\t0\n", "f".repeat(PGO_MAX_FUNCTION_NAME_BYTES + 1));
        fs::write(oversized_name.sites_path(), sites_fixture(&key, &rows))
            .expect("write oversized function-name fixture");
        let error = load_pgo_profile(oversized_name.base(), &key)
            .expect_err("reader must enforce the function-name byte ceiling");
        assert!(error.contains(":4:"), "{error}");
        assert!(
            error.contains("over the 4096-byte sidecar limit"),
            "{error}"
        );
    }

    #[test]
    fn pgo_sidecar_roundtrip_preserves_sites_and_counters() {
        let files = TestPgoFiles::new("roundtrip");
        let key = test_pgo_key(0xfeed_face_cafe_beef_0123_4567_89ab_cdef);
        let map = test_counter_map();
        let sink = Arc::new(Mutex::new(map));

        write_pgo_sites(files.base(), &key, &sink).expect("write GEN-mode sites sidecar");
        write_raw_counters(&files.raw_path(), &[10_000, 9_750, 3]);

        let sites = fs::read_to_string(files.sites_path()).expect("read sites sidecar");
        let site_rows = "hot\t0\nhot\t7\ncold\t0\n";
        assert_eq!(
            sites,
            format!(
                "{PGO_SIDECAR_FORMAT_ID}\n{:032x}\n{:032x}\n{site_rows}",
                key.digest(),
                site_map_checksum(site_rows)
            )
        );

        let profile =
            load_pgo_profile(files.base(), &key).expect("matching sidecars must load in USE mode");
        assert_eq!(profile.profile_key_digest, format!("{:032x}", key.digest()));
        let hot = profile.function("hot").expect("hot function profile");
        assert_eq!(hot.call_count, 10_000);
        assert_eq!(hot.block_hits(0), 10_000);
        assert_eq!(hot.block_hits(7), 9_750);
        let cold = profile.function("cold").expect("cold function profile");
        assert_eq!(cold.call_count, 3);
        assert_eq!(cold.block_hits(0), 3);
    }

    #[test]
    fn pgo_sidecar_accepts_an_explicit_zero_site_profile() {
        let files = TestPgoFiles::new("zero-sites");
        let key = test_pgo_key(0x14);
        let sink = Arc::new(Mutex::new(CounterMap::new()));

        write_pgo_sites(files.base(), &key, &sink).expect("write zero-site sidecar");
        fs::write(files.raw_path(), []).expect("write zero-byte dump for zero sites");
        let profile = load_pgo_profile(files.base(), &key)
            .expect("a module with no compiled functions has a valid empty profile");
        assert_eq!(profile.profile_key_digest, format!("{:032x}", key.digest()));
        assert!(profile.function("missing").is_none());
    }

    #[test]
    fn pgo_sidecar_rejects_incompatible_digest() {
        let files = TestPgoFiles::new("stale-digest");
        let generated_key = test_pgo_key(1);
        let expected_key = test_pgo_key(2);
        let sink = Arc::new(Mutex::new(test_counter_map()));

        write_pgo_sites(files.base(), &generated_key, &sink).expect("write sites sidecar");
        write_raw_counters(&files.raw_path(), &[1, 2, 3]);

        let error = load_pgo_profile(files.base(), &expected_key)
            .expect_err("a sidecar from a different compile key must fail closed");
        assert!(error.contains("incompatible profile key"), "{error}");
        assert!(
            error.contains(&format!("{:032x}", generated_key.digest())),
            "{error}"
        );
        assert!(
            error.contains(&format!("{:032x}", expected_key.digest())),
            "{error}"
        );
    }

    #[test]
    fn pgo_sidecar_rejects_unknown_format_and_malformed_digest() {
        let key = test_pgo_key(0x20);

        let unknown = TestPgoFiles::new("unknown-format");
        fs::write(
            unknown.sites_path(),
            format!(
                "trust-cg-ws2-import/{}/pgo-sites-v2\n{:032x}\n",
                env!("CARGO_PKG_VERSION"),
                key.digest()
            ),
        )
        .expect("write unknown-format fixture");
        let error = load_pgo_profile(unknown.base(), &key)
            .expect_err("unknown sidecar format must fail closed");
        assert!(error.contains("unsupported sites format"), "{error}");
        assert!(error.contains(PGO_SIDECAR_FORMAT_ID), "{error}");

        let missing = TestPgoFiles::new("missing-digest");
        fs::write(missing.sites_path(), format!("{PGO_SIDECAR_FORMAT_ID}\n"))
            .expect("write missing-digest fixture");
        let error =
            load_pgo_profile(missing.base(), &key).expect_err("a missing digest must fail closed");
        assert!(error.contains("missing profile digest"), "{error}");

        for (label, digest) in [
            ("short-digest", "1234"),
            ("uppercase-digest", "0123456789abcdef0123456789abcdeF"),
            ("oversized-digest", "000000000000000000000000000000000"),
        ] {
            let files = TestPgoFiles::new(label);
            fs::write(
                files.sites_path(),
                format!("{PGO_SIDECAR_FORMAT_ID}\n{digest}\n"),
            )
            .expect("write malformed-digest fixture");

            let error = load_pgo_profile(files.base(), &key)
                .expect_err("a non-canonical digest must fail closed");
            assert!(error.contains(":2:"), "{error}");
            assert!(error.contains("malformed profile digest"), "{error}");
        }
    }

    #[test]
    fn pgo_sidecar_rejects_missing_malformed_and_mismatched_site_checksum() {
        let key = test_pgo_key(0x24);

        let missing = TestPgoFiles::new("missing-map-checksum");
        fs::write(
            missing.sites_path(),
            format!("{PGO_SIDECAR_FORMAT_ID}\n{:032x}\n", key.digest()),
        )
        .expect("write missing-checksum fixture");
        let error = load_pgo_profile(missing.base(), &key)
            .expect_err("a missing site-map checksum must fail closed");
        assert!(error.contains("missing site-map checksum"), "{error}");

        for (label, checksum) in [
            ("short-map-checksum", "1234"),
            ("uppercase-map-checksum", "0123456789abcdef0123456789abcdeF"),
            (
                "oversized-map-checksum",
                "000000000000000000000000000000000",
            ),
        ] {
            let files = TestPgoFiles::new(label);
            fs::write(
                files.sites_path(),
                format!(
                    "{PGO_SIDECAR_FORMAT_ID}\n{:032x}\n{checksum}\nhot\t0\n",
                    key.digest()
                ),
            )
            .expect("write malformed-checksum fixture");
            let error = load_pgo_profile(files.base(), &key)
                .expect_err("a non-canonical site-map checksum must fail closed");
            assert!(error.contains(":3:"), "{error}");
            assert!(error.contains("malformed site-map checksum"), "{error}");
        }

        let reordered = TestPgoFiles::new("stale-map-checksum");
        let original_rows = "hot\t0\ncold\t0\n";
        let reordered_rows = "cold\t0\nhot\t0\n";
        fs::write(
            reordered.sites_path(),
            format!(
                "{PGO_SIDECAR_FORMAT_ID}\n{:032x}\n{:032x}\n{reordered_rows}",
                key.digest(),
                site_map_checksum(original_rows)
            ),
        )
        .expect("write reordered site-map fixture with stale checksum");
        let error = load_pgo_profile(reordered.base(), &key)
            .expect_err("reordered site rows must fail their compatibility checksum");
        assert!(
            error.contains("corrupt or incompatible site map"),
            "{error}"
        );
        assert!(error.contains("checksum"), "{error}");

        let unterminated = TestPgoFiles::new("unterminated-site-row");
        let rows = "hot\t0";
        fs::write(unterminated.sites_path(), sites_fixture(&key, rows))
            .expect("write checksum-matching but non-canonical site rows");
        let error = load_pgo_profile(unterminated.base(), &key)
            .expect_err("canonical site rows must end with a newline");
        assert!(error.contains("final row lacks a newline"), "{error}");
    }

    #[test]
    fn pgo_sidecar_rejects_missing_and_empty_inputs() {
        let key = test_pgo_key(0x21);

        let missing_sites = TestPgoFiles::new("missing-sites");
        let error = load_pgo_profile(missing_sites.base(), &key)
            .expect_err("a missing sites file must fail closed");
        assert!(error.contains("reading"), "{error}");
        assert!(error.contains(".sites"), "{error}");

        let empty_sites = TestPgoFiles::new("empty-sites");
        fs::write(empty_sites.sites_path(), []).expect("write empty sites fixture");
        let error = load_pgo_profile(empty_sites.base(), &key)
            .expect_err("an empty sites file must fail closed");
        assert!(error.contains("empty sites file"), "{error}");

        let missing_raw = TestPgoFiles::new("missing-raw");
        fs::write(missing_raw.sites_path(), sites_fixture(&key, "hot\t0\n"))
            .expect("write sites fixture");
        let error = load_pgo_profile(missing_raw.base(), &key)
            .expect_err("a missing raw file must fail closed");
        assert!(error.contains("reading"), "{error}");
        assert!(error.contains(".raw"), "{error}");

        let empty_raw = TestPgoFiles::new("empty-raw");
        fs::write(empty_raw.sites_path(), sites_fixture(&key, "hot\t0\n"))
            .expect("write sites fixture");
        fs::write(empty_raw.raw_path(), []).expect("write empty raw fixture");
        let error = load_pgo_profile(empty_raw.base(), &key)
            .expect_err("an empty raw file for a non-empty map must fail closed");
        assert!(error.contains("0 byte(s)"), "{error}");
        assert!(error.contains("expected 8 bytes"), "{error}");
    }

    #[test]
    fn pgo_sidecar_rejects_blank_duplicate_and_trailing_site_data() {
        let key = test_pgo_key(0x22);
        for (label, lines, expected_line, expected) in [
            ("blank-site", "\nhot\t0\n", ":4:", "malformed site line"),
            (
                "duplicate-site",
                "hot\t0\nhot\t0\n",
                ":5:",
                "duplicate site",
            ),
            (
                "trailing-junk",
                "hot\t0\nunexpected-trailer\n",
                ":5:",
                "malformed site line",
            ),
        ] {
            let files = TestPgoFiles::new(label);
            fs::write(files.sites_path(), sites_fixture(&key, lines))
                .expect("write corrupt sites fixture");
            write_raw_counters(&files.raw_path(), &[1, 2]);

            let error = load_pgo_profile(files.base(), &key)
                .expect_err("corrupt site data must fail closed");
            assert!(error.contains(expected_line), "{error}");
            assert!(error.contains(expected), "{error}");
        }
    }

    #[test]
    fn pgo_sidecar_rejects_raw_length_mismatch() {
        let files = TestPgoFiles::new("raw-length");
        let key = test_pgo_key(3);
        let sink = Arc::new(Mutex::new(test_counter_map()));

        write_pgo_sites(files.base(), &key, &sink).expect("write sites sidecar");
        write_raw_counters(&files.raw_path(), &[1, 2]);

        let error = load_pgo_profile(files.base(), &key)
            .expect_err("a short raw counter dump must fail closed");
        assert!(error.contains("16 byte(s)"), "{error}");
        assert!(error.contains("lists 3 site(s)"), "{error}");
        assert!(error.contains("expected 24 bytes"), "{error}");
    }

    #[test]
    fn pgo_sidecar_rejects_oversized_and_trailing_raw_data() {
        let key = test_pgo_key(0x23);
        for (label, raw, expected_size) in [
            (
                "oversized-raw",
                [1_u64, 2, 3, 4]
                    .into_iter()
                    .flat_map(u64::to_le_bytes)
                    .collect::<Vec<_>>(),
                "32 byte(s)",
            ),
            (
                "trailing-raw-byte",
                {
                    let mut bytes = [1_u64, 2, 3]
                        .into_iter()
                        .flat_map(u64::to_le_bytes)
                        .collect::<Vec<_>>();
                    bytes.push(0xff);
                    bytes
                },
                "25 byte(s)",
            ),
        ] {
            let files = TestPgoFiles::new(label);
            fs::write(
                files.sites_path(),
                sites_fixture(&key, "hot\t0\nhot\t7\ncold\t0\n"),
            )
            .expect("write sites fixture");
            fs::write(files.raw_path(), raw).expect("write corrupt raw fixture");

            let error = load_pgo_profile(files.base(), &key)
                .expect_err("oversized or trailing raw data must fail closed");
            assert!(error.contains(expected_size), "{error}");
            assert!(error.contains("expected 24 bytes"), "{error}");
        }
    }

    #[test]
    fn pgo_sidecar_rejects_malformed_site_inputs() {
        let key = test_pgo_key(4);
        for (label, line, expected) in [
            ("missing-tab", "hot-0", "malformed site line"),
            ("invalid-block", "hot\tnot-a-block", "malformed block id"),
            ("leading-zero-block", "hot\t00", "non-canonical block id"),
            ("plus-block", "hot\t+1", "non-canonical block id"),
            ("empty-function", "\t0", "empty function name"),
        ] {
            let files = TestPgoFiles::new(label);
            fs::write(
                files.sites_path(),
                sites_fixture(&key, &format!("{line}\n")),
            )
            .expect("write malformed sites fixture");
            write_raw_counters(&files.raw_path(), &[1]);

            let error = load_pgo_profile(files.base(), &key)
                .expect_err("malformed site metadata must fail closed");
            assert!(error.contains(":4:"), "{error}");
            assert!(error.contains(expected), "{error}");
        }
    }

    #[test]
    fn pgo_multi_function_generate_sidecar_to_use_compile() {
        let fixture =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/revertBits_clang_o0.ll");
        let (input, module) =
            read_and_import_module(&fixture).expect("import existing multi-function LLVM fixture");
        let config = test_config(OptLevel::O2, None);
        let key = pgo_compatibility_key(
            input.as_bytes(),
            &config,
            default_target_spec(),
            0xfeed_face_cafe_beef_0123_4567_89ab_cdef,
        );
        let sink = Arc::new(Mutex::new(CounterMap::new()));

        let generated = Compiler::new_for_target_spec(config.clone(), default_target_spec())
            .with_profile_generate(sink.clone())
            .compile(&module)
            .expect("multi-function profile-generate compile");
        assert!(!generated.object_code.is_empty());

        let map = sink
            .lock()
            .expect("profile-generate counter map lock")
            .clone();
        let functions: HashSet<_> = map
            .sites
            .iter()
            .map(|site| site.function.as_str())
            .collect();
        assert!(
            functions.len() >= 2,
            "fixture must exercise module-wide counter indexing"
        );
        assert!(
            map.sites
                .iter()
                .enumerate()
                .all(|(index, site)| site.counter_index as usize == index),
            "the generated map must be globally dense before serialization"
        );

        // Keep this integration test cross-platform: it compiles the real
        // AArch64 instrumented object and synthesizes the runtime's documented
        // little-endian u64 dump instead of trying to execute that object on
        // every cargo-test host.
        let files = TestPgoFiles::new("multi-function-gen-use");
        write_pgo_sites(files.base(), &key, &sink).expect("serialize generated sites");
        let counters: Vec<u64> = (1..=map.sites.len() as u64).collect();
        write_raw_counters(&files.raw_path(), &counters);
        let profile =
            load_pgo_profile(files.base(), &key).expect("load generated multi-function profile");
        for function in functions {
            assert!(
                profile.function(function).is_some(),
                "loaded profile must retain `{function}`"
            );
        }

        let used = Compiler::new_for_target_spec(config, default_target_spec())
            .with_profile_use(profile)
            .compile(&module)
            .expect("multi-function profile-use compile");
        assert!(!used.object_code.is_empty());
    }

    #[test]
    fn parse_legacy_contract_defaults_to_o0() {
        let parsed = parse_args(&argv(&["trust-cg-ws2-import", "in.ll", "out.o"]))
            .expect("legacy args parse");

        let ParseOutcome::Run(args) = parsed else {
            panic!("expected run args");
        };
        assert_eq!(args.input, PathBuf::from("in.ll"));
        assert_eq!(args.output, PathBuf::from("out.o"));
        assert_eq!(args.opt_level, OptLevel::O0);
        assert_eq!(args.target_spec, default_target_spec());
        assert_eq!(args.proof_report_path(), None);
        assert_eq!(args.cegis_superopt_budget_sec, None);
    }

    #[test]
    fn parse_benchmark_flags_accept_o2_and_emit_proofs_dir() {
        let parsed = parse_args(&argv(&[
            "trust-cg-ws2-import",
            "--opt-level",
            "2",
            "--cegis-superopt=7",
            "--emit-proofs",
            "proofs",
            "in.ll",
            "out.o",
        ]))
        .expect("benchmark args parse");

        let ParseOutcome::Run(args) = parsed else {
            panic!("expected run args");
        };
        assert_eq!(args.opt_level, OptLevel::O2);
        assert_eq!(args.target_spec, default_target_spec());
        assert_eq!(args.cegis_superopt_budget_sec, Some(7));
        assert_eq!(
            args.proof_report_path(),
            Some(PathBuf::from("proofs/proof-report.json"))
        );
        assert_eq!(
            args.proof_destination_kind(),
            Some("structured-report-directory")
        );
    }

    #[test]
    fn parse_target_flag_accepts_supported_apple_aarch64() {
        let parsed = parse_args(&argv(&[
            "trust-cg-ws2-import",
            "--target",
            "arm64-apple-darwin",
            "in.ll",
            "out.o",
        ]))
        .expect("target args parse");

        let ParseOutcome::Run(args) = parsed else {
            panic!("expected run args");
        };
        assert_eq!(args.target_spec.triple(), WS2_APPLE_AARCH64_TARGET);
    }

    #[test]
    fn parse_target_flag_rejects_unsupported_combo() {
        let error = parse_args(&argv(&[
            "trust-cg-ws2-import",
            "--target=aarch64-pc-windows-msvc",
            "in.ll",
            "out.o",
        ]))
        .expect_err("unsupported target should reject");
        assert!(error.contains("unsupported target"));
        assert!(error.contains("aarch64-pc-windows-msvc"));
    }

    #[test]
    fn parse_rejects_multiple_proof_destinations() {
        let error = parse_args(&argv(&[
            "trust-cg-ws2-import",
            "--proof-report",
            "proof.json",
            "--emit-proofs",
            "proofs",
            "in.ll",
            "out.o",
        ]))
        .expect_err("duplicate proof destinations reject");
        assert!(error.contains("use only one"));
    }

    #[test]
    fn proof_report_records_config_provenance_and_certificates() {
        let args = DriverArgs {
            input: PathBuf::from("in.ll"),
            output: PathBuf::from("out.o"),
            opt_level: OptLevel::O2,
            target_spec: default_target_spec(),
            proof_destination: Some(ProofDestination::ReportFile(PathBuf::from("proof.json"))),
            cegis_superopt_budget_sec: Some(3),
        };
        let certificate = ProofOptimizationCertificateCitation {
            function_name: "ReverseBits32".to_owned(),
            certificate_id: "cert".to_owned(),
            proof_hash: "proof".to_owned(),
            validation_hash: "validation".to_owned(),
            source_region_hash: "source".to_owned(),
            target_region_hash: "target".to_owned(),
            transform_name: "proof-opts.test".to_owned(),
            transform_version: 1,
            admission: "proof-facts".to_owned(),
            kind: "Rewrite".to_owned(),
            status: "applied".to_owned(),
            rejection_code: None,
            rejection_fact: None,
            rejection_detail: None,
            consumed_facts: vec![ProofOptimizationConsumedFactCitation {
                name: "ValidShift".to_owned(),
                payload: Some("31".to_owned()),
            }],
        };
        let result = CompilationResult {
            object_code: vec![0, 1, 2, 3],
            metrics: CompilationMetrics {
                code_size_bytes: 4,
                instruction_count: 1,
                function_count: 1,
                optimization_passes_run: 12,
                proof_optimizations: ProofOptimizationMetrics {
                    certificate_count: 1,
                    applied_count: 1,
                    ..ProofOptimizationMetrics::default()
                },
                fsym_trust_ir: FsymTrustIrMetrics::default(),
            },
            trace: None,
            proofs: None,
            certified_pass_chain: None,
            proof_optimization_certificates: vec![certificate],
            compile_artifact_cache_telemetry: Vec::new(),
        };

        let report = proof_report_json_value(
            &args,
            &test_config(OptLevel::O2, Some(3)),
            &result,
            &argv(&["trust-cg-ws2-import", "--opt-level", "2", "in.ll", "out.o"]),
        );

        assert_eq!(report["schema"], "trust-cg.ws2_import.proof_report.v1");
        assert_eq!(report["compiler_config"]["opt_level"], "O2");
        assert_eq!(
            report["compiler_config"]["target_triple"],
            default_target_spec().triple()
        );
        assert_eq!(report["compiler_config"]["cegis_superopt_budget_sec"], 3);
        assert_eq!(report["provenance"]["input_path"], "in.ll");
        assert_eq!(report["provenance"]["object_path"], "out.o");
        assert_eq!(report["provenance"]["proof_report_path"], "proof.json");
        assert_eq!(report["object"]["static_instruction_count"], 1);
        assert_eq!(report["proof_optimizations"]["certificate_count"], 1);
        assert_eq!(
            report["proof_optimizations"]["certificates"][0]["transform_name"],
            "proof-opts.test"
        );
    }
}
