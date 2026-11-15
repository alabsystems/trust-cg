// compile_corpus.rs - the compile-time regression corpus runner.
//
// Compiles every module of a corpus manifest (benchmarks/compile-corpus) through
// the backend's real compile lanes and records, per module and lane:
//
//   * the VERDICT (compiled, or the exact error text),
//   * the OUTPUT IDENTITY (SHA-256 of the emitted machine code / object bytes,
//     plus one digest per function where the lane exposes function ranges),
//   * the frame-net verifier's coverage and decline counters for the compile,
//   * the cost: instructions retired and cycles elapsed per phase bracket,
//     read in process from the kernel's per-process counters
//     (`proc_pid_rusage(RUSAGE_INFO_V4)` on macOS).
//
// Two builds that produce the same verdicts, digests and counters on the whole
// corpus emitted the same bytes and reached the same verification verdicts; the
// instruction columns then compare their compile cost. `run.py compare` in the
// benchmark directory checks exactly that.
//
// The phase brackets are coarse and exact (load, adapter, per-function
// preparation, link); the attribution INSIDE a bracket (isel, optimization,
// regalloc, each verification pass, encoding) comes from a symbolized `sample`
// profile of `--repeat` runs (`run.py profile`), which reports shares.
//
// Lanes (each compiles the same module independently):
//   jit-raw     the AArch64 raw JIT lane as an embedding runtime drives it:
//               adapter -> prepare_jit_lir_module (the shared pre-ISel LIR
//               step: inlining, inline-only bodies, range simplification;
//               bracket `lir_prepare`; TCG_NO_JIT_LIR_PREPARE skips it) ->
//               Pipeline::prepare_function_with_metrics (the JIT-latency
//               allocator profile) -> JitCompiler link, captured as a
//               RelocatableImage so the bytes are address-free.
//   jit-raw-checked  the same with sealed functions
//               (Pipeline::prepare_function_checked + compile_raw_checked_*):
//               a final-stream check is not re-run at link; same bytes.
//   jit-compiler  Compiler::compile_module_to_jit, the compiler's own (typed)
//               JIT in the JIT-latency configuration, serial: the lane ay's JIT
//               kernels use. Its link skips a final-stream check its
//               preparation passed (TCG_NO_SEALED_JIT_LINK restores it). On
//               request only (`--lane jit-compiler`), on every entry that
//               lists jit-raw; no manifest lists it.
//   aot-object  Compiler::compile to an object file (the AOT/CLI lane), serial,
//               proof certificates off.
//   aot-proofs  the same with proof certificates on (the rustc bridge's
//               production setting).
//
// An entry is one module file or a directory of them (a program the rustc
// bridge compiled one codegen unit at a time, dumped with
// `-Ztrust-ir-cg-args=dump-trust-ir=DIR`); a directory's modules are compiled
// in name order and the entry's record lists each module's verdict and output.
//
// Bench tooling only: nothing here is a proof or a publication authority.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::{BTreeSet, HashMap};
use std::path::{Path, PathBuf};

use anyhow::{Context, anyhow, bail};
use clap::{Parser, Subcommand};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use trust_cg_codegen::compiler::CompilerConfig;
use trust_cg_codegen::jit::{JitCompiler, JitConfig};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, load_module_from_bytes};
use trust_cg_codegen::target::Target;
use trust_cg_codegen::{
    CheckedAarch64Functions, Compiler, InlineOnlyAdmission, JitExternBindings,
    prepare_jit_lir_module,
};
use trust_cg_lower::adapter::{GuardCarrierArch, TlsDialect, prepare_module_for_lir};
use trust_cg_verify::post_ra_spill_slots;

const MANIFEST_SCHEMA: &str = "trust-cg.compile-corpus.manifest.v1";

/// Lanes a manifest does not list, run only when `--lane` names them, on
/// every entry that lists the paired base lane: `(lane, base lane)`.
/// Lanes that run only when `--lane` names them, on the entries that list
/// their base lane (a lane with several bases runs once per entry).
const ON_REQUEST_LANES: &[(&str, &str)] = &[
    ("jit-compiler", "jit-raw"),
    ("composed-census", "jit-raw"),
    ("composed-census", "aot-object"),
];
const RESULT_SCHEMA: &str = "trust-cg.compile-corpus.result.v1";

/// Fake, distinct extern addresses. The corpus is compiled, never executed,
/// and the jit-raw digest is taken from the pre-literal relocatable image, so
/// the values never reach a compared byte.
const FAKE_EXTERN_BASE: usize = 0x7100_0000_0000;

#[derive(Debug, Parser)]
#[command(
    name = "compile_corpus",
    about = "Compile the compile-time corpus: verdicts, output digests and per-phase instructions"
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Compile corpus entries and print one JSON result document.
    Run {
        /// Corpus manifest (benchmarks/compile-corpus/corpus.json).
        #[arg(long)]
        manifest: PathBuf,
        /// Only these entries (exact names); repeatable. Default: every entry.
        #[arg(long = "entry")]
        entries: Vec<String>,
        /// Only these lanes (jit-raw, aot-object, ...; `composed-census`
        /// classifies each function's L09-P3 composed transition record
        /// under a proof-grade preparation); repeatable. Default: the
        /// entry's own lane list.
        #[arg(long = "lane")]
        lanes: Vec<String>,
        /// Compile each (entry, lane) this many times in this process. The
        /// first compile pays one-time initialisation; the record keeps every
        /// repetition's counters.
        #[arg(long, default_value_t = 1)]
        reps: usize,
        /// Compile every module at this level (O0..O3) instead of the level
        /// its producer uses. What a JIT tier at another level would cost:
        /// `run.py tier-cost` compares such a run with the production one.
        /// Recorded in the result; the default keeps each module's own level.
        #[arg(long = "opt-level")]
        opt_level: Option<String>,
        /// Write the JSON here instead of stdout.
        #[arg(long)]
        out: Option<PathBuf>,
    },
    /// Write one of the jit-matrix workload modules (the ay BCP propagation
    /// kernels and the parent-loop kernel) as a binary TrustIR file.
    DumpBuiltin {
        /// bcp-propagate, bcp-propagate-with-decisions, bcp-watched-literal,
        /// bcp-watched-literal-chunked or parent-loop.
        #[arg(long)]
        module: String,
        #[arg(long)]
        out: PathBuf,
    },
    /// Re-encode any readable TrustIR module (binary, JSON or text) as the
    /// canonical binary container.
    Rebin {
        #[arg(long)]
        input: PathBuf,
        #[arg(long)]
        out: PathBuf,
    },
}

#[derive(Debug, Deserialize)]
struct Manifest {
    schema: String,
    entries: Vec<Entry>,
}

#[derive(Debug, Clone, Deserialize)]
struct Entry {
    name: String,
    /// Path relative to the manifest's directory.
    file: String,
    /// Where the module came from (ty-semantic, ty-fused, ay-bcp, ...).
    origin: String,
    /// O0..O3: the level the producing frontend compiles this module at.
    opt_level: String,
    lanes: Vec<String>,
    /// External symbols the producing runtime binds (beyond the module's own
    /// bodyless declarations).
    #[serde(default)]
    externs: Vec<String>,
}

// ---------------------------------------------------------------------------
// Counters
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, Default, Serialize)]
struct Counters {
    instructions: u64,
    cycles: u64,
}

impl Counters {
    fn since(self, start: Counters) -> Counters {
        Counters {
            instructions: self.instructions.saturating_sub(start.instructions),
            cycles: self.cycles.saturating_sub(start.cycles),
        }
    }
}

/// Whole-process instructions retired and cycles elapsed so far. The runner
/// compiles serially on the calling thread, so a delta is that bracket's cost
/// (plus the counter read itself, a few thousand instructions).
#[cfg(target_os = "macos")]
fn read_counters() -> Counters {
    // SAFETY: `info` is a properly aligned, zero-initialised rusage_info_v4 and
    // the flavor RUSAGE_INFO_V4 tells the kernel to write exactly that struct.
    unsafe {
        let mut info: libc::rusage_info_v4 = std::mem::zeroed();
        let rc = libc::proc_pid_rusage(
            libc::getpid(),
            libc::RUSAGE_INFO_V4,
            (&mut info as *mut libc::rusage_info_v4).cast::<libc::rusage_info_t>(),
        );
        if rc != 0 {
            return Counters::default();
        }
        Counters {
            instructions: info.ri_instructions,
            cycles: info.ri_cycles,
        }
    }
}

#[cfg(not(target_os = "macos"))]
fn read_counters() -> Counters {
    Counters::default()
}

const COUNTER_SOURCE: &str = if cfg!(target_os = "macos") {
    "proc_pid_rusage(RUSAGE_INFO_V4)"
} else {
    "unavailable"
};

// ---------------------------------------------------------------------------
// Verifier telemetry
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
struct FrameNetSnapshot {
    analyzed: u64,
    declined: u64,
    framed_analyzed: u64,
    spill_reloads_checked: u64,
    exits_checked: u64,
    violations: u64,
    declines: Vec<(String, u64)>,
}

fn frame_net_snapshot() -> FrameNetSnapshot {
    let coverage = post_ra_spill_slots::frame_coverage();
    FrameNetSnapshot {
        analyzed: coverage.analyzed,
        declined: coverage.declined,
        framed_analyzed: coverage.framed_analyzed,
        spill_reloads_checked: coverage.spill_reloads_checked,
        exits_checked: coverage.exits_checked,
        violations: post_ra_spill_slots::spill_slot_hit_count(),
        declines: post_ra_spill_slots::decline_counts()
            .into_iter()
            .map(|(reason, count)| (reason.tag().to_string(), count))
            .collect(),
    }
}

fn frame_net_delta(after: &FrameNetSnapshot, before: &FrameNetSnapshot) -> Value {
    let declines: Vec<Value> = after
        .declines
        .iter()
        .zip(before.declines.iter())
        .filter(|((_, a), (_, b))| a != b)
        .map(|((tag, a), (_, b))| json!([tag, a - b]))
        .collect();
    json!({
        "analyzed": after.analyzed - before.analyzed,
        "declined": after.declined - before.declined,
        "framed_analyzed": after.framed_analyzed - before.framed_analyzed,
        "spill_reloads_checked": after.spill_reloads_checked - before.spill_reloads_checked,
        "exits_checked": after.exits_checked - before.exits_checked,
        "violations": after.violations - before.violations,
        "declines": declines,
    })
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    digest.iter().map(|b| format!("{b:02x}")).collect()
}

fn opt_level_label(level: OptLevel) -> &'static str {
    match level {
        OptLevel::O0 => "O0",
        OptLevel::O1 => "O1",
        OptLevel::O2 => "O2",
        OptLevel::O3 => "O3",
    }
}

fn parse_opt_level(value: &str) -> anyhow::Result<OptLevel> {
    match value.to_ascii_uppercase().as_str() {
        "O0" | "0" => Ok(OptLevel::O0),
        "O1" | "1" => Ok(OptLevel::O1),
        "O2" | "2" => Ok(OptLevel::O2),
        "O3" | "3" => Ok(OptLevel::O3),
        other => bail!("invalid opt level {other:?}"),
    }
}

fn host_triple() -> &'static str {
    if cfg!(all(target_arch = "aarch64", target_os = "macos")) {
        "aarch64-apple-darwin"
    } else if cfg!(all(target_arch = "aarch64", target_os = "linux")) {
        "aarch64-unknown-linux-gnu"
    } else if cfg!(all(target_arch = "x86_64", target_os = "macos")) {
        "x86_64-apple-darwin"
    } else {
        "x86_64-unknown-linux-gnu"
    }
}

fn bodyless_declarations(module: &trust_ir::Module) -> BTreeSet<String> {
    module
        .functions
        .iter()
        .filter(|func| {
            func.blocks.is_empty() && matches!(func.linkage, trust_ir::Linkage::External)
        })
        .map(|func| func.name.clone())
        .collect()
}

fn fake_externs(module: &trust_ir::Module, entry: &Entry) -> HashMap<String, *const u8> {
    let mut names: BTreeSet<String> = bodyless_declarations(module);
    names.extend(entry.externs.iter().cloned());
    names
        .into_iter()
        .enumerate()
        .map(|(i, name)| (name, (FAKE_EXTERN_BASE + 16 * i) as *const u8))
        .collect()
}

// ---------------------------------------------------------------------------
// Corpus modules
// ---------------------------------------------------------------------------

/// Compile settings a module carries from its producer. A bridge dump writes a
/// JSON sidecar beside each module (`dump-trust-ir`); other modules take the
/// entry's opt level and the defaults.
#[derive(Debug, Clone, Default, Deserialize)]
struct Sidecar {
    #[serde(default)]
    opt_level: Option<String>,
    #[serde(default)]
    target: Option<String>,
    #[serde(default)]
    panic_unwind: bool,
    /// The bridge's `CompilerConfig::eh_frames_cannot_unwind` (a
    /// `panic=abort` AArch64 compile). Absent in older dumps: `false`.
    #[serde(default)]
    eh_frames_cannot_unwind: bool,
    /// The bridge's `CompilerConfig::eh_nounwind_callees`, which decides the
    /// exception tables under `eh_frames_cannot_unwind`. Absent in older
    /// dumps: empty.
    #[serde(default)]
    eh_nounwind_callees: std::collections::BTreeSet<String>,
    /// The bridge's `CompilerConfig::link_unit_definitions` (ruling OD-216):
    /// the trusted runtime routines the crate's other codegen units define.
    /// Absent in older dumps and for a crate that defines none: empty.
    #[serde(default)]
    link_unit_definitions: std::collections::BTreeSet<String>,
    /// The bridge's `CompilerConfig::never_inline` (ruling
    /// OD-NATIVE-NEVER-INLINE-20261107): the `#[inline(never)]` and `#[cold]`
    /// functions the module holds a body of, which OPT-4 does not splice.
    /// Absent in older dumps (a native bridge compile then passed none):
    /// empty.
    #[serde(default)]
    never_inline: std::collections::BTreeSet<String>,
}

struct CorpusModule {
    name: String,
    module: trust_ir::Module,
    opt_level: OptLevel,
    target: Target,
    panic_unwind: bool,
    eh_frames_cannot_unwind: bool,
    eh_nounwind_callees: std::collections::BTreeSet<String>,
    link_unit_definitions: std::collections::BTreeSet<String>,
    never_inline: std::collections::BTreeSet<String>,
}

/// The modules of an entry: its file, or every `*.trust_irbin` of its
/// directory in name order (one compile unit each, compiled in turn).
fn load_entry_modules(base: &Path, entry: &Entry) -> anyhow::Result<Vec<CorpusModule>> {
    let path = base.join(&entry.file);
    let files: Vec<PathBuf> = if path.is_dir() {
        let mut files: Vec<PathBuf> = std::fs::read_dir(&path)
            .with_context(|| format!("read {}", path.display()))?
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.extension().is_some_and(|x| x == "trust_irbin"))
            .collect();
        files.sort();
        files
    } else {
        vec![path.clone()]
    };
    let entry_opt = parse_opt_level(&entry.opt_level)?;
    let mut modules = Vec::with_capacity(files.len());
    for file in files {
        let bytes = std::fs::read(&file).with_context(|| format!("read {}", file.display()))?;
        let module = load_module_from_bytes(&bytes)
            .map_err(|e| anyhow!("decode {}: {e}", file.display()))?;
        let sidecar_path = file.with_extension("json");
        let sidecar: Sidecar = if path.is_dir() && sidecar_path.exists() {
            serde_json::from_str(&std::fs::read_to_string(&sidecar_path)?)
                .with_context(|| format!("parse {}", sidecar_path.display()))?
        } else {
            Sidecar::default()
        };
        let opt_level = match &sidecar.opt_level {
            Some(level) => parse_opt_level(level)?,
            None => entry_opt,
        };
        let target = match sidecar.target.as_deref() {
            None | Some("Aarch64") => Target::Aarch64,
            Some("X86_64") => Target::X86_64,
            Some(other) => bail!("{}: unsupported sidecar target {other:?}", file.display()),
        };
        let name = file
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_default();
        modules.push(CorpusModule {
            name,
            module,
            opt_level,
            target,
            panic_unwind: sidecar.panic_unwind,
            eh_frames_cannot_unwind: sidecar.eh_frames_cannot_unwind,
            eh_nounwind_callees: sidecar.eh_nounwind_callees,
            link_unit_definitions: sidecar.link_unit_definitions,
            never_inline: sidecar.never_inline,
        });
    }
    Ok(modules)
}

// ---------------------------------------------------------------------------
// Lanes
// ---------------------------------------------------------------------------

/// One module's compile through one lane: its verdict and output identity,
/// and the instructions of each phase bracket.
struct ModuleOutcome {
    record: Value,
    phases: Vec<(&'static str, Counters)>,
    /// What the shared pre-ISel LIR step did (`jit-raw` lanes), reported
    /// beside the record: it is not part of the emitted-code identity.
    lir_prepare: Option<Value>,
}

fn outcome_error(phases: Vec<(&'static str, Counters)>, error: String) -> ModuleOutcome {
    ModuleOutcome {
        record: json!({"verdict": "error", "error": error}),
        phases,
        lir_prepare: None,
    }
}

/// The raw AArch64 JIT lane, driven the way an embedding runtime drives it.
/// `checked` prepares sealed functions (`Pipeline::prepare_function_checked`)
/// and links them with `JitCompiler::compile_raw_checked_relocatable`, which
/// does not re-run a final-stream check preparation already passed; its bytes
/// must equal the plain lane's.
fn lane_jit_raw(unit: &CorpusModule, entry: &Entry, checked: bool) -> ModuleOutcome {
    let module = &unit.module;
    let opt_level = unit.opt_level;
    let mut phases = Vec::new();

    let t = read_counters();
    let translated = (|| -> Result<_, String> {
        let prepared = prepare_module_for_lir(module, GuardCarrierArch::AArch64)
            .map_err(|e| format!("adapter preparation: {e}"))?;
        let (functions, validation) = prepared
            .translate_with_tls_and_validation_with_license(
                TlsDialect::default(),
                &trust_cg_jit_matrix::bench_corpus_license(),
            )
            .map_err(|e| format!("adapter translation: {e}"))?;
        validation
            .replay_exact_module_bindings(&functions)
            .map_err(|e| format!("exact binding replay: {e}"))?;
        drop(validation);
        Ok((prepared, functions))
    })();
    phases.push(("adapter", read_counters().since(t)));
    let (prepared, mut functions) = match translated {
        Ok(translated) => translated,
        Err(error) => return outcome_error(phases, error),
    };
    let declarations = bodyless_declarations(module);
    functions.retain(|(func, _)| !declarations.contains(func.name.as_str()));

    // The shared pre-ISel LIR module step an embedding runtime calls between
    // replay and preparation (`TCG_NO_JIT_LIR_PREPARE` skips it, restoring
    // the pre-step bytes).
    let externs = fake_externs(module, entry);
    let t = read_counters();
    let lir_prepare = prepare_jit_lir_module(
        &mut functions,
        prepared.module(),
        GuardCarrierArch::AArch64,
        TlsDialect::default(),
        opt_level,
        InlineOnlyAdmission::DisclosedPremise,
        &trust_cg_jit_matrix::bench_corpus_license(),
        JitExternBindings::Map(&externs),
    );
    phases.push(("lir_prepare", read_counters().since(t)));
    drop(prepared);
    let lir_prepare = match lir_prepare {
        Ok(preparation) => json!({
            "ran": preparation.ran,
            "inline_sites": preparation.inline.sites,
            "inline_rounds": preparation.inline.rounds,
            "inline_only_spliced": preparation
                .inline_only
                .spliced
                .iter()
                .map(|u| json!([u.name, u.sites]))
                .collect::<Vec<_>>(),
            "inline_only_withheld": preparation.inline_only.withheld.len(),
            "range": preparation.range_trace_detail(),
        }),
        Err(error) => return outcome_error(phases, format!("lir prepare: {error}")),
    };

    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        emit_debug: false,
        verify: false,
        target_triple: host_triple().to_owned(),
        cegis_superopt_budget_sec: None,
        enable_jit_fast_regalloc: true,
        ..Default::default()
    });
    let t = read_counters();
    let mut machine = Vec::with_capacity(functions.len());
    let mut sealed = CheckedAarch64Functions::new();
    for (func, proof_ctx) in &functions {
        let prepared = if checked {
            pipeline
                .prepare_function_checked(func, Some(proof_ctx))
                .map(|(function, _metrics)| sealed.push(function))
        } else {
            pipeline
                .prepare_function_with_metrics(func, Some(proof_ctx))
                .map(|(ir_func, _metrics)| machine.push(ir_func))
        };
        if let Err(error) = prepared {
            phases.push(("prepare", read_counters().since(t)));
            return outcome_error(phases, format!("prepare {}: {error}", func.name));
        }
    }
    phases.push(("prepare", read_counters().since(t)));
    let function_count = if checked { sealed.len() } else { machine.len() };

    let jit = JitCompiler::new(JitConfig {
        opt_level,
        verify: false,
        emit_entry_counters: false,
        ..JitConfig::default()
    });
    let t = read_counters();
    let linked = if checked {
        jit.compile_raw_checked_relocatable(&sealed, &externs)
    } else {
        jit.compile_raw_relocatable(&machine, &externs)
    };
    phases.push(("link", read_counters().since(t)));
    let (buffer, image) = match linked {
        Ok(linked) => linked,
        Err(error) => return outcome_error(phases, format!("link: {error}")),
    };
    let output = match &image {
        Ok(image) => {
            let bytes = image.to_bytes();
            let ranges: Vec<Value> = image
                .function_ranges()
                .iter()
                .map(|(name, range)| json!([name, range.start, range.end]))
                .collect();
            json!({
                "image_sha256": sha256_hex(&image.image_sha256()),
                "serialized_sha256": sha256_hex(&bytes),
                "code_len": image.code_len(),
                "function_ranges": ranges,
            })
        }
        Err(refusal) => json!({
            "relocatable_refusal": refusal.as_str(),
            "allocated_size": buffer.allocated_size(),
        }),
    };
    drop(buffer);
    ModuleOutcome {
        record: json!({"verdict": "ok", "functions": function_count, "output": output}),
        phases,
        lir_prepare: Some(lir_prepare),
    }
}

/// The compiler's own JIT lane (`Compiler::compile_module_to_jit`): the typed
/// JIT an embedding runtime reaches through `Compiler` (ay's JIT kernels, TY's
/// typed-host lane), in the JIT-latency configuration at the module's level,
/// serial, against the fake externs. Its sealed link skips a final-stream
/// check preparation already passed (`TCG_NO_SEALED_JIT_LINK` restores it;
/// the bytes must not change). Output identity: the published code bytes
/// (absolute only in the fake extern literals, which are constant here) and,
/// when the module places globals, the data image's address-free manifest; a
/// code site addressing the image depends on where the kernel placed it, so
/// such a module is recorded with `data_image_sites` for the reader.
fn lane_jit_compiler(unit: &CorpusModule, entry: &Entry) -> ModuleOutcome {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = unit.opt_level;
    config.parallel = false;
    config.panic_unwind = unit.panic_unwind;
    let compiler =
        Compiler::new(config).with_codegen_license(trust_cg_jit_matrix::bench_corpus_license());
    let externs = fake_externs(&unit.module, entry);
    let t = read_counters();
    let compiled = compiler.compile_module_to_jit(&unit.module, &externs);
    let phases = vec![("compile", read_counters().since(t))];
    match compiled {
        Ok(result) => {
            let code = result.buffer.code_slice();
            let mut symbols: Vec<(String, u64)> = result
                .buffer
                .symbols()
                .map(|(name, offset)| (name.to_string(), offset))
                .collect();
            symbols.sort();
            let data_image = result.buffer.data_image().map(|record| {
                json!({
                    "manifest_sha256": &record.manifest_sha256,
                    "image_len": record.image_len,
                    "direct_sites": record.direct_site_count,
                    "got_slots": record.got_slot_count,
                })
            });
            ModuleOutcome {
                record: json!({
                    "verdict": "ok",
                    "functions": result.per_function_metrics.len(),
                    "output": {
                        "code_sha256": sha256_hex(code),
                        "code_len": code.len(),
                        "symbols": symbols,
                        "data_image": data_image,
                    },
                }),
                phases,
                lir_prepare: None,
            }
        }
        Err(error) => outcome_error(phases, format!("compile: {error}")),
    }
}

/// The AOT object lane (Compiler::compile), serial, proof certificates off
/// (`aot-object`) or on (`aot-proofs`, the rustc bridge's production setting).
fn lane_aot(unit: &CorpusModule, emit_proofs: bool) -> ModuleOutcome {
    let config = CompilerConfig {
        opt_level: unit.opt_level,
        target: unit.target,
        emit_proofs,
        panic_unwind: unit.panic_unwind,
        eh_frames_cannot_unwind: unit.eh_frames_cannot_unwind,
        eh_nounwind_callees: unit.eh_nounwind_callees.clone(),
        link_unit_definitions: unit.link_unit_definitions.clone(),
        never_inline: unit.never_inline.clone(),
        parallel: false,
        ..CompilerConfig::default()
    };
    let compiler =
        Compiler::new(config).with_codegen_license(trust_cg_jit_matrix::bench_corpus_license());
    let t = read_counters();
    let compiled = compiler.compile(&unit.module);
    let phases = vec![("compile", read_counters().since(t))];
    match compiled {
        Ok(result) => ModuleOutcome {
            record: json!({
                "verdict": "ok",
                "output": {
                    "object_sha256": sha256_hex(&result.object_code),
                    "object_len": result.object_code.len(),
                },
            }),
            phases,
            lir_prepare: None,
        },
        Err(error) => outcome_error(phases, format!("compile: {error}")),
    }
}

/// Classify one function's composed transition record (L09-P3) into the
/// census tallies: outside the legalization check's domain (no TrustIR-to-
/// bytes claim exists; a proof-required route publishes it on its other
/// gates), composed, or refused, which is what a proof-required route's
/// requirement refuses. Up to five refusal texts are kept per module.
fn census_record(
    function: &str,
    record: Option<&trust_cg_verify::composed_transition::TransitionRecord>,
    counts: &mut std::collections::BTreeMap<String, u64>,
    refusals: &mut Vec<String>,
) {
    use trust_cg_codegen::composed_transition::require_composition;
    let mut bump = |key: String| *counts.entry(key).or_default() += 1;
    bump("functions".to_string());
    match require_composition(function, record) {
        Ok(None) => {
            let reason = record
                .and_then(|record| record.not_composed.as_ref())
                .map(|why| why.reason.chars().take(48).collect::<String>())
                .unwrap_or_default();
            bump("not_covered".to_string());
            bump(format!("not_covered/{reason}"));
        }
        Ok(Some(composed)) => {
            bump("composed".to_string());
            bump(format!("composed/pass_runs={}", composed.pass_runs.min(9)));
        }
        Err(refusal) => {
            bump("refused".to_string());
            bump(format!(
                "refused/{}/{}",
                refusal.class(),
                refusal.stage().map_or("-", |stage| stage.as_str())
            ));
            if refusals.len() < 5 {
                refusals.push(refusal.to_string().chars().take(400).collect());
            }
        }
    }
}

/// The composed transition census lane (L09-P3). An entry the JIT lanes
/// compile is translated as `jit-raw` translates it and each function is
/// prepared the way a proof-grade route prepares it (a pipeline with
/// proof-grade publication, the module's own TrustIR attached). An entry the
/// object lanes compile goes through `Compiler::compile` itself (dialect
/// legalization, the object adapter, LIR inlining) with
/// `TRUST_CG_COMPOSED_TRANSITION=record`, certificates off, and its records
/// come back in the compile's metrics; each composing function's record is
/// then held to the object publication binding an `--emit-proofs` object
/// applies (`published`, or `publication_refused/<class>`). Each record is
/// classified by [`census_record`]. The JIT-lane entries measure composition
/// only: no buffer is installed, so no publication binding runs for them.
/// Measurement only: no proof is run and no route's own check is exercised.
fn lane_composed_census(unit: &CorpusModule, entry: &Entry) -> ModuleOutcome {
    let module = &unit.module;
    let mut phases = Vec::new();
    if unit.target != Target::Aarch64 {
        return outcome_error(phases, "composed-census: not an AArch64 module".to_string());
    }
    let mut counts: std::collections::BTreeMap<String, u64> = std::collections::BTreeMap::new();
    let mut refusals = Vec::new();
    if !entry.lanes.iter().any(|lane| lane == "jit-raw") {
        let config = CompilerConfig {
            opt_level: unit.opt_level,
            target: unit.target,
            emit_proofs: false,
            panic_unwind: unit.panic_unwind,
            eh_frames_cannot_unwind: unit.eh_frames_cannot_unwind,
            eh_nounwind_callees: unit.eh_nounwind_callees.clone(),
            link_unit_definitions: unit.link_unit_definitions.clone(),
            never_inline: unit.never_inline.clone(),
            parallel: false,
            ..CompilerConfig::default()
        };
        let compiler =
            Compiler::new(config).with_codegen_license(trust_cg_jit_matrix::bench_corpus_license());
        let t = read_counters();
        let compiled = trust_cg_codegen::env_lock::with_env_overrides(
            &[("TRUST_CG_COMPOSED_TRANSITION", "record")],
            || compiler.compile(module).map_err(|error| error.to_string()),
        );
        phases.push(("compile", read_counters().since(t)));
        return match compiled {
            Ok(result) => {
                for record in &result.metrics.composed_transitions {
                    census_record(&record.function, Some(record), &mut counts, &mut refusals);
                }
                // The publication binding an `--emit-proofs` object applies,
                // run on this record-policy object: each composing function's
                // symbol extent must be exactly its chain's terminal bytes,
                // with no relocation inside.
                for record in &result.metrics.composed_transitions {
                    if !matches!(
                        trust_cg_codegen::composed_transition::require_composition(
                            &record.function,
                            Some(record)
                        ),
                        Ok(Some(_))
                    ) {
                        continue;
                    }
                    let records = [(record.function.as_str(), Some(record))];
                    match trust_cg_codegen::composed_transition::require_object_publication(
                        &result.object_code,
                        &records,
                    ) {
                        Ok(0) => {}
                        Ok(_) => *counts.entry("published".to_string()).or_default() += 1,
                        Err(refusal) => {
                            *counts
                                .entry(format!("publication_refused/{}", refusal.class()))
                                .or_default() += 1;
                            if refusals.len() < 5 {
                                refusals.push(refusal.to_string().chars().take(400).collect());
                            }
                        }
                    }
                }
                ModuleOutcome {
                    record: json!({
                        "verdict": "ok",
                        "route": "aot-object (record policy)",
                        "composed_transitions": counts,
                        "claim": counts.contains_key("composed").then_some(
                            trust_cg_verify::composed_transition::ComposedTransition::CLAIM,
                        ),
                        "refusals": refusals,
                    }),
                    phases,
                    lir_prepare: None,
                }
            }
            Err(error) => outcome_error(phases, format!("compile: {error}")),
        };
    }
    let t = read_counters();
    let translated = (|| -> Result<_, String> {
        let prepared = prepare_module_for_lir(module, GuardCarrierArch::AArch64)
            .map_err(|e| format!("adapter preparation: {e}"))?;
        let (functions, _validation) = prepared
            .translate_with_tls_and_validation_with_license(
                TlsDialect::default(),
                &trust_cg_jit_matrix::bench_corpus_license(),
            )
            .map_err(|e| format!("adapter translation: {e}"))?;
        Ok((prepared, functions))
    })();
    phases.push(("adapter", read_counters().since(t)));
    let (prepared, functions) = match translated {
        Ok(translated) => translated,
        Err(error) => return outcome_error(phases, error),
    };
    let lowered = prepared.module();
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: unit.opt_level,
        verify: false,
        target_triple: host_triple().to_owned(),
        ..Default::default()
    })
    .with_proof_grade_aarch64_publication();
    let t = read_counters();
    for (func, proof_ctx) in &functions {
        let source = lowered
            .functions
            .iter()
            .find(|candidate| candidate.name == func.name && !candidate.blocks.is_empty());
        let prepared = match source {
            Some(source) => pipeline.prepare_function_with_metrics_and_trust_ir_module(
                func,
                Some(proof_ctx),
                lowered,
                source,
            ),
            None => pipeline.prepare_function_with_metrics(func, Some(proof_ctx)),
        };
        match prepared {
            Ok((_, metrics)) => census_record(
                &func.name,
                metrics.composed_transition.as_ref(),
                &mut counts,
                &mut refusals,
            ),
            Err(error) => {
                *counts.entry("preparation_error".to_string()).or_default() += 1;
                if refusals.len() < 5 {
                    refusals.push(format!(
                        "preparation of {}: {}",
                        func.name,
                        error.to_string().chars().take(300).collect::<String>()
                    ));
                }
            }
        }
    }
    phases.push(("prepare", read_counters().since(t)));
    ModuleOutcome {
        record: json!({
            "verdict": "ok",
            "route": "jit-raw adapter, proof-grade preparation (composition only, no publication)",
            "composed_transitions": counts,
            "claim": counts.contains_key("composed").then_some(
                trust_cg_verify::composed_transition::ComposedTransition::CLAIM,
            ),
            "refusals": refusals,
        }),
        phases,
        lir_prepare: None,
    }
}

/// Compile every module of an entry through one lane.
fn run_lane(lane: &str, units: &[CorpusModule], entry: &Entry) -> anyhow::Result<Value> {
    let start = read_counters();
    let before = frame_net_snapshot();
    let mut modules = Vec::with_capacity(units.len());
    let mut phases: Vec<(&'static str, Counters)> = Vec::new();
    let mut lir_prepare = Vec::new();
    let mut all_ok = true;
    for unit in units {
        let outcome = match lane {
            "jit-raw" => lane_jit_raw(unit, entry, false),
            "jit-raw-checked" => lane_jit_raw(unit, entry, true),
            "jit-compiler" => lane_jit_compiler(unit, entry),
            "aot-object" => lane_aot(unit, false),
            "aot-proofs" => lane_aot(unit, true),
            "composed-census" => lane_composed_census(unit, entry),
            other => bail!("entry {}: unknown lane {other:?}", entry.name),
        };
        all_ok &= outcome.record["verdict"] == "ok";
        for (name, counters) in outcome.phases {
            match phases.iter_mut().find(|(n, _)| *n == name) {
                Some((_, acc)) => {
                    acc.instructions += counters.instructions;
                    acc.cycles += counters.cycles;
                }
                None => phases.push((name, counters)),
            }
        }
        if let Some(mut prep) = outcome.lir_prepare {
            if let Some(object) = prep.as_object_mut() {
                object.insert("module".into(), json!(unit.name));
            }
            lir_prepare.push(prep);
        }
        let mut record = outcome.record;
        if let Some(object) = record.as_object_mut() {
            object.insert("module".into(), json!(unit.name));
        }
        modules.push(record);
    }
    let after = frame_net_snapshot();
    let phases: serde_json::Map<String, Value> = phases
        .into_iter()
        .map(|(name, counters)| (name.to_string(), json!(counters)))
        .collect();
    Ok(json!({
        "verdict": if all_ok { "ok" } else { "error" },
        "modules": modules,
        "frame_net": frame_net_delta(&after, &before),
        "phases": phases,
        "lir_prepare": lir_prepare,
        "total": read_counters().since(start),
    }))
}

// ---------------------------------------------------------------------------
// Commands
// ---------------------------------------------------------------------------

fn run(
    manifest_path: &Path,
    only_entries: &[String],
    only_lanes: &[String],
    reps: usize,
    opt_level_override: Option<&str>,
) -> anyhow::Result<Value> {
    let opt_level_override = opt_level_override.map(parse_opt_level).transpose()?;
    let text = std::fs::read_to_string(manifest_path)
        .with_context(|| format!("read {}", manifest_path.display()))?;
    let manifest: Manifest = serde_json::from_str(&text).context("parse manifest")?;
    if manifest.schema != MANIFEST_SCHEMA {
        bail!(
            "manifest schema {:?}, expected {MANIFEST_SCHEMA:?}",
            manifest.schema
        );
    }
    let base = manifest_path
        .parent()
        .map(Path::to_path_buf)
        .unwrap_or_default();
    for name in only_entries {
        if !manifest.entries.iter().any(|entry| &entry.name == name) {
            bail!("no corpus entry named {name:?}");
        }
    }
    let mut results = Vec::new();
    for entry in &manifest.entries {
        if !only_entries.is_empty() && !only_entries.contains(&entry.name) {
            continue;
        }
        let t = read_counters();
        let mut units = load_entry_modules(&base, entry)?;
        let load = read_counters().since(t);
        if let Some(level) = opt_level_override {
            for unit in &mut units {
                unit.opt_level = level;
            }
        }
        let mut lanes = serde_json::Map::new();
        // An on-request lane runs only when `--lane` names it, on the entries
        // that list its base lane; a default run (and so every committed
        // baseline) is unchanged.
        let on_request = ON_REQUEST_LANES.iter().filter(|(lane, base)| {
            only_lanes.iter().any(|l| l == lane) && entry.lanes.iter().any(|l| l == base)
        });
        let mut lane_names: Vec<String> = entry.lanes.to_vec();
        for (lane, _) in on_request {
            if !lane_names.iter().any(|name| name == lane) {
                lane_names.push((*lane).to_string());
            }
        }
        for lane in &lane_names {
            if !only_lanes.is_empty() && !only_lanes.contains(lane) {
                continue;
            }
            let mut repetitions = Vec::with_capacity(reps);
            for _ in 0..reps.max(1) {
                repetitions.push(run_lane(lane, &units, entry)?);
            }
            lanes.insert(lane.clone(), Value::Array(repetitions));
        }
        results.push(json!({
            "name": entry.name,
            "origin": entry.origin,
            "file": entry.file,
            "opt_level": entry.opt_level,
            "compiled_opt_level": opt_level_override.map(opt_level_label),
            "modules": units.len(),
            "module_functions": units.iter().map(|u| u.module.functions.len()).sum::<usize>(),
            "load": load,
            "lanes": lanes,
        }));
    }
    Ok(json!({
        "schema": RESULT_SCHEMA,
        "counter_source": COUNTER_SOURCE,
        "host_triple": host_triple(),
        "reps": reps.max(1),
        "opt_level_override": opt_level_override.map(opt_level_label),
        "entries": results,
    }))
}

fn dump_builtin(name: &str, out: &Path) -> anyhow::Result<()> {
    use trust_cg_jit_matrix::bcp_module_builder as bcp;
    let module = match name {
        "bcp-propagate" => bcp::build_bcp_propagate_module(),
        "bcp-propagate-with-decisions" => bcp::build_bcp_propagate_with_decisions_module(),
        "bcp-watched-literal" => bcp::build_bcp_propagate_watched_literal_module(),
        "bcp-watched-literal-chunked" => bcp::build_bcp_propagate_watched_literal_chunked_module(),
        "parent-loop" => {
            trust_cg_jit_matrix::parent_loop_module_builder::build_parent_loop_module()
        }
        other => bail!("unknown builtin module {other:?}"),
    }
    .map_err(|fault| anyhow!("builtin module {name:?}: the builder refused: {fault}"))?;
    let bytes = trust_ir::binary::serialize_module(&module)
        .map_err(|refusal| anyhow!("builtin module {name:?} has no wire image: {refusal}"))?;
    std::fs::write(out, bytes).with_context(|| format!("write {}", out.display()))
}

fn rebin(input: &Path, out: &Path) -> anyhow::Result<()> {
    let bytes = std::fs::read(input).with_context(|| format!("read {}", input.display()))?;
    let module =
        load_module_from_bytes(&bytes).map_err(|e| anyhow!("decode {}: {e}", input.display()))?;
    let bytes = trust_ir::binary::serialize_module(&module)
        .map_err(|refusal| anyhow!("{} has no wire image: {refusal}", input.display()))?;
    std::fs::write(out, bytes).with_context(|| format!("write {}", out.display()))
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Command::Run {
            manifest,
            entries,
            lanes,
            reps,
            opt_level,
            out,
        } => {
            let result = run(&manifest, &entries, &lanes, reps, opt_level.as_deref())?;
            let text = serde_json::to_string_pretty(&result)?;
            match out {
                Some(path) => std::fs::write(&path, text + "\n")
                    .with_context(|| format!("write {}", path.display()))?,
                None => println!("{text}"),
            }
        }
        Command::DumpBuiltin { module, out } => dump_builtin(&module, &out)?,
        Command::Rebin { input, out } => rebin(&input, &out)?,
    }
    Ok(())
}
