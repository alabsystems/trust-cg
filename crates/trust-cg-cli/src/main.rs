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
use std::process;

use clap::parser::ValueSource;
use clap::{CommandFactory, FromArgMatches, Parser, ValueEnum};
use rayon::prelude::*;
use trust_cg_codegen::jit_diagnostics::sha256_hex;

use trust_cg_codegen::compiler::{CompilationResult, Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::jit::{JitExternalSymbolResolutionPolicy, ProfileHookMode};
use trust_cg_codegen::link_driver::{
    self, LinkError, LinkOutputKind, LinkRequest, PositionIndependence,
};
use trust_cg_codegen::resource_limits;
use trust_cg_codegen::runtime_deps::RuntimeDependencyManifest;
use trust_cg_codegen::{
    CodegenLicensePolicy, CompileArtifactCacheConfig, CompileArtifactCacheTelemetry,
    RelocationModel, UnlicensedPermitException,
};

mod ay_identity_report;
mod emit_proofs;
use trust_cg_codegen::pipeline::{self, FormatMode, OptLevel};
use trust_cg_codegen::target::{
    Target, TargetOperatingSystem, TargetSpec, TargetSpecParseErrorKind,
};
use trust_cg_codegen::wasm;
use trust_cg_verify::AYConfig;
use trust_cg_verify::fsym_summary::{
    FsymSolverEscalationConfig, FsymSolverEscalationResult, FsymSolverStatus, FsymSummary,
};
use trust_cg_verify::fsym_trust_ir::{
    FsymTrustIrDiagnosticKind, FsymTrustIrReport, FsymTrustIrSeverity, FsymTrustIrSkipReason,
    FsymUbClassStatus, scan_module as scan_fsym_trust_ir,
};

/// Input format selector for the CLI `--format` flag.
///
/// Binary `.tmbc` is the default; JSON is a debug opt-in, and the
/// human-readable `.trust_ir` text format was added in #413.
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
        riscv64 (scaffold), wasm32-unknown-unknown (closed-module .wasm via \
        the wasm backend; raw module bytes written to -o).\n\n\
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
    /// Multiple files use bounded parallelism when worthwhile and are linked
    /// together unless `-c` requests separate object files.
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

    /// Print, as one JSON object on stdout, which AY this build admits and
    /// exit: 0 when an AY is admitted, 1 when the identity rule refuses.
    ///
    /// The answer is the rule every solver call in this binary applies: an
    /// absolute `AY_SOLVER_PATH`, else the build toolchain's `bin/ay`,
    /// admitted only when the SHA-256 of its bytes equals the digest recorded
    /// when trust-cg-verify was built. No AY is executed to decide it. A
    /// script that runs an AY itself must obtain admission here first.
    #[arg(long = "print-ay-identity", conflicts_with_all = ["inputs", "input_json"])]
    print_ay_identity: bool,

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

    /// Optimization level (0-3).
    ///
    /// On `--target wasm32-unknown-unknown` the level selects the lane's two
    /// optimizations, the trust-ir mid-end and the local emission pass: at
    /// -O0 neither runs and every function is emitted with the lowering's own
    /// (baseline) body, byte for byte; at -O1, -O2 (the default) and -O3 the
    /// mid-end keeps each rewrite its checker accepts (otherwise the input
    /// is lowered), and each function's rewritten body is used where the
    /// per-function translation validator accepts it, and its baseline body
    /// otherwise. -O1, -O2 and -O3 run the same passes on this lane.
    #[arg(
        short = 'O',
        long = "opt-level",
        value_parser = parse_opt_level,
        default_value = "2"
    )]
    opt_level: OptLevel,

    /// Target architecture or triple. x86 support is x86_64 only:
    /// x86/i386/i486/i586/i686 aliases and triples are rejected.
    ///
    /// `wasm32-unknown-unknown` (alias `wasm32`) routes through the wasm
    /// backend: the output is the raw `.wasm` module bytes written to `-o`,
    /// and object-file/linker options are refused with named diagnostics.
    #[arg(long = "target", value_parser = parse_cli_target, default_value = "aarch64")]
    target: CliTarget,

    /// Compile only -- produce object files, do not link. On the wasm32 lane
    /// each input becomes a relocatable wasm object (`<input>.o`) for
    /// `wasm-ld`.
    #[arg(short = 'c')]
    compile_only: bool,

    /// The `wasm-ld` used to link several wasm32 inputs (default:
    /// `$WASM_LD`, else `wasm-ld`, else `rust-lld`, on PATH). A linker
    /// whose file name is the generic `rust-lld` / `lld` driver is run with
    /// `-flavor wasm`, however it was found.
    #[arg(long = "wasm-ld", value_name = "PATH")]
    wasm_ld: Option<PathBuf>,

    /// Whole-program `panic=unwind` object emission (x86-64 Mach-O and ELF).
    ///
    /// Mirrors the rustc-bridge `CompilerConfig::panic_unwind` plumbing for
    /// the CLI front door: every function of an emitted x86-64 object gets
    /// walkable unwind coverage with the all-filler "keep walking, never
    /// dispatch" LSDA for pass-through frames (Mach-O: compact unwind and a
    /// zPLR FDE per frame-covered function; ELF: `.gcc_except_table`, a zPLR
    /// `.eh_frame` FDE per function and the `DW.ref` personality slot), so a
    /// panic raised in one object can unwind THROUGH sibling objects that
    /// carry no local landing pad. Without this, phase-1 unwind stops dead
    /// (`_URC_END_OF_STACK`) at the first pass-through frame, skipping every
    /// cleanup Drop and the `catch_unwind` handler. AArch64 and x86-64 COFF
    /// output is byte-identical with or without this flag. Exception tables
    /// carry no proof obligation, so with proof certificates on an x86-64
    /// Mach-O or ELF compile under this flag is refused (`[TCG-EH-UNPROVED]`);
    /// a certified x86-64 COFF compile is refused either way, by its
    /// relocation inventory. Default off: abort-model objects stay
    /// byte-identical.
    #[arg(long = "panic-unwind")]
    panic_unwind: bool,

    /// ELF relocation model for native objects: `static` (like `-fno-pic`),
    /// `pie` (`-fPIE`) or `pic` (`-fPIC`, shared objects). Without this
    /// flag a `--shared` link to an AArch64 Linux target compiles its
    /// modules `pic` (the model a shared object's preemptible definitions
    /// need; ruling OD-SHARED-PIC-DEFAULT-20261024), and every other compile
    /// uses `static`. An explicit `static` or `pie` in a `--shared` link is
    /// kept, and on Linux the link is refused by name when a module defines
    /// a symbol with default visibility (`[TCG-LINK-PREEMPTIBLE-DEFINITION]`:
    /// such code inlines and folds its own uses of it, which interposition
    /// would not reach) or addresses one directly
    /// (`[TCG-LINK-PREEMPTIBLE-DIRECT]`); a module whose every definition is
    /// local, hidden or protected links. The same holds for the `static`
    /// objects of an x86-64 or RISC-V Linux `--shared` link, the one model
    /// those targets implement.
    ///
    /// `pic` loads the address of every preemptible (default-visibility,
    /// non-local) definition from the GOT, keeps calls to them as `CALL26`
    /// relocations the linker routes through the PLT, and reaches
    /// thread-locals through TLS descriptors. `static` and `pie` address
    /// definitions PC-relatively and use local-exec (definitions) or
    /// initial-exec (imports) TLS. Implemented for AArch64 ELF targets only;
    /// every other target refuses `pie` and `pic`.
    #[arg(
        long = "relocation-model",
        value_name = "MODEL",
        value_parser = parse_relocation_model
    )]
    relocation_model: Option<RelocationModel>,
    /// Emit every function in its own `.text.<symbol>` section on AArch64
    /// ELF targets (`-ffunction-sections`), so `ld --gc-sections` can drop
    /// unused functions individually.
    ///
    /// Sets `CompilerConfig::function_sections`, which the compile policy
    /// (Artifact partition) and the object-cache identity record. Mach-O
    /// (atom-granular dead stripping already) and x86-64 ignore it. Default
    /// off: one `.text`, byte-identical to before.
    #[arg(long = "function-sections")]
    function_sections: bool,
    /// Explicit AArch64 optional-ISA admission for object emission, as a
    /// comma-separated list of exactly the admitted features (`fp16`,
    /// `lse`, `dotprod`) or `none`.
    ///
    /// Replaces the target contract (Apple arm64: LSE, DotProd and FP16;
    /// generic Linux: none), so it is the only way a generic Linux object
    /// admits FEAT_FP16 scalar half-precision arithmetic. Sets
    /// `CompilerConfig::aarch64_isa_profile`, which the compile policy
    /// (Artifact partition) and the object-cache identity record. The CPU
    /// that runs the object must implement the listed features; nothing here
    /// checks it. Refused for non-AArch64 targets.
    #[arg(long = "aarch64-isa-features", value_name = "LIST")]
    aarch64_isa_features: Option<trust_cg_codegen::target::AArch64IsaProfile>,

    /// Recognize an additional trust-ir v41 codegen-license gate AUTHORITY.
    ///
    /// A function whose `body_gate` is `gated "<authority>"` is compiled only
    /// when `<authority>` is recognized; every other gated body is refused,
    /// and an `ungated` body is refused unconditionally. `clean-kernel-tv`
    /// (the Clean compiler's kernel translation-validation gate) is always
    /// recognized — and it is EVIDENCE-BOUND: its body compiles only with the
    /// kernel-replayed TranslationValidation certificate the module carries
    /// for it and the license's `GateEvidence` (trust-ir v61), whatever the
    /// flags say. Repeatable. Applies to the native and wasm32 lanes and to
    /// `--profile-generate` JIT capture.
    #[arg(long = "recognize-authority", value_name = "NAME", action = clap::ArgAction::Append)]
    recognize_authority: Vec<String>,

    /// Compile function bodies that carry NO codegen license (`body_gate`
    /// absent — the pre-v41 grandfather state), which are REFUSED by default.
    ///
    /// For legacy pre-v41 corpora only: every such blob decodes to no
    /// license. Each compile under this flag prints a disclosure line naming
    /// the unlicensed bodies it admitted. An `ungated` body, an unrecognized
    /// authority, and a gated body without its evidence stay refused.
    #[arg(long = "permit-unlicensed", conflicts_with = "refuse_unlicensed")]
    permit_unlicensed: bool,

    /// Authenticate the inputs' cross-crate imports against this dependency
    /// trust_ir module (repeatable; read with the inputs' `--format`).
    ///
    /// Without `--link`, a module whose proof certificate inherits its
    /// evidence from another module (`InheritedFromCallee` with an import) is
    /// refused: a single-module compile cannot authenticate it. With
    /// `--link`, each input is first validated together with the supplied
    /// dependencies by trust-ir's linked validator: EVERY import row must
    /// match a supplied module's stable digest (a rebuilt dependency is a
    /// `DigestMismatch`), every call to an imported declaration must bind a
    /// definition with a structurally identical signature, and every
    /// dependency must itself validate. Any refusal stops the compile. On
    /// success the backend admits exactly the inheritances that
    /// authenticated; they remain data, and no codegen decision reads them.
    ///
    /// The digest authenticates the dependency MODULE, not the object file a
    /// later link binds. With `--emit-proofs`, every authenticated
    /// `(name, digest, producer)` is written to `linked_dependencies.json` so
    /// the link step can bind the object to its module. Native lanes only.
    #[arg(long = "link", value_name = "DEP", action = clap::ArgAction::Append)]
    link: Vec<PathBuf>,

    /// Refuse a function body that carries NO codegen license. This is the
    /// DEFAULT; the flag is accepted as an explicit spelling of it.
    #[arg(long = "refuse-unlicensed")]
    refuse_unlicensed: bool,

    /// Emit DWARF debug info sections in the output.
    #[arg(short = 'g')]
    debug_info: bool,

    /// Library search paths passed to the linker (-L <dir>).
    #[arg(short = 'L', value_name = "DIR")]
    lib_paths: Vec<PathBuf>,

    /// Libraries to link (-l <name>).
    #[arg(short = 'l', value_name = "LIB")]
    libs: Vec<String>,

    /// Link a shared object instead of an executable (cc `-shared`; on
    /// Darwin `-dynamiclib`). Also spelled `-shared`.
    #[arg(long = "shared")]
    shared: bool,

    /// Link a position-independent executable (cc `-pie`). Also spelled `-pie`.
    #[arg(long = "pie", conflicts_with = "no_pie")]
    pie: bool,

    /// Link a position-dependent executable (cc `-no-pie`; refused on
    /// Darwin). Also spelled `-no-pie`.
    #[arg(long = "no-pie")]
    no_pie: bool,

    /// Link statically (cc `-static`; refused on Darwin). Also spelled `-static`.
    #[arg(long = "static")]
    static_link: bool,

    /// Do not link the C runtime, C library or compiler support library (cc
    /// `-nostdlib`); every runtime dependency must then be supplied by an
    /// input or `-l`. Also spelled `-nostdlib`.
    #[arg(long = "nostdlib")]
    nostdlib: bool,

    /// Shared-object soname (ELF DT_SONAME; Darwin install name). Requires
    /// `--shared`. Also spelled `-soname <NAME>`.
    #[arg(long = "soname", value_name = "NAME")]
    soname: Option<String>,

    /// Run-time library search path (ELF DT_RUNPATH; Darwin LC_RPATH).
    /// Repeatable. Also spelled `-rpath <DIR>`.
    #[arg(long = "rpath", value_name = "DIR", action = clap::ArgAction::Append)]
    rpath: Vec<String>,

    /// Linker passthrough, spelled `-Wl,<arg>[,<arg>...]` as with cc.
    /// Repeatable. Options with a typed trust-cg flag (output kind, PIE,
    /// static, soname, rpath, -o), response files, `-z execstack` and the
    /// BTI/PAC requests `-z force-bti`, `-z pac-plt` and `-z bti-report`
    /// (trust-cg emits no BTI landing pads or PAC) are refused.
    #[arg(
        short = 'W',
        value_name = "l,ARGS",
        action = clap::ArgAction::Append,
        allow_hyphen_values = true
    )]
    linker_passthrough: Vec<String>,

    /// After an aarch64-apple-darwin link, write the linked-image evidence
    /// record `<output>.linked-image.json`: every object relocation outside
    /// `__LD,__compact_unwind` replayed against the linked executable or
    /// dylib, its fixups, import ordinals (against libSystem's SDK stub and
    /// the export lists of `-l` libraries found as `lib<name>.dylib` or
    /// `.tbd` in the `-L` directories or the SDK) and read-only-after-fixup
    /// placement bound. Image content from an input this compile did not
    /// produce (a `-Wl` object or archive member) and a dependent dylib no
    /// bind uses are refused. When the replay disagrees the linked output is
    /// removed and the link fails; any link removes a record an earlier
    /// link left next to its output. Replay evidence, not a proof.
    #[arg(long = "linked-image-evidence")]
    linked_image_evidence: bool,

    /// Write each object's runtime-dependency manifest (undefined symbols
    /// grouped by providing runtime: memory intrinsics, libc, libm, compiler
    /// support library, unwinder, EH personality, TLS runtime, external) as
    /// JSON to this path.
    #[arg(long = "emit-runtime-deps", value_name = "PATH")]
    emit_runtime_deps: Option<PathBuf>,

    /// Emit proof certificates to the given directory (issue #421).
    ///
    /// When set, the compiler requires proof promotion for every instruction
    /// and every emitted object relocation. If that full authority gate passes,
    /// it writes one `.smt2` (SMT-LIB2 query) plus one `.cert` (JSON metadata)
    /// file per verified rule, organised under
    /// `<dir>/<ProofCategory>/<proof_name>.{smt2,cert}`. It also writes
    /// per-function `.lowering.json` and `.trust-proof-cert.json` sidecars.
    /// With multiple inputs, each module uses `<dir>/input_<index>/` so
    /// identically named private functions keep separate certificates.
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

    /// Keep the historical x86-64 code generation in a compile without
    /// `--emit-proofs`.
    ///
    /// By default an x86-64 object compile that emits no proof certificates
    /// requests the certificate-free code-quality policy
    /// (`CompilerConfig::x86_certificate_free_allocation`: the register
    /// allocation changes, frameless leaves, the O2 fixpoint and the
    /// certificate-free IMUL reductions), what the rustc bridge uses with
    /// `no-proof-certs`. This flag withdraws that request. A compile with
    /// `--emit-proofs` never gets it.
    #[arg(long = "no-x86-certificate-free-allocation")]
    no_x86_certificate_free_allocation: bool,

    /// Enable compilation trace output (per-phase timing).
    #[arg(long = "trace")]
    trace: bool,

    /// Print compilation metrics as JSON to stderr.
    #[arg(long = "metrics")]
    metrics: bool,

    /// Disable parallel input-file and per-function compilation.
    ///
    /// The default uses bounded worker pools when there is sufficient work.
    /// This flag makes both input-file and module compilation sequential.
    #[arg(long = "no-parallel")]
    no_parallel: bool,

    /// Enable CEGIS superoptimization with the given per-function budget
    /// in seconds (e.g. `--cegis-superopt=5`). Off by default.
    ///
    /// When set, the compiler runs the CEGIS-based superoptimization pass
    /// on each function. The budget is wall-clock time for solver-backed
    /// verifications only: its clock starts at the function's first
    /// solver-backed query, and no further query starts once it has
    /// elapsed. If candidates are still unverified then, the compile fails
    /// with a CegisIncomplete error rather than emit a partial result.
    /// Results are keyed into a compilation cache so repeat compilations
    /// reuse proven rewrites. See issue #395.
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

fn parse_relocation_model(s: &str) -> Result<RelocationModel, String> {
    s.parse()
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
             aliases x86-64 and x64), riscv64, wasm32-unknown-unknown (alias \
             wasm32), x86_64-unknown-linux-gnu, x86_64-pc-windows-msvc, \
             x86_64-apple-darwin"
        ),
    })
}

/// A `--target` request: either a register-machine native spec, or the wasm32
/// stack-machine lane.
///
/// WebAssembly is deliberately not a [`Target`] variant (see
/// `trust_cg_codegen::wasm::target`): it is recognized here, at the dispatch
/// boundary, and routed to `trust_cg_codegen::wasm::compile_module` instead of
/// the native object pipeline.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CliTarget {
    /// aarch64 / x86-64 / riscv64 — the native object/linker pipeline.
    Native(TargetSpec),
    /// wasm32-unknown-unknown — the closed-module wasm backend; the output is
    /// the raw `.wasm` module bytes written to `-o`.
    Wasm32,
}

/// The wasm32 spellings the CLI accepts: the canonical triple and the bare
/// architecture alias (matching the aarch64/x86_64 alias convention).
fn parse_cli_target(s: &str) -> Result<CliTarget, String> {
    let normalized = s.trim().to_ascii_lowercase();
    if wasm::is_wasm32_target(&normalized) {
        return match normalized.as_str() {
            "wasm32" | "wasm32-unknown-unknown" => Ok(CliTarget::Wasm32),
            other => Err(format!(
                "unsupported wasm target '{other}': the wasm backend is the closed-module \
                 wasm32-unknown-unknown lane (no WASI or emscripten imports); use \
                 --target wasm32-unknown-unknown (alias wasm32)"
            )),
        };
    }
    parse_target(s).map(CliTarget::Native)
}

/// The result of compiling a single input file.
struct FileCompilationResult {
    /// Path to the generated .o file.
    object_path: PathBuf,
    /// Canonical tMBC bytes for the loaded input module.
    trust_ir_bytes: Vec<u8>,
    /// The compilation result from the compiler.
    result: CompilationResult,
    /// Under `--link` (WS7.9): every import row of the input that the linked
    /// walk authenticated, for the `--emit-proofs` sidecar.
    linked_dependencies: Option<Vec<trust_cg_codegen::LinkedDependency>>,
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
/// Positional inputs use `--format`; the deprecated `--input-json` path
/// always selects JSON. Clap prevents combining the two input forms.
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

/// The first input read as `.trust_ir` TEXT under `format`: every input under
/// `--format=text`, and under `--format=auto` an input the legacy sniffing
/// classifies as text. `None` when no input is text.
fn text_format_input(format: FormatMode, inputs: &[PathBuf]) -> Option<&Path> {
    match format {
        FormatMode::Text => inputs.first().map(PathBuf::as_path),
        FormatMode::Auto => inputs
            .iter()
            .find(|input| pipeline::detect_input_format(input) == pipeline::InputFormat::TrustIr)
            .map(PathBuf::as_path),
        FormatMode::Tmbc | FormatMode::Json => None,
    }
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
fn temp_object_path(directory: &Path, index: usize) -> PathBuf {
    directory.join(format!("input_{index}.o"))
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
) -> Result<(), String> {
    if mode == FsymModeArg::Off {
        return Ok(());
    }

    let report = scan_fsym_trust_ir(module);
    let severity = match mode {
        FsymModeArg::Off => return Ok(()),
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
        )?;
    }

    if rejected {
        if solver_concrete_ub == 0 {
            return Err(format!(
                "--fsym=error rejected '{}' before codegen ({} concrete UB diagnostic(s), {} deref-coverage error(s))",
                input.display(),
                report.diagnostics.len(),
                report.coverage_errors.len(),
            ));
        } else {
            return Err(format!(
                "--fsym=error rejected '{}' before codegen ({} concrete UB diagnostic(s), {} solver concrete UB result(s), {} deref-coverage error(s))",
                input.display(),
                report.diagnostics.len(),
                solver_concrete_ub,
                report.coverage_errors.len(),
            ));
        }
    }
    Ok(())
}

fn write_fsym_preflight_report(path: &Path, report: &serde_json::Value) -> Result<(), String> {
    serde_json::to_string_pretty(report)
        .map_err(|e| e.to_string())
        .and_then(|json| fs::write(path, json).map_err(|e| e.to_string()))
        .map_err(|error| {
            format!(
                "failed to write fsym preflight JSON report to '{}': {error}",
                path.display()
            )
        })
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
        // Which runs a clean verdict is about: trust-ir reference-interpreter
        // runs within this bound, on entry arguments carrying no pointer
        // naming an allocation and no runtime handle. No other run is claimed.
        // (Since trust-ir v50 the interpreter has no memory budget.)
        "run_model": {
            "fuel_below": report.run_model().fuel_limit,
            "entry_arguments": "no pointer naming an allocation, no runtime handle",
        },
        // What a clean verdict is about: every UB class, and whether fsym
        // checks it (a `NotChecked` class says why a scanned function cannot
        // contain it).
        // `interpreter_sites` counts the places trust-ir's reference
        // interpreter raises UB of the class (`fsym_ub_map`).
        "ub_classes": report.ub_classes().iter().map(|class| {
            let kind = match class.status {
                FsymUbClassStatus::Checked(kind) => Some(fsym_diagnostic_kind_name(kind)),
                FsymUbClassStatus::NotChecked => None,
            };
            let interpreter_sites = trust_cg_verify::fsym_ub_map::fsym_sites_per_class()
                .into_iter()
                .find(|(name, _)| *name == class.name)
                .map_or(0, |(_, sites)| sites);
            serde_json::json!({
                "name": class.name,
                "checked": kind.is_some(),
                "kind": kind,
                "detail": class.detail,
                "interpreter_sites": interpreter_sites,
            })
        }).collect::<Vec<_>>(),
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
        FsymTrustIrDiagnosticKind::Overlap => "overlap",
        FsymTrustIrDiagnosticKind::UnsummarizedCall => "unsummarized-call",
        FsymTrustIrDiagnosticKind::InvalidFree => "invalid-free",
        FsymTrustIrDiagnosticKind::PointerArithmetic => "pointer-arithmetic",
        FsymTrustIrDiagnosticKind::Misaligned => "misaligned",
        FsymTrustIrDiagnosticKind::Uninitialized => "uninitialized-read",
        FsymTrustIrDiagnosticKind::UnreachableReached => "unreachable-reached",
        FsymTrustIrDiagnosticKind::ScanBound => "scan-bound",
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
        FsymTrustIrSkipReason::PointerWidth => "pointer-width",
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

#[allow(clippy::too_many_arguments)]
fn run_profile_generate_jit(
    module: &trust_ir::Module,
    trust_ir_bytes: &[u8],
    config: &CompilerConfig,
    target_spec: TargetSpec,
    codegen_license: &CodegenLicensePolicy,
    out: &Path,
    supplied_inputs: Option<&[u64]>,
) -> Result<(), String> {
    if config.target != Target::host() {
        return Err(format!(
            "--profile-generate JIT capture requires target {} to match host {}",
            config.target.name(),
            Target::host().name(),
        ));
    }
    // The JIT capture runs on the host and emits no Mach-O object, so a macOS
    // deployment target does not take part in the host comparison.
    let host_comparable = target_spec
        .with_default_os_abi()
        .without_apple_deployment_target();
    if target_spec.has_explicit_os_abi() && host_comparable != TargetSpec::host() {
        return Err(format!(
            "--profile-generate JIT capture requires target triple {} to match host triple {}",
            host_comparable.triple(),
            TargetSpec::host().triple(),
        ));
    }

    let target = select_profile_run_target(module, supplied_inputs)
        .map_err(|error| format!("--profile-generate: {error}"))?;

    let extern_symbols = std::collections::HashMap::new();
    // The capture is an in-process JIT compile, not an object compile: the
    // certificate-free allocation request is an object-compile control and is
    // refused at the closed-JIT proof-grade boundary, so it is never carried
    // into the JIT.
    let jit_config = CompilerConfig {
        x86_certificate_free_allocation: false,
        ..config.clone()
    };
    let jit = Compiler::new(jit_config)
        .with_codegen_license(codegen_license.clone())
        .compile_module_to_jit_with_profile_hooks(
            module,
            &extern_symbols,
            ProfileHookMode::BlockCounts,
        )
        .map_err(|error| format!("--profile-generate JIT capture failed: {error}"))?;

    let observation = invoke_profile_target(&jit.buffer, &target)
        .map_err(|error| format!("--profile-generate: {error}"))?;

    let profile_key = pgo_cache_key(trust_ir_bytes, config, target_spec);
    let profile = jit.buffer.block_profdata_with_key(&profile_key);

    trust_cg_opt::pgo::write_to_path(&profile, out)
        .map_err(|error| format!("cannot write profile '{}': {error}", out.display()))?;
    emit_profile_generate_report(&profile, out, &target, &observation);

    eprintln!(
        "trust-cg: --profile-generate: ran {} call(s) through '{}' and wrote {} function profile(s) -> {}",
        target.call_count(),
        target.name,
        profile.functions.len(),
        out.display(),
    );
    Ok(())
}

/// The trust-ir v41 codegen-license policy the CLI flags select: the default
/// recognized set (`clean-kernel-tv`, evidence-bound) plus every
/// `--recognize-authority`, REFUSING claim-less bodies (the default, DG-73)
/// unless `--permit-unlicensed` names the legacy-corpus exception.
fn codegen_license_policy(cli: &Cli) -> CodegenLicensePolicy {
    let mut policy = CodegenLicensePolicy::default();
    for authority in &cli.recognize_authority {
        policy = policy.with_recognized_authority(authority.clone());
    }
    if cli.permit_unlicensed {
        policy =
            policy.with_unlicensed_permit_exception(UnlicensedPermitException::LegacyCorpusFlag);
    }
    policy
}

/// The disclosure `--permit-unlicensed` owes: the bodies of `module` (read
/// from `input`) that compile only because the flag permits claim-less
/// bodies. Printed to stderr before the compile; nothing when there are none.
fn disclose_unlicensed_bodies(
    policy: &CodegenLicensePolicy,
    module: &trust_ir::Module,
    input: &Path,
) {
    let permitted = policy.unlicensed_bodies_permitted(module);
    if permitted.is_empty() {
        return;
    }
    eprintln!(
        "trust-cg: note: --permit-unlicensed: '{}': compiling {} function bod{} with NO codegen \
         license (`body_gate` absent, the pre-v41 grandfather state; refused by default): {}",
        input.display(),
        permitted.len(),
        if permitted.len() == 1 { "y" } else { "ies" },
        permitted.join(", ")
    );
}

/// Build a CompilerConfig from CLI flags for a native target spec.
fn build_config(cli: &Cli, target_spec: TargetSpec) -> CompilerConfig {
    CompilerConfig {
        opt_level: cli.opt_level,
        target: target_spec.architecture,
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
        jit_external_symbol_resolution: JitExternalSymbolResolutionPolicy::default(),
        // Whole-program panic=unwind: default abort model; `--panic-unwind`
        // opts the x86-64 Mach-O emitter into full walkable FDE coverage for
        // pass-through frames (the rustc bridge derives the same bit from
        // `tcx.sess.panic_strategy()`).
        panic_unwind: cli.panic_unwind,
        relocation_model: effective_relocation_model(cli, target_spec),
        function_sections: cli.function_sections,
        aarch64_isa_profile: cli.aarch64_isa_features,
        aarch64_force_frame_pointers: false,
        never_inline: Default::default(),
        eh_frames_cannot_unwind: false,
        eh_nounwind_callees: Default::default(),
        link_unit_definitions: Default::default(),
        x86_certificate_free_allocation: cli_requests_x86_certificate_free_allocation(
            cli,
            target_spec,
        ),
    }
}

/// Whether an object compile through the CLI requests the certificate-free
/// x86-64 allocation (`CompilerConfig::x86_certificate_free_allocation`).
///
/// The CLI is trust-cg's production ahead-of-time front door (a TrustIR
/// module to an object), and it installs no process policy. TY at
/// `f76a29357f` does not invoke it: TY compiles in process through
/// `CompilerConfig::for_host_jit()`, which installs nothing and so keeps
/// every certificate-free change off (`X86AllocationQuality::Installed`).
/// A compile without
/// `--emit-proofs` keeps no proof certificates, so it requests the
/// allocation the rustc bridge installs for `no-proof-certs`; a compile with
/// `--emit-proofs` does not request it (and `Compiler::compile` would
/// withhold it anyway, `X86AllocationQuality::Withheld`). Only x86-64 targets
/// request it, so no other target's compile-policy digest changes.
/// `--no-x86-certificate-free-allocation` opts out (the historical
/// allocation). The in-process JIT capture of `--profile-generate` never
/// carries the request ([`run_profile_generate_jit`]).
fn cli_requests_x86_certificate_free_allocation(cli: &Cli, target_spec: TargetSpec) -> bool {
    target_spec.architecture == Target::X86_64
        && cli.emit_proofs.is_none()
        && !cli.no_x86_certificate_free_allocation
}

/// The relocation model a native compile uses: the explicit
/// `--relocation-model`; else `pic` when the invocation links a shared
/// object (`--shared`) for an AArch64 Linux target, the one object path that
/// implements `pic` and whose shared objects export default-visibility
/// definitions preemptibly; else `static`, the only model every other object
/// path accepts (ruling OD-SHARED-PIC-DEFAULT-20261024). A Linux shared
/// link of `static` or `pie` objects is refused by the link driver when they
/// define a default-visibility symbol (`[TCG-LINK-PREEMPTIBLE-DEFINITION]`,
/// the model is stated in [`build_link_request`]), address one directly
/// (`[TCG-LINK-PREEMPTIBLE-DIRECT]`) or use local-exec TLS
/// (`[TCG-LINK-TLS-MODEL]`).
fn effective_relocation_model(cli: &Cli, target_spec: TargetSpec) -> RelocationModel {
    if let Some(model) = cli.relocation_model {
        return model;
    }
    let target = target_spec.with_default_os_abi();
    if cli.shared
        && target.architecture == Target::Aarch64
        && target.operating_system == TargetOperatingSystem::Linux
    {
        RelocationModel::Pic
    } else {
        RelocationModel::Static
    }
}

fn build_config_for_input_count(
    cli: &Cli,
    input_count: usize,
    target_spec: TargetSpec,
) -> CompilerConfig {
    let mut config = build_config(cli, target_spec);
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

fn pgo_cache_key(
    trust_ir_bytes: &[u8],
    config: &CompilerConfig,
    target_spec: TargetSpec,
) -> trust_cg_opt::CacheKey {
    trust_cg_codegen::pgo_cache_key(trust_ir_bytes, config, target_spec)
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
    fsym_mode: FsymModeArg,
    fsym_solver: FsymSolverArg,
    fsym_report_json: Option<&Path>,
    profile_use: Option<&trust_cg_opt::pgo::ProfData>,
    profile_use_path: Option<&Path>,
    profile_generate: Option<&Path>,
    profile_generate_inputs: Option<&[u64]>,
    compile_artifact_cache: Option<&CompileArtifactCacheConfig>,
    codegen_license: &CodegenLicensePolicy,
    link_dependencies: Option<&[trust_ir::Module]>,
) -> Result<FileCompilationResult, String> {
    // Load the trust_ir module using the explicit format selection (#414).
    let module = pipeline::load_module_as(input, format).map_err(|error| {
        format!(
            "failed to read trust_ir module from '{}': {error}",
            input.display()
        )
    })?;
    // `--link` (WS7.9): authenticate every import row against the supplied
    // dependencies before anything else reads the module; the compile then
    // admits exactly the cross-crate inheritances that authenticated.
    let linked_license;
    let (codegen_license, linked_dependencies) = match link_dependencies {
        None => (codegen_license, None),
        Some(dependencies) => {
            let imports = trust_cg_codegen::authenticate_linked_imports(&module, dependencies)
                .map_err(|refusal| {
                    format!(
                        "--link: the imports of '{}' were not authenticated: {refusal}",
                        input.display()
                    )
                })?;
            let rows = imports.dependencies().to_vec();
            linked_license = codegen_license.clone().with_authenticated_imports(imports);
            (&linked_license, Some(rows))
        }
    };
    run_fsym_preflight(input, &module, fsym_mode, fsym_solver, fsym_report_json)?;

    let trust_ir_bytes = pipeline::encode_tmbc(&module).map_err(|error| {
        format!(
            "failed to encode canonical tMBC for '{}': {error}",
            input.display()
        )
    })?;

    if let Some(profile) = profile_use {
        let profile_key = pgo_cache_key(&trust_ir_bytes, config, target_spec);
        trust_cg_opt::pgo::enforce_fresh(profile, &profile_key).map_err(|error| {
            format!("--profile-use is stale for '{}': {error}", input.display())
        })?;
        emit_profile_use_report(
            profile,
            profile_use_path,
            profile_use_enables_optimization(config.opt_level),
        );
    }

    // Compile. The trust-ir v41 codegen license is enforced by the compiler
    // before any cache lookup and again inside the adapter.
    disclose_unlicensed_bodies(codegen_license, &module, input);
    let mut compiler = Compiler::new_for_target_spec(config.clone(), target_spec)
        .with_codegen_license(codegen_license.clone());
    if let Some(profile) =
        profile_use.filter(|_| profile_use_enables_optimization(config.opt_level))
    {
        compiler = compiler.with_profile_use(profile.clone());
    }
    if let Some(cache) = compile_artifact_cache {
        compiler = compiler.with_compile_artifact_cache(cache.clone());
    }
    let result = compiler
        .compile(&module)
        .map_err(|error| format!("compilation of '{}' failed: {error}", input.display()))?;

    if let Some(out) = profile_generate {
        run_profile_generate_jit(
            &module,
            &trust_ir_bytes,
            config,
            target_spec,
            codegen_license,
            out,
            profile_generate_inputs,
        )?;
    }

    Ok(FileCompilationResult {
        object_path: obj_path.to_path_buf(),
        trust_ir_bytes,
        result,
        linked_dependencies,
    })
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
/// Missing compiler certificates are reported on stderr. Certification and
/// destination-alias errors propagate to the driver before any proof writes.
fn emit_proof_artifacts(
    dir: &Path,
    result: &CompilationResult,
    target_spec: TargetSpec,
    trust_ir_bytes: &[u8],
    compiler_config_bytes: &[u8],
    protected_paths: &[PathBuf],
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
            protected_paths,
        },
    )
    .map(Some)
}

/// Print proof certificates for a compilation result.
///
/// Certificates are grouped by function, in first-appearance order. Each group
/// opens with the WS7.2 disclosure line
/// ([`trust_cg_verify::proof_certificate::TRUST_IR_TO_LIR_NOT_COVERED`]): every
/// rule below it relates LIR to machine code, and the trust-ir -> LIR adapter
/// is outside that boundary (F-111: an adapter miscompile still earned three
/// `[VERIFIED]` rules). No function-level `VERIFIED` is ever printed, because
/// no certificate trust-cg produces covers trust-ir -> machine (WS7.16); the
/// per-rule status keeps its exact grade.
fn print_proofs(result: &CompilationResult) {
    if let Some(ref proofs) = result.proofs {
        eprint!("{}", render_proofs(proofs));
    }
}

/// The text [`print_proofs`] writes to stderr.
fn render_proofs(proofs: &[trust_cg_codegen::compiler::ProofCertificate]) -> String {
    use std::fmt::Write as _;
    use trust_cg_verify::proof_certificate::{CoveredSpan, TRUST_IR_TO_LIR_NOT_COVERED};

    let mut out = String::new();
    if proofs.is_empty() {
        out.push_str("trust-cg: note: proof emission enabled but no certificates produced\n");
        return out;
    }
    out.push_str("--- proof certificates ---\n");
    if trust_cg_codegen::MUTATION_KNOBS {
        out.push_str(
            "  trust-cg: warning: this build carries test-only mutation knobs; \
             its certificates are not a release claim\n",
        );
    }
    let mut functions: Vec<&str> = Vec::new();
    for cert in proofs {
        if !functions.contains(&cert.function_name.as_str()) {
            functions.push(&cert.function_name);
        }
    }
    let span = CoveredSpan::LirToMachine;
    debug_assert!(!span.covers_trust_ir_to_lir());
    for function in functions {
        let _ = writeln!(out, "  [{function}] {TRUST_IR_TO_LIR_NOT_COVERED}");
        for cert in proofs.iter().filter(|cert| cert.function_name == function) {
            let status = if cert.verified {
                "VERIFIED"
            } else {
                "UNVERIFIED"
            };
            let _ = writeln!(out, "    {} [{status}] ({span})", cert.rule_name);
        }
    }
    out.push_str("--- end proofs ---\n");
    out
}

/// Print compilation metrics for a compilation result, including the object's
/// runtime-dependency manifest (or the reason it could not be read).
fn print_metrics(result: &CompilationResult) {
    let metrics_json = serde_json::json!({
        "code_size_bytes": result.metrics.code_size_bytes,
        "instruction_count": result.metrics.instruction_count,
        "function_count": result.metrics.function_count,
        "optimization_passes_run": result.metrics.optimization_passes_run,
        // WS7.2: whether this binary carries the test-only mutation knobs
        // (`trust_cg_lower::mutation_knobs`). A release build never does.
        "mutation_knobs": trust_cg_codegen::MUTATION_KNOBS,
        "compile_artifact_cache": cache_telemetry_json(
            &result.compile_artifact_cache_telemetry
        ),
        "runtime_dependencies": runtime_dependencies_json(&result.object_code),
        "dialect_legalization": result
            .dialect_legalization
            .as_ref()
            .map(trust_cg_codegen::dialect_legalization::DialectLegalizationReport::to_json),
    });
    eprintln!("{}", serde_json::to_string_pretty(&metrics_json).unwrap());
}

/// The runtime-dependency manifest of one emitted object as JSON, or an
/// `error` object naming why its symbol table could not be read.
fn runtime_dependencies_json(object: &[u8]) -> serde_json::Value {
    match RuntimeDependencyManifest::from_object(object) {
        Ok(manifest) => manifest.to_json(),
        Err(error) => serde_json::json!({ "error": error.to_string() }),
    }
}

/// Write the `--emit-runtime-deps` report: one manifest per emitted object.
/// An object whose symbol table cannot be read fails the report closed.
fn write_runtime_deps_report(
    path: &Path,
    entries: &[(PathBuf, PathBuf, &[u8])],
) -> Result<(), String> {
    let mut objects = Vec::with_capacity(entries.len());
    for (input, object_path, object) in entries {
        let manifest = RuntimeDependencyManifest::from_object(object).map_err(|error| {
            format!(
                "--emit-runtime-deps: cannot read '{}': {error}",
                object_path.display()
            )
        })?;
        objects.push(serde_json::json!({
            "input": input.display().to_string(),
            "object": object_path.display().to_string(),
            "manifest": manifest.to_json(),
        }));
    }
    let report = serde_json::json!({
        "schema": trust_cg_codegen::runtime_deps::RUNTIME_DEPENDENCY_SCHEMA,
        "objects": objects,
    });
    let text = serde_json::to_string_pretty(&report)
        .map_err(|error| format!("--emit-runtime-deps: {error}"))?;
    fs::write(path, text + "\n").map_err(|error| {
        format!(
            "--emit-runtime-deps: cannot write '{}': {error}",
            path.display()
        )
    })
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

/// cc-compatible single-dash spellings of the typed link options. clap has no
/// single-dash long options, so these exact tokens are rewritten to their
/// double-dash forms before parsing (never after `--` and never when the
/// token is the value of a preceding option).
const CC_LINK_SPELLINGS: &[(&str, &str)] = &[
    ("-shared", "--shared"),
    ("-pie", "--pie"),
    ("-no-pie", "--no-pie"),
    ("-static", "--static"),
    ("-nostdlib", "--nostdlib"),
    ("-soname", "--soname"),
    ("-rpath", "--rpath"),
];

/// Every `-x` / `--long` spelling of an option that takes a separate value.
fn options_taking_values() -> std::collections::BTreeSet<String> {
    let command = Cli::command();
    let mut options = std::collections::BTreeSet::new();
    for arg in command.get_arguments() {
        if arg.is_positional() || !arg.get_action().takes_values() {
            continue;
        }
        if let Some(short) = arg.get_short() {
            options.insert(format!("-{short}"));
        }
        if let Some(long) = arg.get_long() {
            options.insert(format!("--{long}"));
        }
    }
    options
}

/// Rewrite the cc-compatible single-dash link spellings (see
/// [`CC_LINK_SPELLINGS`]) to the double-dash options clap parses.
fn normalize_cc_link_spellings(
    args: impl IntoIterator<Item = std::ffi::OsString>,
) -> Vec<std::ffi::OsString> {
    let value_options = options_taking_values();
    let mut normalized = Vec::new();
    let mut expecting_value = false;
    let mut after_terminator = false;
    for (index, arg) in args.into_iter().enumerate() {
        if index == 0 || after_terminator || expecting_value {
            expecting_value = false;
            normalized.push(arg);
            continue;
        }
        let Some(text) = arg.to_str() else {
            normalized.push(arg);
            continue;
        };
        if text == "--" {
            after_terminator = true;
            normalized.push(arg);
            continue;
        }
        let spelled = CC_LINK_SPELLINGS
            .iter()
            .find(|(single, _)| *single == text)
            .map(|(_, double)| *double)
            .unwrap_or(text);
        expecting_value = value_options.contains(spelled);
        normalized.push(spelled.into());
    }
    normalized
}

/// The typed link options present on the command line, by flag name.
fn requested_link_options(cli: &Cli) -> Vec<&'static str> {
    let mut flags = Vec::new();
    for (flag, present) in [
        ("--shared", cli.shared),
        ("--pie", cli.pie),
        ("--no-pie", cli.no_pie),
        ("--static", cli.static_link),
        ("--nostdlib", cli.nostdlib),
        ("--soname", cli.soname.is_some()),
        ("--rpath", !cli.rpath.is_empty()),
        ("-Wl", !cli.linker_passthrough.is_empty()),
        ("--linked-image-evidence", cli.linked_image_evidence),
    ] {
        if present {
            flags.push(flag);
        }
    }
    flags
}

/// Build the validated system-link request for this invocation, or every
/// named refusal (fail-closed; no option is dropped).
fn build_link_request(
    cli: &Cli,
    objects: Vec<PathBuf>,
    output: PathBuf,
    target_spec: TargetSpec,
) -> Result<LinkRequest, Vec<String>> {
    let mut refusals = Vec::new();
    let mut request = LinkRequest::executable(target_spec, objects, output);
    if cli.shared {
        request.kind = LinkOutputKind::SharedLibrary;
    }
    request.position_independence = if cli.pie {
        PositionIndependence::Pie
    } else if cli.no_pie {
        PositionIndependence::NoPie
    } else {
        PositionIndependence::DriverDefault
    };
    request.static_link = cli.static_link;
    request.nostdlib = cli.nostdlib;
    request.soname = cli.soname.clone();
    request.rpaths = cli.rpath.clone();
    request.lib_paths = cli.lib_paths.clone();
    request.libs = cli.libs.clone();
    // Every positional object is one this invocation compiles, under this
    // model: the driver refuses a shared object whose `static` or `pie`
    // objects define a default-visibility symbol
    // ([`link_driver::non_pic_definition_refusals`]).
    request.compiled_relocation_model = Some(effective_relocation_model(cli, target_spec));
    for value in &cli.linker_passthrough {
        match value.strip_prefix("l,") {
            Some(args) => match link_driver::parse_wl_group(args, target_spec) {
                Ok(group) => request.linker_arg_groups.push(group),
                Err(refusal) => refusals.push(refusal.to_string()),
            },
            None => refusals.push(format!(
                "-W{value}: only the -Wl,<arg>[,<arg>...] linker passthrough is accepted"
            )),
        }
    }
    refusals.extend(request.refusals().iter().map(ToString::to_string));
    if cli.linked_image_evidence {
        let target = target_spec.with_default_os_abi();
        if target.operating_system != TargetOperatingSystem::Darwin
            || target.architecture != Target::Aarch64
        {
            refusals.push(format!(
                "--linked-image-evidence: only aarch64-apple-darwin Mach-O images are replayed, \
                 not {}",
                target.triple()
            ));
        }
    }
    if refusals.is_empty() {
        Ok(request)
    } else {
        Err(refusals)
    }
}

/// Invoke the system linker for `request`. On failure the linker's own
/// stderr is reproduced, followed by one classified `error[link:<kind>]`
/// line per diagnostic. Inputs refused before the linker runs (local-exec
/// TLS in a shared object) print one `error[link:<kind>]` line each and no
/// linker output.
///
/// The link driver stages a link whose AArch64 ELF inputs carry a
/// local-exec TLS relocation or a GOT-page `ADRP` relocation
/// (`R_AARCH64_ADR_GOT_PAGE`, `R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21`,
/// `R_AARCH64_TLSDESC_ADR_PAGE21`). Every `pic`, initial-exec or
/// TLS-descriptor object has one. On Linux it stages every link, and runs
/// with the linker's input trace every link that is not a plain
/// `--nostdlib` executable link: every `--shared` link, every link with the
/// C runtime (whose start files carry GOT-page `ADRP`s), every link with a
/// `-l` library or a `-Wl` group, and every link with a positional input the
/// AArch64 ELF reader cannot read (every non-AArch64 link among them). The
/// linker writes into a fresh directory next to the output path,
/// so that directory must be writable, and `-o /dev/null` with such a link
/// is refused. Every staged Linux image is also refused when its
/// `.eh_frame` pointers are not shown to resolve where an unwinder must
/// find them (`[TCG-LINK-EH-FRAME-WINDOW]`, `[TCG-LINK-EH-FRAME-UNPROVEN]`):
/// gold 2.42 and LLD 22.1.6 write an `R_AARCH64_PREL32` value in
/// `[2^31, 2^32)`, which an unwinder reads as negative. The driver reads
/// the `.eh_frame` input where its own link map places it: that map is
/// always written (its `-Map` comes after every `-Wl` group, and the
/// linker is given the driver's path in place of every map path of a `-Wl`
/// group), and a map a `-Wl` group asks for is written from it where that
/// linker would have written it, never to the file the output path names;
/// an image whose map was not written or cannot be read is refused. A
/// static executable with an FDE its `.eh_frame_hdr` table does not locate
/// is refused unless the C driver's own `crtbeginT.o` is the only input that
/// references a registration function and the frames it registers reach
/// that FDE. An image is also refused when it names a program interpreter
/// without a dynamic section (`[TCG-LINK-INTERP-NO-DYNAMIC]`: LLD's dynamic
/// `--nostdlib --no-pie` image, which glibc's loader faults on), when it is
/// an `ET_EXEC` without an interpreter whose dynamic section needs shared
/// libraries or holds dynamic relocations, or a PIE without an interpreter
/// that needs shared libraries or holds dynamic relocations no loaded input
/// relocates (`[TCG-LINK-DYNAMIC-NO-INTERP]`: LLD's `--static` link given
/// `-Wl,-Bdynamic`, a `--pie --nostdlib -Wl,--no-dynamic-linker` program
/// with its own `_start`), and when a `--static` link's image names an
/// interpreter or needs a shared library anyway
/// (`[TCG-LINK-STATIC-DYNAMIC]`). An image refused after the linker ran
/// prints what the link printed on standard error, then one
/// `error[link:<kind>]` line each, and is removed without reaching the
/// output path. Such an image is either local-exec TLS in an image that is
/// not an executable, or an image not shown to keep its GOT-page `ADRP`s
/// within the page window of their slots (or one that cannot be read),
/// where the relocation is in a positional input or in any AArch64 ELF
/// relocatable object the trace names (a `-Wl` operand, a `-l` library, an
/// archive member, a linker script's input or a C runtime start file), or
/// an image whose trace does not show what was loaded when either check
/// needs it (`[TCG-LINK-INPUT-TRACE]`, for example with `-Wl,--verbose`). A
/// successful link that wrote no image (`[TCG-LINK-NO-OUTPUT]`) is refused
/// when an input needs the read-back. Neither touches a file already at the
/// output path.
fn link(request: &LinkRequest) -> Result<(), String> {
    let target_spec = request.target.with_default_os_abi();
    eprintln!(
        "trust-cg: linking {} object file(s) -> {}{}",
        request.objects.len(),
        request.output.display(),
        if request.kind == LinkOutputKind::SharedLibrary {
            " (shared object)"
        } else {
            ""
        },
    );

    match link_driver::run_link(request, "cc") {
        Ok(success) => {
            eprint!("{}", success.stderr);
            Ok(())
        }
        Err(LinkError::Failed(failure)) => {
            eprint!("{}", failure.stderr);
            for diagnostic in &failure.diagnostics {
                eprintln!("trust-cg: {diagnostic}");
            }
            Err(LinkError::Failed(failure).to_string())
        }
        Err(error @ LinkError::Spawn { .. }) => {
            let hint = if target_spec.operating_system == TargetOperatingSystem::Darwin {
                "ensure Xcode command line tools are installed (xcode-select --install)".to_string()
            } else {
                format!(
                    "install a C toolchain capable of linking {} objects",
                    target_spec.triple()
                )
            };
            Err(format!("{error}\n  hint: {hint}"))
        }
        Err(error @ LinkError::Refused(_)) => Err(error.to_string()),
        Err(LinkError::InputRefused(diagnostics)) => {
            for diagnostic in &diagnostics {
                eprintln!("trust-cg: {diagnostic}");
            }
            Err("link inputs refused before the linker ran".to_string())
        }
        Err(LinkError::OutputRefused {
            output,
            staged,
            removed,
            diagnostics,
            stderr,
        }) => {
            eprint!("{stderr}");
            for diagnostic in &diagnostics {
                eprintln!("trust-cg: {diagnostic}");
            }
            Err(format!(
                "the linked output for {} was refused and not installed; {}",
                output.display(),
                if removed {
                    "the linker's image was removed".to_string()
                } else {
                    format!(
                        "the linker's image {} could not be removed and must not be used",
                        staged.display()
                    )
                }
            ))
        }
        Err(
            error @ (LinkError::OutputMissing { .. }
            | LinkError::OutputStaging { .. }
            | LinkError::LinkMap { .. }),
        ) => {
            if let LinkError::OutputMissing { stderr, .. }
            | LinkError::OutputStaging { stderr, .. }
            | LinkError::LinkMap { stderr, .. } = &error
            {
                eprint!("{stderr}");
            }
            Err(error.to_string())
        }
        Err(error @ LinkError::CodeSignature { .. }) => {
            eprintln!("trust-cg: error[link:code-signature]: {error}");
            Err("the linked output failed its code-signature check".to_string())
        }
        Err(error @ LinkError::OutputUnreadable { .. }) => Err(error.to_string()),
    }
}

/// Export lists of the `-l` libraries for the linked-image record: the first
/// `lib<name>.dylib` or `lib<name>.tbd` in the `-L` directories, then the
/// SDK's `usr/lib`. A library found nowhere contributes no list, so a bind
/// the image makes to it refuses the record.
fn link_library_exports(cli: &Cli) -> Vec<trust_cg_codegen::macho::linked_image::ProviderExports> {
    use trust_cg_codegen::macho::linked_image::ProviderExports;
    let sdk_lib = process::Command::new("xcrun")
        .arg("--show-sdk-path")
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| {
            PathBuf::from(String::from_utf8_lossy(&output.stdout).trim()).join("usr/lib")
        });
    let mut providers = Vec::new();
    for lib in &cli.libs {
        let directories = cli.lib_paths.iter().cloned().chain(sdk_lib.clone());
        let found = directories.into_iter().find_map(|directory| {
            let dylib = directory.join(format!("lib{lib}.dylib"));
            if let Ok(bytes) = fs::read(&dylib) {
                return ProviderExports::from_dylib_image(&bytes, dylib.display().to_string()).ok();
            }
            let tbd = directory.join(format!("lib{lib}.tbd"));
            fs::read_to_string(&tbd)
                .ok()
                .and_then(|text| ProviderExports::from_tbd(&text, tbd.display().to_string()).ok())
        });
        providers.extend(found);
    }
    providers
}

/// Named refusals for options that make no sense in the closed-module wasm32
/// lane. Fail-closed: an inapplicable option is refused with a diagnostic
/// naming the flag and the reason — never silently ignored.
///
/// `-c` is deliberately NOT refused: the wasm lane always behaves as
/// compile-only (one module in, raw `.wasm` bytes out, no linker), so `-c`
/// requests exactly what the lane does. IR-level options (`--fsym`,
/// `--emit-json`, `--emit-trust_ir`) also stay usable, and so does `-O`: both
/// wasm routes compile at `cli.opt_level` (see the option's help).
fn wasm32_flag_refusals(cli: &Cli, input_count: usize) -> Vec<String> {
    let mut refusals: Vec<String> = Vec::new();
    let mut refuse = |flag: &str, reason: &str| refusals.push(format!("{flag}: {reason}"));
    // Several inputs without `-c` are compiled to objects and linked by
    // wasm-ld, which takes library paths, libraries and passthrough options.
    let linking = input_count > 1 && !cli.compile_only;
    if cli.wasm_ld.is_some() && !linking {
        refuse(
            "--wasm-ld",
            "the linker only runs when several wasm32 inputs are linked without -c",
        );
    }

    if input_count == 0 {
        refuse(
            "<INPUT>...",
            "the wasm32 lane needs at least one trust_ir module",
        );
    }
    if cli.compile_only && input_count > 1 && cli.output.is_some() {
        refuse(
            "-o/--output",
            "with -c each of several inputs becomes its own object (<input>.o); -o names \
             one file",
        );
    }
    if !cli.link.is_empty() {
        refuse(
            "--link",
            "the wasm32 lane does not consume authenticated imports; a module with a \
             cross-crate inheritance is refused there",
        );
    }
    if !linking && !cli.lib_paths.is_empty() {
        refuse(
            "-L",
            "linker library search paths apply only when several wasm32 inputs are linked \
             (without -c)",
        );
    }
    if !linking && !cli.libs.is_empty() {
        refuse(
            "-l",
            "libraries are linked only when several wasm32 inputs are linked (without -c)",
        );
    }
    for flag in requested_link_options(cli) {
        if flag == "-Wl" && linking {
            continue;
        }
        refuse(
            flag,
            "system-link options do not apply to the wasm32 lane (only -L, -l and -Wl reach \
             wasm-ld when several inputs are linked)",
        );
    }
    if cli.emit_runtime_deps.is_some() {
        refuse(
            "--emit-runtime-deps",
            "runtime-dependency manifests read native object symbol tables; the wasm32 \
             lane emits a closed module with no undefined native symbols",
        );
    }
    if cli.debug_info {
        refuse(
            "-g",
            "DWARF debug-info emission is not wired for the wasm backend",
        );
    }
    if cli
        .relocation_model
        .is_some_and(|model| model != RelocationModel::Static)
    {
        refuse(
            "--relocation-model",
            "the wasm lane emits no native objects, so it has no ELF relocation model",
        );
    }
    if cli.panic_unwind {
        refuse(
            "--panic-unwind",
            "whole-program unwind FDE coverage is an x86-64 Mach-O object concern; \
             the wasm lane emits no native objects",
        );
    }
    if cli.function_sections {
        refuse(
            "--function-sections",
            "function sections are an ELF object-layout policy; the wasm lane emits \
             no native objects",
        );
    }
    if cli.emit_proofs.is_some() {
        refuse(
            "--emit-proofs",
            "the wasm lane emits no proof certificates (its verification route is \
             not_run per the compile-evidence summary); refusing rather than writing \
             an empty proof directory",
        );
    }
    if cli.profile_generate.is_some() {
        refuse(
            "--profile-generate",
            "PGO capture is the native host-JIT path; the wasm lane has no JIT",
        );
    }
    if cli.profile_use.is_some() {
        refuse(
            "--profile-use",
            "profile-guided optimization is the native pipeline; the wasm lane's \
             optimizations (its trust-ir mid-end and local emission pass) read no profile",
        );
    }
    if cli.cegis_superopt.is_some() {
        refuse(
            "--cegis-superopt",
            "CEGIS superoptimization is native-only; the wasm lane's optimizations are \
             its trust-ir mid-end and local emission pass",
        );
    }
    if cli.compile_artifact_cache.is_some() {
        refuse(
            "--compile-artifact-cache",
            "the compile artifact cache is keyed to the native object pipeline",
        );
    }
    if cli.trace {
        refuse(
            "--trace",
            "per-phase compilation tracing is not implemented for the wasm lane",
        );
    }
    if cli.metrics {
        refuse(
            "--metrics",
            "native compilation metrics are not produced by the wasm lane; the \
             compile-evidence summary on stderr carries the module facts",
        );
    }
    refusals
}

/// The `.wasm` destination for the wasm32 lane: `-o` when given, else the
/// input path with a `.wasm` extension.
fn wasm_output_path(cli: &Cli, input: &Path) -> PathBuf {
    cli.output.clone().unwrap_or_else(|| {
        // `-c` emits a relocatable object; otherwise the (closed or linked)
        // module.
        input.with_extension(if cli.compile_only { "o" } else { "wasm" })
    })
}

/// Identity key for an artifact path, so aliased spellings of one file
/// (`out.json`, `./out.json`, `dir/../out.json`) compare equal.
///
/// An existing path canonicalizes directly. A path that does not exist yet —
/// the normal case for an output — canonicalizes through its parent
/// directory, which is the part that can be resolved, and the file name is
/// appended verbatim. If neither resolves, retain the supplied spelling before
/// applying the host's output naming policy.
///
/// On macOS and Windows, CLI output names are conservatively compared without
/// case distinctions, including before files exist. This portability rule also
/// rejects case-only distinctions on case-sensitive volumes on those hosts.
fn output_alias_key(path: &Path) -> PathBuf {
    if let Ok(canonical) = path.canonicalize() {
        return output_alias_case_key(canonical);
    }
    let parent = match path.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => parent,
        _ => Path::new("."),
    };
    output_alias_case_key(match (parent.canonicalize(), path.file_name()) {
        (Ok(dir), Some(name)) => dir.join(name),
        _ => path.to_path_buf(),
    })
}

fn output_alias_case_key(path: PathBuf) -> PathBuf {
    #[cfg(any(target_os = "macos", windows))]
    {
        match path.to_str() {
            Some(path) => PathBuf::from(path.to_lowercase()),
            None => PathBuf::from(path.as_os_str().to_ascii_lowercase()),
        }
    }
    #[cfg(not(any(target_os = "macos", windows)))]
    {
        path
    }
}

/// Named refusals for output paths that alias — an output that
/// names an input, or two requested outputs that name one file.
///
/// Fail-closed for the same reason the flag refusals are: writing an artifact
/// over the input module destroys the module the compile must read, and two
/// requests resolving to one file mean one of them is silently lost. Both are
/// refused by name before anything is read or written.
///
/// Paths are compared by [`output_alias_key`], so `out.json`, `./out.json` and
/// `dir/../out.json` are recognised as one file even before it exists.
fn output_alias_refusals(requested: &[(&str, &Path)], inputs: &[PathBuf]) -> Vec<String> {
    let keys: Vec<PathBuf> = requested
        .iter()
        .map(|(_, path)| output_alias_key(path))
        .collect();
    let input_keys: Vec<PathBuf> = inputs.iter().map(|path| output_alias_key(path)).collect();

    // Canonical paths cover symlinks and not-yet-created outputs. Existing
    // hard links need filesystem identity as well: distinct paths may still
    // name the same file and be truncated by the writer.
    let aliases = |left: &Path, right: &Path, left_key: &Path, right_key: &Path| {
        left_key == right_key || same_file::is_same_file(left, right).unwrap_or(false)
    };
    let mut refusals = Vec::new();
    for (i, (label, path)) in requested.iter().enumerate() {
        for (input, input_key) in inputs.iter().zip(&input_keys) {
            if aliases(path, input, &keys[i], input_key) {
                refusals.push(format!(
                    "{label}: '{}' is the input module '{}'; writing it would destroy the \
                     module this compile reads (give the artifact its own path)",
                    path.display(),
                    input.display(),
                ));
            }
        }
    }
    for i in 0..requested.len() {
        for j in (i + 1)..requested.len() {
            if aliases(requested[i].1, requested[j].1, &keys[i], &keys[j]) {
                refusals.push(format!(
                    "{}: '{}' is also written by {}; two requested outputs naming one file \
                     would clobber each other (give each its own path)",
                    requested[i].0,
                    requested[i].1.display(),
                    requested[j].0,
                ));
            }
        }
    }
    refusals
}

fn auxiliary_output_paths(cli: &Cli) -> Vec<(&str, &Path)> {
    let mut requested = Vec::new();
    for (label, path) in [
        ("--emit-json", cli.emit_json.as_deref()),
        ("--emit-trust_ir", cli.emit_trust_ir.as_deref()),
        ("--fsym-report-json", cli.fsym_report_json.as_deref()),
        ("--profile-generate", cli.profile_generate.as_deref()),
        ("--emit-runtime-deps", cli.emit_runtime_deps.as_deref()),
    ] {
        if let Some(path) = path {
            requested.push((label, path));
        }
    }
    requested
}

fn native_output_alias_refusals(cli: &Cli, inputs: &[PathBuf]) -> Vec<String> {
    let object_paths: Vec<PathBuf> = if cli.compile_only {
        inputs
            .iter()
            .map(|input| object_path_for(input, cli.output.as_deref(), inputs.len() == 1))
            .collect()
    } else {
        vec![cli.output.clone().unwrap_or_else(|| PathBuf::from("a.out"))]
    };
    let mut requested = auxiliary_output_paths(cli);
    for path in &object_paths {
        requested.push(("-o/--output", path));
    }
    // Profiles are input artifacts too. Check before any round-trip output
    // or preflight report is written, since profile loading happens later.
    let mut protected_inputs = inputs.to_vec();
    if let Some(path) = &cli.profile_use {
        protected_inputs.push(path.clone());
    }
    output_alias_refusals(&requested, &protected_inputs)
}

fn wasm32_output_alias_refusals(cli: &Cli, inputs: &[PathBuf]) -> Vec<String> {
    // A missing / multi-input invocation is already refused by name; the
    // default output path is only defined for the single-input lane.
    let Some(first_input) = inputs.first() else {
        return Vec::new();
    };
    let out_path = wasm_output_path(cli, first_input);

    let mut requested = auxiliary_output_paths(cli);
    requested.push((
        if cli.output.is_some() {
            "-o/--output"
        } else {
            "-o/--output (defaulted to <INPUT>.wasm)"
        },
        out_path.as_path(),
    ));

    output_alias_refusals(&requested, inputs)
}

/// Load one trust_ir module for a single-input request, failing closed with
/// the CLI's standard read diagnostic.
fn load_single_input_module(input: &Path, format: FormatMode) -> trust_ir::Module {
    match pipeline::load_module_as(input, format) {
        Ok(m) => m,
        Err(e) => {
            eprintln!(
                "trust-cg: error: failed to read trust_ir module from '{}': {}",
                input.display(),
                e,
            );
            process::exit(1);
        }
    }
}

/// Write the `--emit-json` round-trip artifact for an already-loaded module.
fn write_emit_json_artifact(module: &trust_ir::Module, emit_path: &Path) {
    match serde_json::to_string_pretty(module)
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

/// Write the `--emit-trust_ir` round-trip artifact for an already-loaded
/// module (#413).
fn write_emit_trust_ir_artifact(module: &trust_ir::Module, emit_path: &Path) {
    match pipeline::save_module_to_trust_ir_text(module, emit_path) {
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

/// Compile one trust_ir module through the wasm backend
/// (`--target wasm32-unknown-unknown`).
///
/// The output is the raw `.wasm` module bytes written to `-o` (default: the
/// input path with a `.wasm` extension). The machine-readable
/// [`wasm::WasmCompileEvidence`] summary — naming what ran and what did NOT on
/// this route (verification route: not_run) — is printed to stderr as one
/// `trust-cg: wasm-evidence:` line.
///
/// PUBLICATION ORDER: this lane publishes nothing until the compile has
/// SUCCEEDED. Every refusal (inapplicable options, aliased output paths) fires
/// before the input is read; the module is then loaded ONCE, preflighted, and
/// compiled; only then are the requested artifacts written (`--emit-json`,
/// `--emit-trust_ir`, then the `.wasm` module). A refused invocation and a
/// failed compile — a target-free module, a refused call contract, an fsym
/// rejection — leave the filesystem as they found it, so a partial artifact
/// can never outlive a failed run. The one deliberate exception is
/// `--fsym-report-json`: that report is the record of the preflight itself and
/// is written by the preflight, including when the preflight rejects.
fn run_wasm32_compile(cli: &Cli, inputs: &[PathBuf], format: FormatMode) {
    let mut refusals = wasm32_flag_refusals(cli, inputs.len());
    refusals.extend(wasm32_output_alias_refusals(cli, inputs));
    if !refusals.is_empty() {
        for refusal in &refusals {
            eprintln!("trust-cg: error: --target wasm32-unknown-unknown: {refusal}");
        }
        process::exit(1);
    }
    if cli.compile_only || inputs.len() > 1 {
        run_wasm32_objects(cli, inputs, format);
        return;
    }

    let input = &inputs[0];
    let module = load_single_input_module(input, format);
    if let Err(error) = run_fsym_preflight(
        input,
        &module,
        cli.fsym,
        cli.fsym_solver,
        cli.fsym_report_json.as_deref(),
    ) {
        eprintln!("trust-cg: error: {error}");
        process::exit(1);
    }

    // The closed module owns its memory: sized to hold the static data of the
    // module it emits plus a stack of `WASM_CLOSED_MIN_STACK_BYTES`, never
    // capped, and never less stack than the input module would get (static
    // data the mid-end adds grows the memory). The lane admits the module
    // under the flags' license policy (`--recognize-authority`,
    // `--permit-unlicensed`) and trust-ir's codegen admission, as
    // `compile_one` does on the native lanes, at `-O`'s level.
    let license = codegen_license_policy(cli);
    disclose_unlicensed_bodies(&license, &module, input);
    let compiled = wasm::compile_sized_closed_module_with_evidence_license_optimized(
        &module,
        &license,
        cli.opt_level,
    );
    let (bytes, evidence) = match compiled {
        Ok(compiled) => compiled,
        Err(e) => {
            eprintln!(
                "trust-cg: error: wasm32 compilation of '{}' failed: {}",
                input.display(),
                e,
            );
            process::exit(1);
        }
    };

    // The compile succeeded: publish the requested artifacts, module bytes
    // last.
    if let Some(emit_path) = cli.emit_json.as_deref() {
        write_emit_json_artifact(&module, emit_path);
    }
    if let Some(emit_path) = cli.emit_trust_ir.as_deref() {
        write_emit_trust_ir_artifact(&module, emit_path);
    }

    let out_path = wasm_output_path(cli, input);
    if let Err(e) = fs::write(&out_path, &bytes) {
        eprintln!(
            "trust-cg: error: cannot write '{}': {}",
            out_path.display(),
            e,
        );
        process::exit(1);
    }

    eprintln!("trust-cg: wasm-evidence: {}", evidence.to_json());
    eprintln!(
        "trust-cg: compiled {} function(s), {} bytes -> {} (wasm32-unknown-unknown)",
        evidence.function_count,
        bytes.len(),
        out_path.display(),
    );
}

/// The object and link half of the wasm32 lane: every input becomes a
/// relocatable wasm object (`wasm::compile_object`, at `-O`'s level). With `-c` the objects
/// are the output (`<input>.o`, or `-o` for one input); otherwise they are
/// linked by `wasm-ld` into `-o` (default: the first input with a `.wasm`
/// extension), exporting every
/// default-visibility definition (`--export-dynamic`) with no entry point.
///
/// Like the closed lane, nothing is published until every input compiled.
fn run_wasm32_objects(cli: &Cli, inputs: &[PathBuf], format: FormatMode) {
    let license = codegen_license_policy(cli);
    let mut objects: Vec<(PathBuf, Vec<u8>)> = Vec::with_capacity(inputs.len());
    for input in inputs {
        let module = load_single_input_module(input, format);
        if let Err(error) = run_fsym_preflight(
            input,
            &module,
            cli.fsym,
            cli.fsym_solver,
            cli.fsym_report_json.as_deref(),
        ) {
            eprintln!("trust-cg: error: {error}");
            process::exit(1);
        }
        disclose_unlicensed_bodies(&license, &module, input);
        let (bytes, evidence) = match wasm::compile_object_with_evidence_license_optimized(
            &module,
            &license,
            cli.opt_level,
        ) {
            Ok(compiled) => compiled,
            Err(e) => {
                eprintln!(
                    "trust-cg: error: wasm32 compilation of '{}' failed: {}",
                    input.display(),
                    e,
                );
                process::exit(1);
            }
        };
        if !cli.compile_only
            && let Some(what) = wasm32_link_export_collision(cli, &module)
        {
            eprintln!(
                "trust-cg: error: wasm32 link of '{}' refused: {what}",
                input.display()
            );
            process::exit(1);
        }
        eprintln!("trust-cg: wasm-evidence: {}", evidence.to_json());
        if inputs.len() == 1 {
            if let Some(emit_path) = cli.emit_json.as_deref() {
                write_emit_json_artifact(&module, emit_path);
            }
            if let Some(emit_path) = cli.emit_trust_ir.as_deref() {
                write_emit_trust_ir_artifact(&module, emit_path);
            }
        }
        objects.push((input.clone(), bytes));
    }

    if cli.compile_only {
        for (input, bytes) in &objects {
            let out = match (&cli.output, inputs.len()) {
                (Some(o), 1) => o.clone(),
                _ => input.with_extension("o"),
            };
            if let Err(e) = fs::write(&out, bytes) {
                eprintln!("trust-cg: error: cannot write '{}': {}", out.display(), e);
                process::exit(1);
            }
            eprintln!(
                "trust-cg: compiled {} bytes -> {} (wasm32-unknown-unknown relocatable object)",
                bytes.len(),
                out.display(),
            );
        }
        return;
    }

    let Some(linker) = find_wasm_ld(cli) else {
        eprintln!(
            "trust-cg: error: --target wasm32-unknown-unknown: linking {} inputs needs wasm-ld \
             (pass --wasm-ld <PATH>, set WASM_LD, or put wasm-ld / rust-lld on PATH); \
             use -c to emit the relocatable objects instead",
            inputs.len()
        );
        process::exit(1);
    };
    let out = wasm_output_path(cli, &inputs[0]);
    let dir = match tempfile_dir_near(&out) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("trust-cg: error: cannot create a link directory: {e}");
            process::exit(1);
        }
    };
    let mut cmd = process::Command::new(&linker.0);
    cmd.args(&linker.1);
    // The memory layout rustc gives a wasm32 link: a 1 MiB shadow stack
    // placed BELOW static data (`--stack-first`), so a stack overflow runs
    // off the bottom of linear memory and traps instead of silently
    // overwriting globals. Stated before the `-Wl` passthrough, which may
    // override it.
    cmd.args(["-z", "stack-size=1048576", "--stack-first"]);
    for (i, (_, bytes)) in objects.iter().enumerate() {
        let path = dir.join(format!("input{i}.o"));
        if let Err(e) = fs::write(&path, bytes) {
            eprintln!("trust-cg: error: cannot write '{}': {}", path.display(), e);
            process::exit(1);
        }
        cmd.arg(path);
    }
    for dir in &cli.lib_paths {
        cmd.arg("-L").arg(dir);
    }
    for lib in &cli.libs {
        cmd.arg(format!("-l{lib}"));
    }
    for value in &cli.linker_passthrough {
        let Some(args) = value.strip_prefix("l,") else {
            eprintln!(
                "trust-cg: error: -W{value}: only the -Wl,<arg>[,<arg>...] linker passthrough \
                 is accepted"
            );
            process::exit(1);
        };
        cmd.args(args.split(','));
    }
    cmd.args(["--no-entry", "--export-dynamic", "-o"]).arg(&out);
    let status = cmd.status();
    let _ = fs::remove_dir_all(&dir);
    match status {
        Ok(s) if s.success() => {
            // `wasm-ld` does not check that its own exports (the memory, a
            // `-Wl,--export=` name) are distinct from the definitions
            // `--export-dynamic` exports; a module with two exports of one
            // name is invalid, so it is never left behind as a success.
            let duplicate = match fs::read(&out) {
                Ok(bytes) => wasm_duplicate_export(&bytes),
                Err(e) => Some(format!("cannot read the linked module: {e}")),
            };
            if let Some(why) = duplicate {
                let _ = fs::remove_file(&out);
                eprintln!(
                    "trust-cg: error[link]: the linked module '{}' is invalid, refused and \
                     removed: {why}",
                    out.display()
                );
                process::exit(1);
            }
            eprintln!(
                "trust-cg: linked {} wasm32 object(s) -> {} ({})",
                objects.len(),
                out.display(),
                linker.0.display(),
            );
        }
        Ok(s) => {
            eprintln!(
                "trust-cg: error[link]: {} exited with {s}",
                linker.0.display()
            );
            process::exit(1);
        }
        Err(e) => {
            eprintln!(
                "trust-cg: error[link]: cannot run {}: {e}",
                linker.0.display()
            );
            process::exit(1);
        }
    }
}

/// The export name `wasm-ld` gives the linked memory when no passthrough
/// option renames or imports it.
const WASM_LD_MEMORY_EXPORT: &str = "memory";

/// The name the linked module exports its memory under, read from the `-Wl`
/// options `wasm-ld` takes for it (single- or double-dash, the last one
/// winning): `--export-memory` exports it as `memory`,
/// `--export-memory=<name>` as `<name>`; with neither, `--import-memory[=…]`
/// exports none, and otherwise `wasm-ld` exports it as `memory`. Options that
/// only size or share the memory (`--initial-memory=`, `--max-memory=`,
/// `--shared-memory`, `--no-growable-memory`) leave the export alone.
fn wasm32_linked_memory_export(cli: &Cli) -> Option<String> {
    let mut export: Option<String> = None;
    let mut import = false;
    let args = cli
        .linker_passthrough
        .iter()
        .filter_map(|value| value.strip_prefix("l,"))
        .flat_map(|args| args.split(','));
    for arg in args {
        let Some(option) = arg.strip_prefix("--").or_else(|| arg.strip_prefix('-')) else {
            continue;
        };
        if option == "export-memory" {
            export = Some(WASM_LD_MEMORY_EXPORT.to_string());
        } else if let Some(name) = option.strip_prefix("export-memory=") {
            export = Some(name.to_string());
        } else if option == "import-memory" || option.starts_with("import-memory=") {
            import = true;
        }
    }
    match (export, import) {
        (Some(name), _) => Some(name),
        (None, true) => None,
        (None, false) => Some(WASM_LD_MEMORY_EXPORT.to_string()),
    }
}

/// The first export name a wasm module carries twice (`Some` with the
/// reason), or `Some` when the module's section or export structure cannot be
/// read. `None` for a well-formed export section with distinct names.
fn wasm_duplicate_export(bytes: &[u8]) -> Option<String> {
    fn leb(bytes: &[u8], at: &mut usize) -> Option<u32> {
        let mut value = 0u32;
        for shift in (0..35).step_by(7) {
            let byte = *bytes.get(*at)?;
            *at += 1;
            value |= u32::from(byte & 0x7f).checked_shl(shift)?;
            if byte & 0x80 == 0 {
                return Some(value);
            }
        }
        None
    }
    fn scan(bytes: &[u8]) -> Option<Option<String>> {
        if bytes.get(..8)? != b"\0asm\x01\0\0\0" {
            return None;
        }
        let mut at = 8;
        while at < bytes.len() {
            let id = bytes[at];
            at += 1;
            let size = leb(bytes, &mut at)? as usize;
            let end = at.checked_add(size).filter(|&e| e <= bytes.len())?;
            if id == 7 {
                let mut p = at;
                let count = leb(bytes, &mut p)?;
                let mut seen = std::collections::HashSet::new();
                for _ in 0..count {
                    let len = leb(bytes, &mut p)? as usize;
                    let name = bytes.get(p..p.checked_add(len)?)?;
                    p += len;
                    // The export's kind byte, then its index.
                    p += 1;
                    leb(bytes, &mut p)?;
                    if !seen.insert(name) {
                        return Some(Some(format!(
                            "it exports `{}` twice",
                            String::from_utf8_lossy(name)
                        )));
                    }
                }
                if p != end {
                    return None;
                }
            }
            at = end;
        }
        Some(None)
    }
    scan(bytes).unwrap_or_else(|| Some("its export section cannot be read".to_string()))
}

/// A definition the link would export beside the memory under the memory's
/// own export name ([`wasm32_linked_memory_export`]): the link exports every
/// default-visibility definition (`--export-dynamic`), and `wasm-ld` exports
/// the memory without checking the name is free, which yields a module no
/// engine accepts ("duplicate export name"). `None` when no such definition
/// exists, or the memory is not exported.
fn wasm32_link_export_collision(cli: &Cli, module: &trust_ir::Module) -> Option<String> {
    let memory_export = wasm32_linked_memory_export(cli)?;
    let exported = |linkage: trust_ir::Linkage, visibility: trust_ir::Visibility| {
        !matches!(
            linkage,
            trust_ir::Linkage::Internal
                | trust_ir::Linkage::Private
                | trust_ir::Linkage::AvailableExternally
                | trust_ir::Linkage::ExternalWeak
        ) && visibility != trust_ir::Visibility::Hidden
    };
    let function = module.functions.iter().find(|f| {
        f.name == memory_export && !f.blocks.is_empty() && exported(f.linkage, f.visibility)
    });
    let global = module.globals.iter().find(|g| {
        g.name == memory_export && g.initializer.is_some() && exported(g.linkage, g.visibility)
    });
    let kind = match (function, global) {
        (Some(_), _) => "function",
        (None, Some(_)) => "global",
        (None, None) => return None,
    };
    Some(format!(
        "it defines an exported {kind} `{memory_export}`, and the link exports every \
         default-visibility definition beside the linked memory's own `{memory_export}` export \
         — the module would carry two exports of one name (give the definition internal \
         linkage or hidden visibility, or rename the memory export with -Wl,--export-memory=<name>)"
    ))
}

/// A private directory for link inputs, next to the output (never a
/// world-writable temp directory).
fn tempfile_dir_near(out: &Path) -> std::io::Result<PathBuf> {
    let parent = out
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .map(Path::to_path_buf)
        .unwrap_or_else(|| PathBuf::from("."));
    for n in 0..1000u32 {
        let dir = parent.join(format!(".trust-cg-wasm-link-{}-{n}", process::id()));
        match fs::create_dir(&dir) {
            Ok(()) => return Ok(dir),
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(e) => return Err(e),
        }
    }
    Err(std::io::Error::other("no free link directory name"))
}

/// The leading arguments that select the wasm flavor of linker `path`. lld
/// picks its driver from `argv[0]` (`wasm-ld` names it) or from `-flavor`,
/// which it reads ONLY as `argv[1]`; the generic `rust-lld` / `lld` driver
/// names none, so it is given `-flavor wasm` by file name — the rule rustc
/// applies — whether it came from `--wasm-ld`, `$WASM_LD` or PATH. Anything
/// else (a `wasm-ld`, or a wrapper that selects its own flavor) is run as is:
/// lld rejects a second `-flavor`.
fn wasm_ld_flavor_args(path: &Path) -> Vec<String> {
    match path.file_stem().and_then(|stem| stem.to_str()) {
        Some("rust-lld" | "lld") => vec!["-flavor".to_string(), "wasm".to_string()],
        _ => Vec::new(),
    }
}

/// The wasm linker and the leading arguments that select its wasm flavor.
fn find_wasm_ld(cli: &Cli) -> Option<(PathBuf, Vec<String>)> {
    let with_flavor = |path: PathBuf| {
        let flavor = wasm_ld_flavor_args(&path);
        (path, flavor)
    };
    if let Some(p) = &cli.wasm_ld {
        return Some(with_flavor(p.clone()));
    }
    if let Some(p) = std::env::var_os("WASM_LD").filter(|p| !p.is_empty()) {
        return Some(with_flavor(PathBuf::from(p)));
    }
    let path = std::env::var_os("PATH")?;
    for dir in std::env::split_paths(&path) {
        let wasm_ld = dir.join("wasm-ld");
        if wasm_ld.is_file() {
            return Some(with_flavor(wasm_ld));
        }
    }
    for dir in std::env::split_paths(&path) {
        let rust_lld = dir.join("rust-lld");
        if rust_lld.is_file() {
            return Some(with_flavor(rust_lld));
        }
    }
    None
}

fn main() -> process::ExitCode {
    // Parse through `ArgMatches` so the CLI can tell an EXPLICITLY-PASSED
    // option from a default one: an explicit `--fsym-solver` under
    // `--fsym=off` is a dropped request — an option the selected route never
    // reads — and the CLI refuses dropped requests by name rather than
    // ignoring them.
    let matches = Cli::command().get_matches_from(normalize_cc_link_spellings(std::env::args_os()));
    let fsym_solver_explicit =
        matches.value_source("fsym_solver") == Some(ValueSource::CommandLine);
    let cli = match Cli::from_arg_matches(&matches) {
        Ok(cli) => cli,
        Err(e) => e.exit(),
    };
    if cli.print_ay_identity {
        let (report, admitted) = ay_identity_report::report();
        println!("{report}");
        return if admitted {
            process::ExitCode::SUCCESS
        } else {
            process::ExitCode::FAILURE
        };
    }
    let inputs = resolve_inputs(&cli);
    let format = resolve_format(&cli);
    // WS7.3 (F-064 / F-065 / F-072): the `.trust_ir` TEXT codec is not total
    // at this trust-ir pin — it cannot carry function summaries, clause
    // bindings, every layout fact or `global_asm` (trust-ir WS4.4 / WS4.5
    // open). The pinned parser refuses a text that was printed with a loss
    // (`; #lossy`), so a text round trip cannot launder a refusal; but a text
    // input can still never state those facts. A proof path
    // (`--emit-proofs`) or a strict license path (`--refuse-unlicensed`)
    // refuses text input by name; the default path warns.
    if let Some(text_input) = text_format_input(format, &inputs) {
        if cli.emit_proofs.is_some() || cli.refuse_unlicensed {
            let flag = if cli.emit_proofs.is_some() {
                "--emit-proofs"
            } else {
                "--refuse-unlicensed"
            };
            eprintln!(
                "trust-cg: error: text-format input refused under {flag}: '{}' is `.trust_ir` \
                 text, and the text codec at this trust-ir pin cannot carry function \
                 summaries, clause bindings, every layout fact or `global_asm` \
                 (TEXT_INPUT_NOT_TOTAL); pass the binary module instead",
                text_input.display()
            );
            process::exit(1);
        }
        eprintln!(
            "trust-cg: warning: text-format input '{}': the `.trust_ir` text codec at this \
             trust-ir pin cannot carry function summaries, clause bindings, every layout fact \
             or `global_asm` (TEXT_INPUT_NOT_TOTAL); the module compiles as the text states it",
            text_input.display()
        );
    }

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
    // `--fsym-solver` is read only while the preflight runs: under the default
    // `--fsym=off` the preflight returns before the solver is consulted, so an
    // explicitly-passed solver is a DROPPED REQUEST. The default value is not
    // a request and is not refused.
    if fsym_solver_explicit && cli.fsym == FsymModeArg::Off {
        eprintln!("trust-cg: error: --fsym-solver requires --fsym=warn or --fsym=error");
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

    // wasm32 dispatch boundary (see `trust_cg_codegen::wasm::target`): the
    // wasm lane compiles one module to raw `.wasm` bytes and returns — the
    // native object/linker pipeline below never runs for it.
    //
    // It dispatches BEFORE the emit-json / emit-trust_ir publication below
    // because that lane publishes nothing until its compile has succeeded: it
    // runs its own refusals, loads the module once, compiles, and only then
    // writes the artifacts requested here (see `run_wasm32_compile`).
    // Otherwise a `--target wasm32 --emit-json out.json` invocation that the
    // backend goes on to refuse would still leave `out.json` behind. The
    // native lane's order is unchanged: it publishes these round-trip
    // artifacts before compiling, exactly as before.
    let target_spec = match cli.target {
        CliTarget::Wasm32 => {
            run_wasm32_compile(&cli, &inputs, format);
            return process::ExitCode::SUCCESS;
        }
        CliTarget::Native(spec) => spec,
    };
    // Capture MACOSX_DEPLOYMENT_TARGET once, as Apple's compiler drivers do,
    // for an Apple target whose triple names no macOS version (the explicit
    // triple wins). The captured version sets every object's LC_BUILD_VERSION
    // minimum OS and the link's -mmacosx-version-min, and it is part of the
    // target spec the compile policy and artifact-cache identity bind. A
    // malformed or too-old value is refused, never replaced by the default.
    let target_spec = match target_spec.with_macos_deployment_target_from_environment() {
        Ok(spec) => spec,
        Err(error) => {
            eprintln!("trust-cg: error: {error}");
            process::exit(1);
        }
    };

    if cli.compile_only && inputs.len() > 1 && cli.output.is_some() {
        eprintln!("trust-cg: error: -o/--output with -c requires exactly one input file");
        process::exit(1);
    }
    let mut refusals = native_output_alias_refusals(&cli, &inputs);
    // Link options are validated before any input is read or artifact written:
    // under -c they are dropped requests (no link step runs), otherwise the
    // request must be admissible for the target.
    if cli.compile_only {
        for flag in requested_link_options(&cli) {
            refusals.push(format!(
                "{flag}: -c compiles objects only; no link step runs"
            ));
        }
    } else if let Err(link_refusals) = build_link_request(
        &cli,
        inputs.clone(),
        cli.output.clone().unwrap_or_else(|| PathBuf::from("a.out")),
        target_spec,
    ) {
        refusals.extend(link_refusals);
    }
    if !refusals.is_empty() {
        for refusal in refusals {
            eprintln!("trust-cg: error: {refusal}");
        }
        process::exit(1);
    }

    // Admit operator resource controls before reading inputs or publishing
    // round-trip artifacts. Validation is independent of input count and
    // --no-parallel; both file and function compilation share this contract.
    let worker_count = match resource_limits::try_worker_count_for_items(inputs.len()) {
        Ok(workers) => {
            if cli.no_parallel {
                None
            } else {
                workers
            }
        }
        Err(error) => {
            eprintln!("trust-cg: error: invalid execution resource budget: {error}");
            return process::ExitCode::FAILURE;
        }
    };

    // Emit JSON round-trip output if requested (single input only).
    if let Some(ref emit_path) = cli.emit_json {
        let module = load_single_input_module(&inputs[0], format);
        write_emit_json_artifact(&module, emit_path);
    }

    // Emit .trust_ir text round-trip output if requested (#413, single input only).
    if let Some(ref emit_path) = cli.emit_trust_ir {
        let module = load_single_input_module(&inputs[0], format);
        write_emit_trust_ir_artifact(&module, emit_path);
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

    let config = build_config_for_input_count(&cli, inputs.len(), target_spec);
    let compiler_config_bytes = canonical_compiler_config_bytes(&config, target_spec);
    let compile_artifact_cache = compile_artifact_cache_config(&cli, &config);
    let codegen_license = codegen_license_policy(&cli);
    // `--link` dependencies are read once, with the inputs' format, before
    // any input is compiled.
    let link_dependencies: Option<Vec<trust_ir::Module>> = if cli.link.is_empty() {
        None
    } else {
        Some(
            cli.link
                .iter()
                .map(|path| {
                    pipeline::load_module_as(path, format).unwrap_or_else(|error| {
                        eprintln!(
                            "trust-cg: error: --link: failed to read trust_ir module from '{}': \
                             {error}",
                            path.display()
                        );
                        process::exit(1);
                    })
                })
                .collect(),
        )
    };

    // Determine whether we need temp files (linking mode) or permanent files
    // (compile-only mode).
    let compile_only = cli.compile_only;
    // Each invocation owns a private directory. Input indices distinguish
    // modules with identical basenames in different source directories.
    let temp_directory = if compile_only {
        None
    } else {
        Some(
            tempfile::Builder::new()
                .prefix("trust-cg-")
                .tempdir()
                .unwrap_or_else(|error| {
                    eprintln!("trust-cg: error: cannot create temporary object directory: {error}");
                    process::exit(1);
                }),
        )
    };
    let compile_input = |(index, input): (usize, &PathBuf)| {
        let obj_path = match &temp_directory {
            Some(directory) => temp_object_path(directory.path(), index),
            None => object_path_for(input, cli.output.as_deref(), inputs.len() == 1),
        };
        let compile = || {
            compile_one(
                input,
                &config,
                target_spec,
                format,
                &obj_path,
                cli.fsym,
                cli.fsym_solver,
                cli.fsym_report_json.as_deref(),
                loaded_profile.as_ref(),
                cli.profile_use.as_deref(),
                cli.profile_generate.as_deref(),
                profile_generate_inputs.as_deref(),
                compile_artifact_cache.as_ref(),
                &codegen_license,
                link_dependencies.as_deref(),
            )
        };
        // Certified sidecars require every instruction's proof evidence. The
        // compiler's promotion gate rejects every unverified entry (sampled
        // evidence and registry-name candidates included) before the object
        // can be written; there is no weaker policy to override.
        compile()
    };

    let file_results: Result<Vec<FileCompilationResult>, String> =
        if let Some(worker_count) = worker_count {
            // Multiple files: bounded parallel compilation via a local Rayon pool.
            let pool = match resource_limits::build_rayon_pool(worker_count) {
                Ok(pool) => pool,
                Err(error) => {
                    eprintln!("trust-cg: error: failed to create bounded worker pool: {error}");
                    return process::ExitCode::FAILURE;
                }
            };
            pool.install(|| inputs.par_iter().enumerate().map(compile_input).collect())
        } else {
            inputs.iter().enumerate().map(compile_input).collect()
        };
    let file_results = match file_results {
        Ok(results) => results,
        Err(error) => {
            eprintln!("trust-cg: error: {error}");
            return process::ExitCode::FAILURE;
        }
    };

    // Print per-file diagnostics.
    let mut total_functions = 0usize;
    let mut total_code_bytes = 0usize;
    let mut total_emit_summary = emit_proofs::EmitSummary::default();
    let mut protected_proof_paths = inputs.clone();
    protected_proof_paths.extend(
        auxiliary_output_paths(&cli)
            .into_iter()
            .map(|(_, path)| path.to_path_buf()),
    );
    protected_proof_paths.extend(file_results.iter().map(|result| result.object_path.clone()));
    if !compile_only {
        protected_proof_paths.push(cli.output.clone().unwrap_or_else(|| PathBuf::from("a.out")));
    }
    if let Some(path) = &cli.profile_use {
        protected_proof_paths.push(path.clone());
    }

    for (input_index, fr) in file_results.iter().enumerate() {
        print_trace(&fr.result);
        print_proofs(&fr.result);
        if cli.metrics {
            print_metrics(&fr.result);
        }

        // Emit per-proof SMT-LIB2 + certificate files (#421).
        if let Some(ref dir) = cli.emit_proofs {
            let module_dir = if file_results.len() > 1 {
                dir.join(format!("input_{input_index}"))
            } else {
                dir.clone()
            };
            match emit_proof_artifacts(
                &module_dir,
                &fr.result,
                target_spec,
                &fr.trust_ir_bytes,
                &compiler_config_bytes,
                &protected_proof_paths,
            ) {
                Ok(Some(s)) => total_emit_summary.merge(s),
                Ok(None) => {}
                Err(e) => {
                    eprintln!(
                        "trust-cg: error: failed to emit proof files to '{}': {}",
                        module_dir.display(),
                        e,
                    );
                    return process::ExitCode::FAILURE;
                }
            }
            if let Some(rows) = &fr.linked_dependencies
                && let Err(e) = emit_proofs::write_linked_dependencies(
                    &module_dir,
                    rows,
                    &protected_proof_paths,
                )
            {
                eprintln!(
                    "trust-cg: error: failed to write linked dependencies to '{}': {}",
                    module_dir.display(),
                    e,
                );
                return process::ExitCode::FAILURE;
            }
        }

        // Proof validation and destination checks must succeed before an
        // existing permanent object is replaced. Publication of several
        // independent files is still not an atomic filesystem transaction.
        if let Err(error) = fs::write(&fr.object_path, &fr.result.object_code) {
            eprintln!(
                "trust-cg: error: cannot write '{}': {error}",
                fr.object_path.display()
            );
            return process::ExitCode::FAILURE;
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

    if let Some(path) = &cli.emit_runtime_deps {
        let entries: Vec<(PathBuf, PathBuf, &[u8])> = inputs
            .iter()
            .zip(&file_results)
            .map(|(input, result)| {
                (
                    input.clone(),
                    result.object_path.clone(),
                    result.result.object_code.as_slice(),
                )
            })
            .collect();
        if let Err(error) = write_runtime_deps_report(path, &entries) {
            eprintln!("trust-cg: error: {error}");
            return process::ExitCode::FAILURE;
        }
    }

    if compile_only {
        // Done -- object files are in place.
        return process::ExitCode::SUCCESS;
    }

    // Linking mode: combine all .o files into an executable or shared object.
    let output_path = cli.output.clone().unwrap_or_else(|| PathBuf::from("a.out"));

    let object_paths: Vec<PathBuf> = file_results.iter().map(|f| f.object_path.clone()).collect();

    let request = match build_link_request(&cli, object_paths, output_path.clone(), target_spec) {
        Ok(request) => request,
        Err(refusals) => {
            for refusal in refusals {
                eprintln!("trust-cg: error: {refusal}");
            }
            return process::ExitCode::FAILURE;
        }
    };
    if let Err(error) = link(&request) {
        eprintln!("trust-cg: error: {error}");
        return process::ExitCode::FAILURE;
    }
    if cli.linked_image_evidence {
        let providers = link_library_exports(&cli);
        match link_driver::record_darwin_linked_image(&request, "cc", &providers) {
            Ok(path) => eprintln!(
                "trust-cg: linked-image evidence record -> {}",
                path.display()
            ),
            Err(error) => {
                eprintln!("trust-cg: error[link:image-evidence]: {error}");
                return process::ExitCode::FAILURE;
            }
        }
    }

    eprintln!(
        "trust-cg: linked {} file(s), {} function(s), {} code bytes -> {}",
        file_results.len(),
        total_functions,
        total_code_bytes,
        output_path.display(),
    );
    process::ExitCode::SUCCESS
}

/// The codegen license the crate's unit tests compile their hand-built
/// fixtures under. Those fixtures carry no codegen license (`body_gate:
/// None`), which trust-cg REFUSES by default (roadmap WS7.5, decision gate
/// DG-73), so they state `Permit` explicitly: none of them passes (or is
/// refused) because the license silently refused it. Declared under a plain
/// `#[cfg(test)]`, so the production `Permit` census never counts it.
#[cfg(test)]
pub(crate) mod license_test_support {
    /// The default policy with claim-less bodies permitted.
    pub(crate) fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
        trust_cg_codegen::CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn proof_cert(
        function: &str,
        rule: &str,
        verified: bool,
    ) -> trust_cg_codegen::compiler::ProofCertificate {
        trust_cg_codegen::compiler::ProofCertificate {
            ay_refusal_note: None,
            source_bound_obligation: None,
            rule_name: rule.to_string(),
            verified,
            category: "ConstantMaterialization".to_string(),
            strength: "Formal".to_string(),
            function_name: function.to_string(),
        }
    }

    /// WS7.2 (F-111): every function's certificates open with the adapter
    /// disclosure, each rule names its LIR -> machine span, and no line is a
    /// function-level `VERIFIED`: the rules stay exactly graded, the claim
    /// they add up to is no longer overstated.
    #[test]
    fn proof_listing_names_the_adapter_blind_spot_per_function() {
        let text = render_proofs(&[
            proof_cert("two_inserts_sub", "ConstMat: MOVZ", true),
            proof_cert("other", "RET", true),
            proof_cert("two_inserts_sub", "covered_elsewhere RET", false),
        ]);
        // A build carrying the test-only mutation knobs says so on its own
        // line; nothing else changes.
        assert_eq!(
            text.contains("carries test-only mutation knobs"),
            trust_cg_codegen::MUTATION_KNOBS,
            "{text}"
        );
        let lines: Vec<&str> = text
            .lines()
            .filter(|line| !line.contains("carries test-only mutation knobs"))
            .collect();
        assert_eq!(lines.first(), Some(&"--- proof certificates ---"), "{text}");
        assert_eq!(lines.last(), Some(&"--- end proofs ---"), "{text}");
        let headers: Vec<&str> = lines
            .iter()
            .copied()
            .filter(|line| line.contains("NOT COVERED"))
            .collect();
        assert_eq!(
            headers,
            [
                "  [two_inserts_sub] trust-ir->lir: NOT COVERED (adapter outside the proven boundary)",
                "  [other] trust-ir->lir: NOT COVERED (adapter outside the proven boundary)",
            ],
            "{text}"
        );
        // Grouped by function: both of two_inserts_sub's rules sit under its
        // header, before `other`'s.
        assert_eq!(
            &lines[1..6],
            [
                headers[0],
                "    ConstMat: MOVZ [VERIFIED] (lir->machine)",
                "    covered_elsewhere RET [UNVERIFIED] (lir->machine)",
                headers[1],
                "    RET [VERIFIED] (lir->machine)",
            ],
            "{text}"
        );
        for line in &lines {
            if line.contains("VERIFIED") {
                assert!(
                    line.starts_with("    ") && line.ends_with("(lir->machine)"),
                    "a VERIFIED outside a LIR -> machine rule row: {line:?}"
                );
            }
        }
        assert_eq!(
            render_proofs(&[]),
            "trust-cg: note: proof emission enabled but no certificates produced\n"
        );
    }

    /// A generic lld driver (`rust-lld`, `lld`) names no flavor in `argv[0]`,
    /// so it gets `-flavor wasm` however it was found; a `wasm-ld` (or a
    /// wrapper selecting its own flavor) gets none, since lld rejects a second
    /// `-flavor`.
    #[test]
    fn wasm_ld_flavor_follows_the_linker_file_name() {
        let flavor = vec!["-flavor".to_string(), "wasm".to_string()];
        for generic in [
            "rust-lld",
            "/opt/rust/lib/rustlib/aarch64-apple-darwin/bin/rust-lld",
            "/usr/bin/lld",
            "C:/rust/bin/rust-lld.exe",
        ] {
            assert_eq!(wasm_ld_flavor_args(Path::new(generic)), flavor, "{generic}");
        }
        for named in [
            "wasm-ld",
            "/usr/bin/wasm-ld",
            "/rustlib/bin/gcc-ld/wasm-ld",
            "wasm-ld-22",
        ] {
            assert!(wasm_ld_flavor_args(Path::new(named)).is_empty(), "{named}");
        }
    }

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
    fn linker_target_flags_are_os_specific() {
        let cli = Cli::parse_from(["trust-cg", "-L", "/opt/lib", "-l", "m", "one.tmbc"]);
        let args = |triple: &str, objects: &[&str]| {
            let request = build_link_request(
                &cli,
                objects.iter().map(PathBuf::from).collect(),
                "out".into(),
                parse_target(triple).unwrap(),
            )
            .unwrap();
            let command = request.command("cc").unwrap();
            assert_eq!(command.get_program(), "cc");
            command
                .get_args()
                .map(|arg| arg.to_str().unwrap().to_owned())
                .collect::<Vec<_>>()
        };
        // ELF links always request a non-executable stack before the inputs;
        // only Darwin gets the Apple `-arch` flag, and neither leaks into the
        // other.
        for linux in ["x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu"] {
            assert_eq!(
                args(linux, &["a.o", "b.o"]),
                [
                    "-o",
                    "out",
                    "-Wl,-z,noexecstack",
                    "a.o",
                    "b.o",
                    "-L/opt/lib",
                    "-lm"
                ],
                "{linux}"
            );
        }
        assert_eq!(
            args("x86_64-apple-darwin", &["a.o"]),
            ["-arch", "x86_64", "-o", "out", "a.o", "-L/opt/lib", "-lm"]
        );
        let darwin = args("aarch64-apple-darwin", &["a.o"]);
        assert_eq!(&darwin[..2], ["-arch", "arm64"]);
        assert!(
            !darwin.iter().any(|arg| arg == "-Wl,-z,noexecstack"),
            "ld64 has no -z noexecstack"
        );
        assert_eq!(
            args("x86_64-pc-windows-msvc", &["a.o"]),
            ["-o", "out", "a.o", "-L/opt/lib", "-lm"]
        );
    }

    fn normalized(args: &[&str]) -> Vec<String> {
        normalize_cc_link_spellings(args.iter().map(std::ffi::OsString::from))
            .into_iter()
            .map(|arg| arg.into_string().unwrap())
            .collect()
    }

    #[test]
    fn cc_link_spellings_normalize_only_in_option_position() {
        assert_eq!(
            normalized(&[
                "trust-cg",
                "-shared",
                "-soname",
                "libx.so",
                "-rpath",
                "-static",
                "-pie",
                "-no-pie",
                "-nostdlib",
                "a.tmbc",
            ]),
            [
                "trust-cg",
                "--shared",
                "--soname",
                "libx.so",
                "--rpath",
                "-static",
                "--pie",
                "--no-pie",
                "--nostdlib",
                "a.tmbc",
            ],
            "the value of -rpath is never rewritten, even when it looks like a flag"
        );
        assert_eq!(
            normalized(&["trust-cg", "-o", "-shared", "a.tmbc"]),
            ["trust-cg", "-o", "-shared", "a.tmbc"],
            "an output literally named -shared stays an output"
        );
        assert_eq!(
            normalized(&["trust-cg", "a.tmbc", "--", "-static"]),
            ["trust-cg", "a.tmbc", "--", "-static"]
        );
    }

    #[test]
    fn typed_link_options_build_a_validated_request() {
        let cli = Cli::parse_from(normalize_cc_link_spellings(
            [
                "trust-cg",
                "-shared",
                "-soname",
                "libtcg.so.1",
                "-rpath",
                "$ORIGIN",
                "-Wl,-z,text",
                "-Wl,--as-needed",
                "a.tmbc",
            ]
            .map(std::ffi::OsString::from),
        ));
        let target = parse_target("aarch64-unknown-linux-gnu").unwrap();
        let request =
            build_link_request(&cli, vec!["a.o".into()], "libtcg.so".into(), target).unwrap();
        let args: Vec<String> = request
            .driver_arguments()
            .unwrap()
            .into_iter()
            .map(|arg| arg.into_string().unwrap())
            .collect();
        assert_eq!(
            args,
            [
                "-shared",
                "-o",
                "libtcg.so",
                "-Wl,-z,noexecstack",
                "a.o",
                "-Wl,-soname,libtcg.so.1",
                "-Wl,-rpath,$ORIGIN",
                "-Wl,-z,text",
                "-Wl,--as-needed",
            ]
        );
    }

    /// The executable modes map to the C driver's flags, in the cc spelling
    /// and the double-dash spelling alike (the linked images and their runs
    /// are checked by `tests/link_options.rs` `linux_link_modes`).
    #[test]
    fn executable_mode_options_map_to_driver_flags() {
        let target = parse_target("aarch64-unknown-linux-gnu").unwrap();
        for (spellings, expected) in [
            (vec![vec!["-pie"], vec!["--pie"]], vec!["-pie"]),
            (vec![vec!["-no-pie"], vec!["--no-pie"]], vec!["-no-pie"]),
            (vec![vec!["-static"], vec!["--static"]], vec!["-static"]),
            (
                vec![vec!["-nostdlib"], vec!["--nostdlib"]],
                vec!["-nostdlib"],
            ),
            (
                vec![vec!["-no-pie", "-static", "-nostdlib"]],
                vec!["-no-pie", "-static", "-nostdlib"],
            ),
        ] {
            for flags in spellings {
                let mut argv = vec!["trust-cg"];
                argv.extend(flags.iter().copied());
                argv.push("a.tmbc");
                let cli = Cli::parse_from(normalize_cc_link_spellings(
                    argv.iter().map(std::ffi::OsString::from),
                ));
                let request =
                    build_link_request(&cli, vec!["a.o".into()], "prog".into(), target).unwrap();
                let args: Vec<String> = request
                    .driver_arguments()
                    .unwrap()
                    .into_iter()
                    .map(|arg| arg.into_string().unwrap())
                    .collect();
                let mut want: Vec<&str> = expected.clone();
                want.extend(["-o", "prog", "-Wl,-z,noexecstack"]);
                // A static link asks for `.eh_frame_hdr`, as the C driver
                // does for every other link.
                if expected.contains(&"-static") {
                    want.push("-Wl,--eh-frame-hdr");
                }
                want.push("a.o");
                assert_eq!(args, want, "{flags:?}");
            }
        }
    }

    #[test]
    fn invalid_link_options_are_refused_by_name() {
        let target = parse_target("aarch64-unknown-linux-gnu").unwrap();
        let darwin = parse_target("aarch64-apple-darwin").unwrap();
        for (args, spec, expected) in [
            (vec!["-Wall"], target, "-Wall: only the -Wl"),
            (vec!["-Wl,-shared"], target, "--shared"),
            (
                vec!["--soname", "x"],
                target,
                "--soname: only a shared object",
            ),
            (
                vec!["--shared", "--static"],
                target,
                "--static: a shared object",
            ),
            (vec!["--static"], darwin, "--static: Darwin"),
            (vec!["--no-pie"], darwin, "--no-pie: arm64 Darwin"),
            (
                vec!["-Wl,-z,force-bti"],
                target,
                "-Wl,-z,force-bti: [TCG-LINK-BTI-PAC] `-z force-bti` is refused",
            ),
            (
                vec!["-Wl,-zpac-plt"],
                target,
                "-Wl,-zpac-plt: [TCG-LINK-BTI-PAC] `-z pac-plt` is refused",
            ),
            (
                vec!["-Wl,-z,relro", "-Wl,-z,bti-report=error"],
                darwin,
                "-Wl,-z,bti-report=error: [TCG-LINK-BTI-PAC] `-z bti-report=error` is refused",
            ),
        ] {
            let mut argv = vec!["trust-cg"];
            argv.extend(args.iter().copied());
            argv.push("a.tmbc");
            let cli = Cli::parse_from(argv);
            let refusals =
                build_link_request(&cli, vec!["a.o".into()], "out".into(), spec).unwrap_err();
            assert!(
                refusals.iter().any(|refusal| refusal.contains(expected)),
                "{args:?}: {refusals:?}"
            );
        }
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
    fn an_x86_64_compile_without_certificates_requests_the_certificate_free_allocation() {
        let x86 = parse_target("x86_64-unknown-linux-gnu").unwrap();
        let plain = Cli::parse_from(["trust-cg", "-c", "a.tmbc"]);
        assert!(build_config(&plain, x86).x86_certificate_free_allocation);
        assert!(!build_config(&plain, x86).emit_proofs);

        // Certificates kept: no request (Compiler::compile would withhold it).
        let proofs = Cli::parse_from(["trust-cg", "-c", "--emit-proofs=proofs", "a.tmbc"]);
        let config = build_config(&proofs, x86);
        assert!(config.emit_proofs);
        assert!(!config.x86_certificate_free_allocation);

        // The explicit opt-out keeps the historical allocation.
        let opted_out = Cli::parse_from([
            "trust-cg",
            "-c",
            "--no-x86-certificate-free-allocation",
            "a.tmbc",
        ]);
        assert!(!build_config(&opted_out, x86).x86_certificate_free_allocation);

        // Other targets never carry the request, so their policy digests
        // are unchanged.
        for target in ["aarch64", "aarch64-unknown-linux-gnu", "riscv64"] {
            let spec = parse_target(target).unwrap();
            assert!(
                !build_config(&plain, spec).x86_certificate_free_allocation,
                "{target}"
            );
        }
    }

    #[test]
    fn multi_input_cli_config_disables_inner_function_parallelism() {
        let spec = TargetSpec::unknown_for_architecture(Target::Aarch64);
        let single = Cli::parse_from(["trust-cg", "one.tmbc"]);
        assert!(build_config_for_input_count(&single, 1, spec).parallel);

        let multiple = Cli::parse_from(["trust-cg", "one.tmbc", "two.tmbc"]);
        assert!(!build_config_for_input_count(&multiple, 2, spec).parallel);

        let explicit_serial = Cli::parse_from(["trust-cg", "--no-parallel", "one.tmbc"]);
        assert!(!build_config_for_input_count(&explicit_serial, 1, spec).parallel);
    }

    #[test]
    fn parse_cli_target_accepts_the_two_wasm32_spellings_only() {
        assert_eq!(parse_cli_target("wasm32").unwrap(), CliTarget::Wasm32);
        assert_eq!(
            parse_cli_target("wasm32-unknown-unknown").unwrap(),
            CliTarget::Wasm32
        );

        // Other wasm32 triples are wasm32 per `is_wasm32_target`, but the
        // closed-module lane refuses them with a named diagnostic.
        for target in ["wasm32-wasip1", "wasm32-wasi", "wasm32-unknown-emscripten"] {
            let err = parse_cli_target(target).unwrap_err();
            assert!(err.contains("closed-module"), "{target}: {err}");
            assert!(err.contains("wasm32-unknown-unknown"), "{target}: {err}");
        }

        // wasm64 is not a wasm32 target and falls through to the native
        // parser's unsupported-architecture rejection.
        let err = parse_cli_target("wasm64-unknown-unknown").unwrap_err();
        assert!(err.contains("unsupported architecture"), "{err}");
    }

    #[test]
    fn parse_cli_target_keeps_native_targets_native() {
        for target in ["aarch64", "x86_64-unknown-linux-gnu", "riscv64"] {
            match parse_cli_target(target).unwrap() {
                CliTarget::Native(spec) => {
                    assert_eq!(spec, parse_target(target).unwrap());
                }
                CliTarget::Wasm32 => panic!("{target} must not route to the wasm lane"),
            }
        }
    }

    #[test]
    fn wasm32_lane_refuses_object_and_linker_flags_by_name() {
        let cli = Cli::parse_from([
            "trust-cg",
            "--target",
            "wasm32",
            "-g",
            "-L",
            "/lib",
            "-l",
            "m",
            "--panic-unwind",
            "--relocation-model",
            "pic",
            "--emit-proofs",
            "proofs/",
            "--trace",
            "--metrics",
            "--shared",
            "--nostdlib",
            "--rpath",
            "/lib",
            "-Wl,-z,text",
            "--emit-runtime-deps",
            "deps.json",
            "one.tmbc",
        ]);
        let refusals = wasm32_flag_refusals(&cli, 1);
        let joined = refusals.join("\n");
        for flag in [
            "-g",
            "-L",
            "-l",
            "--panic-unwind",
            "--relocation-model",
            "--emit-proofs",
            "--trace",
            "--metrics",
            "--shared",
            "--nostdlib",
            "--rpath",
            "-Wl",
            "--emit-runtime-deps",
        ] {
            assert!(
                refusals.iter().any(|r| r.starts_with(&format!("{flag}:"))),
                "expected a named refusal for {flag}:\n{joined}"
            );
        }

        // Several inputs are linked by wasm-ld, which takes -L, -l and -Wl.
        let linked = Cli::parse_from([
            "trust-cg",
            "--target",
            "wasm32",
            "-L",
            "/lib",
            "-l",
            "m",
            "-Wl,-z,stack-size=65536",
            "a.tmbc",
            "b.tmbc",
        ]);
        let refusals = wasm32_flag_refusals(&linked, 2);
        assert!(
            refusals.is_empty(),
            "a wasm-ld link must not be refused: {refusals:?}"
        );
        // No input at all is refused.
        let none = Cli::parse_from(["trust-cg", "--target", "wasm32"]);
        assert!(
            wasm32_flag_refusals(&none, 0)
                .iter()
                .any(|r| r.starts_with("<INPUT>...:")),
            "expected a named no-input refusal"
        );
        // With -c, several inputs become several objects, which one -o cannot name.
        let objects = Cli::parse_from([
            "trust-cg", "--target", "wasm32", "-c", "-o", "x.o", "a.tmbc", "b.tmbc",
        ]);
        assert!(
            wasm32_flag_refusals(&objects, 2)
                .iter()
                .any(|r| r.starts_with("-o/--output:")),
            "expected a named -o refusal for several objects"
        );
        // --wasm-ld names a linker that only a link runs.
        let unused_linker = Cli::parse_from([
            "trust-cg",
            "--target",
            "wasm32",
            "--wasm-ld",
            "ld",
            "a.tmbc",
        ]);
        assert!(
            wasm32_flag_refusals(&unused_linker, 1)
                .iter()
                .any(|r| r.starts_with("--wasm-ld:")),
            "expected a named --wasm-ld refusal without a link"
        );

        // A plain single-input wasm32 compile carries no refusals.
        let ok = Cli::parse_from(["trust-cg", "--target", "wasm32", "a.tmbc"]);
        assert!(wasm32_flag_refusals(&ok, 1).is_empty());
        let ok_compile_only = Cli::parse_from(["trust-cg", "--target", "wasm32", "-c", "a.tmbc"]);
        assert!(wasm32_flag_refusals(&ok_compile_only, 1).is_empty());

        // Every -O level is read by the wasm routes, so none is refused.
        for level in ["-O0", "-O1", "-O2", "-O3"] {
            let explicit_opt = Cli::parse_from(["trust-cg", "--target", "wasm32", level, "a.tmbc"]);
            assert!(wasm32_flag_refusals(&explicit_opt, 1).is_empty(), "{level}");
        }
    }

    #[test]
    fn relocation_model_flag_parses_into_the_compiler_config() {
        let spec = parse_target("aarch64-unknown-linux-gnu").unwrap();
        let default = Cli::parse_from(["trust-cg", "-c", "a.tmbc"]);
        assert_eq!(default.relocation_model, None);
        assert_eq!(
            build_config(&default, spec).relocation_model,
            RelocationModel::Static
        );
        // A shared link without a model compiles `pic` on AArch64 Linux
        // (OD-SHARED-PIC-DEFAULT-20261024), and keeps `static` where no other
        // model is implemented; an explicit model is always kept.
        let shared = Cli::parse_from(["trust-cg", "--shared", "-o", "liba.so", "a.tmbc"]);
        assert_eq!(
            build_config(&shared, spec).relocation_model,
            RelocationModel::Pic
        );
        for triple in [
            "x86_64-unknown-linux-gnu",
            "aarch64-apple-darwin",
            "x86_64-apple-darwin",
        ] {
            assert_eq!(
                build_config(&shared, parse_target(triple).unwrap()).relocation_model,
                RelocationModel::Static,
                "{triple}"
            );
        }
        for model in RelocationModel::ALL {
            let explicit = Cli::parse_from([
                "trust-cg",
                "--shared",
                "--relocation-model",
                model.name(),
                "-o",
                "liba.so",
                "a.tmbc",
            ]);
            assert_eq!(build_config(&explicit, spec).relocation_model, model);
        }
        for model in RelocationModel::ALL {
            let cli = Cli::parse_from([
                "trust-cg",
                "--relocation-model",
                model.name(),
                "-c",
                "a.tmbc",
            ]);
            assert_eq!(build_config(&cli, spec).relocation_model, model);
        }
        assert!(
            Cli::try_parse_from(["trust-cg", "--relocation-model", "fpic", "a.tmbc"]).is_err(),
            "an unknown relocation model is a parse error, never a silent default"
        );
    }

    #[test]
    fn wasm32_lane_refuses_aliased_output_paths_by_name() {
        // An output that names the input would destroy the module the compile
        // reads (`--format=text --emit-json <input> <input>`).
        let over_input = Cli::parse_from([
            "trust-cg",
            "--target",
            "wasm32",
            "--format=text",
            "--emit-json",
            "m.trust_ir",
            "m.trust_ir",
        ]);
        let refusals = wasm32_output_alias_refusals(&over_input, &[PathBuf::from("m.trust_ir")]);
        assert!(
            refusals
                .iter()
                .any(|r| r.starts_with("--emit-json:") && r.contains("input module")),
            "expected a named emit-over-input refusal: {refusals:?}"
        );

        // Two outputs naming one file: one of them would be clobbered. The
        // aliased spelling (`./out.json`) must be recognised as the same file.
        let colliding = Cli::parse_from([
            "trust-cg",
            "--target",
            "wasm32",
            "--emit-json",
            "out.json",
            "-o",
            "./out.json",
            "m.tmbc",
        ]);
        let refusals = wasm32_output_alias_refusals(&colliding, &[PathBuf::from("m.tmbc")]);
        assert!(
            refusals
                .iter()
                .any(|r| r.starts_with("--emit-json:") && r.contains("-o/--output")),
            "expected a named output-collision refusal: {refusals:?}"
        );

        // Distinct outputs and a distinct input: nothing is refused.
        let ok = Cli::parse_from([
            "trust-cg",
            "--target",
            "wasm32",
            "--emit-json",
            "out.json",
            "--emit-trust_ir",
            "out.trust_ir",
            "-o",
            "out.wasm",
            "m.tmbc",
        ]);
        assert!(
            wasm32_output_alias_refusals(&ok, &[PathBuf::from("m.tmbc")]).is_empty(),
            "distinct paths must not be refused"
        );

        // The DEFAULT output path aliases the input when the input itself ends
        // in `.wasm`; that is still a destroyed input, and it is named.
        let default_over_input = Cli::parse_from(["trust-cg", "--target", "wasm32", "m.wasm"]);
        let refusals =
            wasm32_output_alias_refusals(&default_over_input, &[PathBuf::from("m.wasm")]);
        assert!(
            refusals
                .iter()
                .any(|r| r.starts_with("-o/--output (defaulted to <INPUT>.wasm):")),
            "expected the defaulted output path to be named: {refusals:?}"
        );
    }

    #[test]
    fn output_alias_key_identifies_aliased_spellings_of_one_path() {
        let dir = std::env::temp_dir().join(format!("trust_cg_alias_key_{}", process::id()));
        let inner = dir.join("inner");
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&inner).expect("create alias-key scratch dirs");

        // The file does not exist yet — the normal case for an output — so the
        // key resolves through the parent directory.
        let plain = dir.join("probe.json");
        let dotted = dir.join(".").join("probe.json");
        let via_parent = inner.join("..").join("probe.json");
        assert_eq!(output_alias_key(&plain), output_alias_key(&dotted));
        assert_eq!(output_alias_key(&plain), output_alias_key(&via_parent));
        assert_ne!(
            output_alias_key(&plain),
            output_alias_key(&dir.join("other.json")),
        );

        // An existing file canonicalizes directly, to the same key.
        fs::write(&plain, b"{}").expect("write alias-key probe");
        assert_eq!(output_alias_key(&plain), output_alias_key(&via_parent));

        let _ = fs::remove_dir_all(&dir);
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
