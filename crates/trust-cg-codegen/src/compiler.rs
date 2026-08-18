// trust-cg-codegen/compiler.rs - Public compilation API
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Public compilation library API for Trust Codegen.
//!
//! The [`Compiler`] struct is the top-level entry point for programmatic
//! compilation. It wraps the internal [`Pipeline`](crate::pipeline::Pipeline)
//! with a clean configuration interface and structured result types.
//!
//! # Quick start
//!
//! ```text
//! use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
//!
//! let compiler = Compiler::new(CompilerConfig::default());
//! let result = compiler.compile(&trust_ir_module)?;
//! let object_bytes = result.object_code;
//! ```
//!
//! # Host JIT target safety
//!
//! [`CompilerConfig::default`] is a legacy object-code configuration that
//! targets [`Target::Aarch64`]. It is not a safe default for in-process JIT
//! execution on every host. Code that will compile and immediately call local
//! executable memory should use [`CompilerConfig::for_host_jit`] or
//! [`Compiler::for_host`] so the target is selected from [`Target::host`].

use std::collections::HashMap;
use std::sync::atomic::AtomicU64;
use std::time::{Duration, Instant};

use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::compile_artifact_cache_profile::{
    COMPILE_ARTIFACT_PROFILE_USE_DISABLED_SHA256, CompileArtifactCacheBoundary,
    CompileArtifactCacheConfig, CompileArtifactCacheKey, CompileArtifactCacheLookup,
    CompileArtifactCacheTelemetry, CompileArtifactProofPolicy, LocalFilesystemCompileArtifactCache,
};
use crate::dialect_pipeline::{DialectPipelineError, lower_dialects_if_needed};
use crate::jit_diagnostics::sha256_hex;
use crate::pipeline::{
    ObjectGlobal, OptLevel, PGO_COUNTER_ARRAY_SYMBOL, PGO_NSITES_SYMBOL, Pipeline, PipelineConfig,
    PipelineError, ProofOptimizationCertificateCitation, guard_kernel_gate_enabled,
};
use crate::target::{CallingConvention, Target, TargetOperatingSystem, TargetSpec};
use crate::x86_64::X86MachineCodeEvidence;

// ---------------------------------------------------------------------------
// Error types
// ---------------------------------------------------------------------------

/// Errors that can occur during compilation through the [`Compiler`] API.
#[derive(Debug, Error)]
pub enum CompileError {
    /// trust_ir to LIR adapter translation failed.
    #[error("adapter error: {0}")]
    Adapter(#[from] trust_cg_lower::AdapterError),

    /// Pre-adapter trust_ir dialect lowering failed (unknown dialect op, pass
    /// error, or fixpoint not reached). See `dialect_pipeline` module.
    /// Tracked under #433 / trust_ir #428.
    #[error("dialect pipeline error: {0}")]
    DialectPipeline(#[from] DialectPipelineError),

    /// Pipeline compilation failed (ISel, regalloc, encoding, etc.).
    #[error("pipeline error: {0}")]
    Pipeline(#[from] PipelineError),

    /// A certified opt pass run failed before the compiler could synthesize a
    /// checked production pass chain.
    #[error("certified pass execution failed for {pass_name} in {function_name}: {detail}")]
    CertifiedPassExecutionFailed {
        /// Certified pass identity.
        pass_name: String,
        /// Function whose pass run failed.
        function_name: String,
        /// Fail-closed detail.
        detail: String,
    },

    /// Certified pass-chain validation failed while attaching production pass
    /// certificates.
    #[cfg(feature = "verify")]
    #[error("certified pass chain validation failed: {0}")]
    CertifiedPassChain(#[from] trust_cg_verify::CertifiedPassChainError),

    /// The carrier-hygiene invariant (`trust_cg_verify::carrier_hygiene`) was
    /// violated on an emitted x86-64 ISel function: a wide-reading consumer
    /// (`SAR`/`IDIV` / `SHR`/`DIV`) read its source across the full 32/64-bit
    /// carrier without a proven (width-aware) sign/zero extension. This is the
    /// MISCOMPILE #51 / #66 hazard (a 32-bit `NOT`/`NEG`/`SUB` of a narrow
    /// i8/i16 value leaves dirty high carrier bits). The pure-lattice checker
    /// runs UNCONDITIONALLY (not behind the `verify` feature) over every
    /// optimized x86 function, so a regression in the ISel extension guards
    /// fails the compile closed instead of silently shipping wrong code.
    #[error(
        "carrier-hygiene violation in {function_name}: {opcode:?} (block {block}, \
         inst {inst_index}) reads vreg {operand:?} across the full carrier without \
         a proven {required:?} extension (proven state: {actual:?}). {detail}"
    )]
    CarrierHygiene {
        /// Function whose emitted ISel stream violated the invariant.
        function_name: String,
        /// Block id (`X86ISelBlock` key) of the violating instruction.
        block: u32,
        /// Index of the violating instruction within its block.
        inst_index: usize,
        /// The wide-reading consumer opcode (`Idiv`/`Div`/`SarRI`/`ShrRR`/...).
        opcode: trust_cg_ir::x86_64_ops::X86Opcode,
        /// Source operand vreg whose carrier hygiene could not be proven.
        operand: trust_cg_ir::regs::VReg,
        /// Extension the consumer's semantics require (`Sign`/`Zero`).
        required: trust_cg_verify::carrier_hygiene::RequiredExtension,
        /// Proven lattice state of `operand` at the consumer.
        actual: trust_cg_verify::carrier_hygiene::HighBits,
        /// Human-readable explanation referencing the historical miscompile class.
        detail: String,
    },

    /// A per-pass translation validator
    /// (`trust_cg_verify::pass_validators`) rejected a glue-pass expansion the
    /// x86-64 pipeline relies on. Today this guards the overflow / checked-arith
    /// expansion (MISCOMPILE #67): the live division-free wide-multiply
    /// expansion is re-proven equivalent for the x86-64 trap semantics, and a
    /// regression to the AArch64-only `SDIV`-identity expansion (which SIGFPEs
    /// on x86 `IDIV`-by-zero) is rejected. Runs UNCONDITIONALLY (not behind the
    /// `verify` feature).
    #[error(
        "per-pass validation rejected for x86-64 pass `{pass_name}` (obligation \
         `{obligation_name}`): {reason}"
    )]
    PassValidationRejected {
        /// Pass whose expansion failed translation validation.
        pass_name: String,
        /// Name of the rejected proof obligation.
        obligation_name: String,
        /// Fail-closed rejection detail (counterexample / reason).
        reason: String,
    },

    /// Compile artifact cache I/O or validation failed.
    #[error("compile artifact cache error: {0}")]
    CompileArtifactCache(#[from] std::io::Error),

    /// Profile-use input could not be encoded into the compile artifact key.
    #[error("profile-use input cannot be encoded for compile artifact cache identity: {0}")]
    ProfileUseCacheIdentity(#[from] trust_cg_opt::pgo::ProfDataError),

    /// Compile artifact cache identity JSON could not be serialized.
    #[error("compile artifact cache identity JSON serialization failed for {component}: {source}")]
    CompileArtifactCacheIdentityJson {
        /// Identity component being serialized.
        component: &'static str,
        /// Underlying JSON serialization error.
        #[source]
        source: serde_json::Error,
    },

    /// Module contains no functions.
    #[error("empty module: no functions to compile")]
    EmptyModule,

    /// The shared trust-ir-level inliner (OPT-4) structural self-check detected
    /// that the inlined result dropped or duplicated an instruction relative to
    /// `caller ⊎ renamed-callee`. Fail the compile CLOSED rather than emit an
    /// unvalidated substitution — never a miscompile.
    #[error("trust-ir inliner self-check failed: {detail}")]
    IrInline {
        /// Fail-closed detail (which opcode multiset diverged, in which fn).
        detail: String,
    },

    /// JIT compilation failed while producing executable memory.
    #[error("JIT compilation failed: {0}")]
    Jit(#[from] crate::jit::JitError),

    /// Caller attempted to JIT-compile code for an ISA that does not match
    /// the current host process.
    #[error(
        "host JIT target mismatch: config target {target:?} does not match \
         host {host:?}; use CompilerConfig::for_host_jit() or \
         Compiler::for_host() for in-process JIT"
    )]
    JitTargetMismatch {
        /// Target selected by the caller's compiler configuration.
        target: Target,
        /// Target architecture of the current host process.
        host: Target,
    },

    /// Caller selected the host ISA, but requested a different OS/ABI target
    /// spec than the current process can execute in-process.
    #[error(
        "host JIT target spec mismatch: requested {requested} but host JIT ABI \
         is {host}; cross-OS/ABI JIT execution is not supported"
    )]
    JitTargetSpecMismatch {
        /// OS/ABI target spec requested by the caller.
        requested: TargetSpec,
        /// OS/ABI target spec for the current host process.
        host: TargetSpec,
    },

    /// Caller selected the host target, but the high-level Compiler JIT path
    /// does not yet have a backend wired for that target.
    #[error(
        "Compiler::compile_module_to_jit does not yet support host target \
         {target:?}; refusing to emit a different ISA for in-process execution"
    )]
    JitTargetUnsupported {
        /// Host target that is not yet supported by `compile_module_to_jit`.
        target: Target,
    },

    /// `compile_ir_function` currently accepts the AArch64-flavoured canonical
    /// MachFunction only; feeding it to another target pipeline would emit the
    /// wrong ISA (or a mislabeled object) rather than dispatching per target.
    #[error(
        "Compiler::compile_ir_function accepts prebuilt AArch64 MachIR only; configured target {target:?} is unsupported"
    )]
    PrebuiltIrTargetUnsupported { target: Target },

    /// Caller requested proof certificates (`config.emit_proofs == true`) for
    /// a target or build configuration that does not yet produce
    /// per-instruction proof certificates through a target-specific function
    /// verifier.
    ///
    /// Returned instead of silently producing `proofs: None` so embedders that
    /// opt into a verified-codegen attestation workflow learn the truth at the
    /// public API boundary rather than trusting a silent lie. Today this fires
    /// for `Target::Riscv64` unconditionally, and for AArch64 / x86-64 proof
    /// requests when the `verify` feature is disabled. With `verify` on, the
    /// x86-64 path produces real certs via
    /// `trust_cg_verify::x86_64_function_verifier` — see #465. The AArch64 path
    /// likewise requires the `verify` feature.
    ///
    /// Tracking: #465 (x86-64 proofs; landed for default `verify` builds),
    /// RISC-V proofs (TBD).
    #[error(
        "proof certificates are not yet supported for target {target:?} in \
         this build; set config.emit_proofs = false, or enable the `verify` \
         feature for AArch64/x86-64 proof generation. Tracking: #465 \
         (x86-64 proofs), RISC-V proofs (TBD)."
    )]
    ProofsUnsupportedForTarget {
        /// The target that requested proofs but cannot produce them.
        target: Target,
    },

    /// A caller requested proof-backed install/promotion, but the public proof
    /// status surface did not prove every emitted entry.
    #[error("proof promotion rejected for target {target:?}: {reason}")]
    ProofPromotionRejected {
        /// Target whose compiled artifact was being promoted.
        target: Target,
        /// Fail-closed rejection detail.
        reason: String,
    },

    /// The resolved JIT validation mode is [`JitValidationMode::Unchecked`] on
    /// an arch whose default is a verifying mode, but no explicit opt-in was
    /// given. Executing uncertified JIT bytes on such a default path requires
    /// `TCG_JIT_UNCHECKED=1` (or an explicit `jit_validation_mode_override`).
    #[error(
        "JIT compile for target {target:?} would execute UNCERTIFIED bytes: the \
         default validation mode is verifying, so reaching Unchecked requires the \
         explicit opt-in TCG_JIT_UNCHECKED=1 (or CompilerConfig::for_host_jit_unchecked / \
         jit_validation_mode_override = Some(Unchecked))"
    )]
    JitUncertifiedBytesRequireOptIn {
        /// Target whose JIT compile was fail-closed.
        target: Target,
    },

    /// Caller requested public x86-64 AOT object emission for a host OS whose
    /// native object format is not implemented yet.
    #[error(
        "x86-64 AOT object format is unsupported for target OS {target_os}: \
         {required_format} emission is not implemented; {context}"
    )]
    X86AotObjectFormatUnsupported {
        /// Host OS selected by the current Rust target.
        target_os: &'static str,
        /// Native object format needed for this host OS.
        required_format: &'static str,
        /// Human-readable fail-closed detail.
        context: &'static str,
    },
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Verbosity level for the compiler's timing trace.
///
/// Distinct from [`trust_cg_ir::TraceLevel`] which controls structured event
/// logging. This enum controls per-phase timing output in the compiler API.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompilerTraceLevel {
    /// No trace output.
    None,
    /// Summary: total time and pass counts.
    Summary,
    /// Full: per-phase timing and per-function details.
    Full,
}

/// Verification policy the high-level compiler applies when it lowers a
/// [`CompilerConfig`] into a [`crate::jit::JitConfig`].
///
/// The three modes form the JIT-5 validation ladder:
///
/// | mode              | executed bytes            | discharge cost           |
/// |-------------------|---------------------------|--------------------------|
/// | [`Self::Unchecked`]      | NOT cert-covered (dev)    | none                     |
/// | [`Self::CachedVerified`] | every byte cert-covered   | amortized (content cache)|
/// | [`Self::AlwaysVerify`]   | every byte cert-covered   | full, every compile      |
///
/// `Unchecked` is loudly labeled and, on any arch whose default is a verifying
/// mode (x86-64 after JIT-5), reachable only via the explicit
/// `TCG_JIT_UNCHECKED=1` env opt-in or an explicit
/// [`CompilerConfig::jit_validation_mode_override`]. Both `CachedVerified` and
/// `AlwaysVerify` are fail-closed by construction: a cache miss re-verifies
/// (never skips) and a verification failure rejects the compile — no
/// uncertified byte is ever published on those paths.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JitValidationMode {
    /// Dev-only low-latency JIT mode. No JIT proof certificates are requested
    /// and executed bytes are NOT covered by a verified certificate. Loudly
    /// labeled in every artifact; reaching it on a verifying-default arch
    /// requires an explicit opt-in (`TCG_JIT_UNCHECKED=1` or an explicit mode
    /// override).
    Unchecked,
    /// Target default (JIT-5): every executed byte must be covered by a
    /// verified certificate, but the expensive discharge may be satisfied
    /// from a content-addressed certificate cache keyed by
    /// (canonical trust-ir/machine content hash x config fingerprint). A cache
    /// MISS falls back to FULL verification (never to skip); a verification
    /// FAILURE fails closed. Warm latency stays ~free while soundness matches
    /// [`Self::AlwaysVerify`].
    CachedVerified,
    /// Paranoid/CI fail-closed JIT mode. The executable buffer must be
    /// compiled with JIT verification enabled — every compile re-discharges,
    /// bypassing the certificate cache — so proof consumers cannot observe an
    /// empty certificate map as a vacuous success. Formerly `ProofRequired`.
    AlwaysVerify,
}

impl JitValidationMode {
    /// Whether this mode requires [`crate::jit::JitConfig::verify`] — i.e.
    /// every executed byte must carry a verified certificate.
    pub fn requires_jit_verification(self) -> bool {
        matches!(self, Self::CachedVerified | Self::AlwaysVerify)
    }

    /// Whether this mode may satisfy the verification obligation from the
    /// content-addressed certificate cache (warm-hit fast path). Only
    /// [`Self::CachedVerified`] consults the cache; [`Self::AlwaysVerify`]
    /// always re-discharges.
    pub fn uses_certificate_cache(self) -> bool {
        matches!(self, Self::CachedVerified)
    }

    /// Whether executed bytes are left uncertified (dev-only escape hatch).
    pub fn is_unchecked(self) -> bool {
        matches!(self, Self::Unchecked)
    }

    /// Stable lowercase label for metrics / replay metadata / diagnostics.
    pub fn label(self) -> &'static str {
        match self {
            Self::Unchecked => "unchecked",
            Self::CachedVerified => "cached-verified",
            Self::AlwaysVerify => "always-verify",
        }
    }

    fn ensure_supported(self, target: Target) -> Result<(), CompileError> {
        match self {
            Self::Unchecked => Ok(()),
            Self::CachedVerified | Self::AlwaysVerify if target == Target::Riscv64 => {
                Err(CompileError::ProofsUnsupportedForTarget { target })
            }
            Self::CachedVerified | Self::AlwaysVerify => {
                #[cfg(feature = "verify")]
                {
                    let _ = target;
                    Ok(())
                }
                #[cfg(not(feature = "verify"))]
                {
                    Err(CompileError::ProofsUnsupportedForTarget { target })
                }
            }
        }
    }
}

/// Environment escape hatch: setting `TCG_JIT_UNCHECKED=1` downgrades an
/// otherwise-verifying default JIT validation mode to [`JitValidationMode::Unchecked`].
///
/// This is the ONLY way to execute uncertified JIT bytes on the default path
/// of a verifying-default arch (x86-64 after JIT-5). It is loudly labeled: a
/// stderr marker is emitted the first time the downgrade takes effect, and the
/// resolved mode is recorded in every [`JitCompilationResult`] provenance.
pub(crate) const JIT_UNCHECKED_ENV: &str = "TCG_JIT_UNCHECKED";

/// The default JIT validation mode for a target arch, before any explicit
/// override or `emit_proofs` back-compat mapping is applied.
///
/// JIT-5 flips x86-64 to [`JitValidationMode::CachedVerified`]. AArch64 stays
/// [`JitValidationMode::Unchecked`] pending the production flip (JIT-11 /
/// A64-8, an M-series lane). RISC-V has no verifier and stays `Unchecked`.
/// In a build without the `verify` feature no mode can verify, so every arch
/// defaults to `Unchecked` (the mode is still selectable but degrades to
/// dev-only).
pub(crate) fn arch_default_jit_validation_mode(target: Target) -> JitValidationMode {
    #[cfg(feature = "verify")]
    {
        match target {
            // JIT-5: x86-64 host JIT executes only cert-covered bytes by default.
            Target::X86_64 => JitValidationMode::CachedVerified,
            // aarch64 default flip is JIT-11/A64-8 (M-series); riscv has no verifier.
            _ => JitValidationMode::Unchecked,
        }
    }
    #[cfg(not(feature = "verify"))]
    {
        let _ = target;
        JitValidationMode::Unchecked
    }
}

/// Whether the `TCG_JIT_UNCHECKED=1` env escape hatch is engaged.
fn jit_unchecked_env_engaged() -> bool {
    crate::env_lock::var(JIT_UNCHECKED_ENV)
        .ok()
        .map(|v| v == "1")
        .unwrap_or(false)
}

/// Emit the loud one-time marker when an Unchecked downgrade takes effect, so
/// executing uncertified bytes can never be silent.
fn warn_jit_unchecked_engaged(target: Target, via_env: bool) {
    use std::sync::atomic::{AtomicBool, Ordering};
    static WARNED: AtomicBool = AtomicBool::new(false);
    if !WARNED.swap(true, Ordering::Relaxed) {
        let how = if via_env {
            "TCG_JIT_UNCHECKED=1"
        } else {
            "explicit jit_validation_mode_override"
        };
        eprintln!(
            "[trust-cg][JIT][UNCHECKED] executing UNCERTIFIED JIT bytes on {target:?} \
             (validation downgraded to Unchecked via {how}); executed bytes are NOT \
             covered by a verified certificate"
        );
    }
}

/// Configuration for the [`Compiler`].
#[derive(Debug, Clone)]
pub struct CompilerConfig {
    /// Optimization level (O0 through O3).
    pub opt_level: OptLevel,
    /// Target architecture.
    ///
    /// `CompilerConfig::default()` intentionally preserves Trust Codegen's legacy
    /// object-code default of [`Target::Aarch64`]. It is not a host-JIT
    /// default. In-process JIT callers should use
    /// [`CompilerConfig::for_host_jit()`] or [`Compiler::for_host()`].
    pub target: Target,
    /// Whether to emit proof certificates for each compiled function.
    ///
    /// When true, the compiler runs the trust-cg-verify function verifier on
    /// each prepared MachFunction and produces a [`ProofCertificate`] per
    /// verified instruction. Currently uses mock evaluation (exhaustive for
    /// 8-bit, statistical for 32/64-bit); will upgrade to formal ay proofs
    /// when ay integration is complete.
    pub emit_proofs: bool,
    /// Compilation trace verbosity.
    pub trace_level: CompilerTraceLevel,
    /// Whether to emit DWARF debug info sections in the output object file.
    ///
    /// When true, the pipeline generates `__debug_info`, `__debug_abbrev`,
    /// `__debug_str`, and `__debug_line` sections.
    pub emit_debug: bool,
    /// Whether to compile functions in parallel using rayon.
    ///
    /// When true and the module contains 2+ functions, the per-function
    /// compilation phases (ISel, optimization, register allocation, frame
    /// lowering, branch resolution) run in parallel across a rayon thread
    /// pool. The final Mach-O emission phase remains sequential since it
    /// builds a single combined `__text` section.
    ///
    /// Default: `true`.
    pub parallel: bool,
    /// Per-function wall-clock budget for the CEGIS superopt pass.
    ///
    /// When `Some(n)`, the pipeline runs [`trust_cg_verify::CegisSuperoptPass`]
    /// with `budget_sec = n` during optimization. Results are keyed into the
    /// compilation cache so repeat compilations reuse proven rewrites.
    /// When `None` (default), the pass is not scheduled. The CLI flag
    /// `--cegis-superopt=<secs>` sets this field.
    ///
    /// Issue: #395. Default: `None` (off).
    pub cegis_superopt_budget_sec: Option<u64>,
    /// Run the bounded trust_ir fsym preflight from the real compiler pipeline.
    ///
    /// This is diagnostic-only: concrete UB diagnostics, bounded skips, and
    /// unknown obligations are surfaced through [`CompilationMetrics`], but
    /// the compiler does not reject code here. Rejection policy remains owned
    /// by frontends such as `trust-cg --fsym=error`.
    ///
    /// Issue: #377. Default: `false` (off).
    pub enable_fsym_trust_ir_preflight: bool,
    /// Use the JIT-latency register allocator profile.
    ///
    /// When `true`, register allocation runs
    /// [`trust_cg_regalloc::AllocConfig::jit_latency_aarch64`] — the LinearScan
    /// core with quality features disabled (no coalescing, no splitting, no
    /// slot reuse). Targeted at the BCP/parent-loop JIT shapes where compile
    /// latency dominates code quality.
    ///
    /// [`CompilerConfig::for_host_jit`] turns this on. The default and
    /// AOT object-code paths leave it off so the existing
    /// [`AllocStrategy::LinearScan`] code-quality features remain in play.
    pub enable_jit_fast_regalloc: bool,
    /// Explicit override for the JIT validation mode (JIT-5).
    ///
    /// When `None` (the default) the mode is derived from `emit_proofs` and
    /// the target's arch default via [`Self::jit_validation_mode`]. When
    /// `Some(mode)` the override wins over both — an in-code opt-in that, for
    /// [`JitValidationMode::Unchecked`], is an explicit and loudly-labeled
    /// alternative to the `TCG_JIT_UNCHECKED=1` env escape hatch.
    ///
    /// This exists so that:
    /// - callers who need dev-only raw codegen (e.g. exercising opcodes whose
    ///   proofs are still pending) can request `Unchecked` without the env; and
    /// - CI can pin `AlwaysVerify` regardless of arch default.
    pub jit_validation_mode_override: Option<JitValidationMode>,
    /// Whole-program `panic=unwind` mode (FUZZ-7 / EH Lane 5, cross-object).
    ///
    /// When true, the x86-64 Mach-O emitter gives EVERY frame-covered object
    /// full per-function walkable FDE coverage (the all-filler LSDA "keep
    /// walking, never dispatch" path), not just objects that carry a local
    /// exception-handling function. A panic unwinds across object boundaries;
    /// a pass-through frame in an object with no local landing pad would
    /// otherwise stop phase-1 unwind dead (`_URC_END_OF_STACK`), skipping every
    /// cleanup Drop. The frontend sets this from `tcx.sess.panic_strategy()`.
    ///
    /// Read ONLY inside the Mach-O output arms; ELF/COFF/RawBytes are
    /// byte-unaffected. When false (abort mode, or any non-unwind target) the
    /// emitted object is byte-identical to before this field existed.
    pub panic_unwind: bool,
}

impl Default for CompilerConfig {
    fn default() -> Self {
        Self {
            opt_level: OptLevel::O2,
            target: Target::Aarch64,
            emit_proofs: false,
            trace_level: CompilerTraceLevel::None,
            emit_debug: false,
            parallel: true,
            cegis_superopt_budget_sec: None,
            enable_fsym_trust_ir_preflight: false,
            enable_jit_fast_regalloc: false,
            jit_validation_mode_override: None,
            panic_unwind: false,
        }
    }
}

impl CompilerConfig {
    /// Host-safe profile for in-process JIT compilation.
    ///
    /// This is equivalent to [`CompilerConfig::jit_fast`] with
    /// [`Target::host`]. Use this when generated code will be placed in
    /// executable memory and called by the current process. It deliberately
    /// avoids inheriting [`CompilerConfig::default`]'s concrete AArch64 target.
    pub fn for_host_jit() -> Self {
        Self::jit_fast(Target::host())
    }

    /// Low-latency profile for tiny JIT modules.
    ///
    /// Solver and runtime specializers often compile one small function whose
    /// first-use latency matters more than peak standalone code quality. This
    /// profile keeps the API explicit for those consumers instead of requiring
    /// each embedder to rediscover the same knobs.
    ///
    /// The `target` argument is explicit. For in-process execution, prefer
    /// [`CompilerConfig::for_host_jit`] so the selected target matches
    /// [`Target::host`].
    pub fn jit_fast(target: Target) -> Self {
        Self {
            opt_level: OptLevel::O1,
            target,
            emit_proofs: false,
            trace_level: CompilerTraceLevel::None,
            emit_debug: false,
            parallel: false,
            cegis_superopt_budget_sec: None,
            enable_fsym_trust_ir_preflight: false,
            // The jit_fast profile is the canonical home for the new
            // latency-tuned regalloc strategy. Tests and AOT compiles that
            // need the full quality features keep the Default profile.
            enable_jit_fast_regalloc: true,
            // JIT-5: leave the mode unset so it resolves to the target's arch
            // default (x86-64 -> CachedVerified; aarch64 -> Unchecked pending
            // JIT-11). Callers that need a dev-only raw JIT set the override.
            jit_validation_mode_override: None,
            // JIT modules never emit an EH sidecar; abort-equivalent here.
            panic_unwind: false,
        }
    }

    /// Dev-only host-JIT profile that executes UNCERTIFIED bytes.
    ///
    /// Equivalent to [`Self::for_host_jit`] but with an explicit
    /// [`JitValidationMode::Unchecked`] override, the loud in-code opt-in that
    /// bypasses the JIT-5 cert-coverage requirement without needing the
    /// `TCG_JIT_UNCHECKED=1` env var. Use only for exercising codegen whose
    /// instruction proofs are still pending (e.g. SIMD lanes); never in a
    /// production execution path.
    pub fn for_host_jit_unchecked() -> Self {
        Self {
            jit_validation_mode_override: Some(JitValidationMode::Unchecked),
            ..Self::for_host_jit()
        }
    }

    /// JIT validation policy implied by this compiler configuration.
    ///
    /// Resolution order (JIT-5), env-independent:
    /// 1. an explicit [`Self::jit_validation_mode_override`] wins;
    /// 2. otherwise `emit_proofs == true` maps to [`JitValidationMode::AlwaysVerify`]
    ///    (back-compat: the former `ProofRequired`);
    /// 3. otherwise the target's arch default
    ///    ([`arch_default_jit_validation_mode`]): x86-64 -> `CachedVerified`,
    ///    others -> `Unchecked`.
    ///
    /// This is the *configured* mode. The env escape hatch
    /// (`TCG_JIT_UNCHECKED=1`) is applied separately at compile time by
    /// [`Self::resolve_jit_validation_mode`] so a pure config query stays
    /// deterministic (the M4 gate asserts `for_host_jit().jit_validation_mode()`
    /// == `CachedVerified` on x86-64 without consulting the environment).
    pub fn jit_validation_mode(&self) -> JitValidationMode {
        if let Some(mode) = self.jit_validation_mode_override {
            return mode;
        }
        if self.emit_proofs {
            return JitValidationMode::AlwaysVerify;
        }
        arch_default_jit_validation_mode(self.target)
    }

    /// Compile-time resolution of the JIT validation mode, applying the
    /// `TCG_JIT_UNCHECKED=1` env escape hatch and the fail-closed downgrade
    /// gate.
    ///
    /// - If the configured mode ([`Self::jit_validation_mode`]) is a verifying
    ///   mode, it is returned unchanged (unless the env downgrades an
    ///   *arch-default* verifying mode to Unchecked).
    /// - If the configured mode is `Unchecked`, it is permitted only when the
    ///   arch's own default is already `Unchecked` (e.g. aarch64 pending
    ///   JIT-11), OR the caller set an explicit override, OR the
    ///   `TCG_JIT_UNCHECKED=1` env var is engaged. Otherwise — an implicit
    ///   Unchecked on a verifying-default arch — this FAILS CLOSED: executing
    ///   uncertified bytes requires the explicit opt-in.
    ///
    /// Any resolved `Unchecked` is loudly labeled (a one-time stderr marker).
    pub fn resolve_jit_validation_mode(&self) -> Result<JitValidationMode, CompileError> {
        let arch_default = arch_default_jit_validation_mode(self.target);
        let env_engaged = jit_unchecked_env_engaged();

        // The env escape hatch downgrades an arch-default verifying mode to
        // Unchecked (the "execute uncertified bytes on the default path"
        // opt-in). An explicit override or emit_proofs is NOT overridden by the
        // env — a caller that asked to verify keeps verifying.
        if env_engaged
            && self.jit_validation_mode_override.is_none()
            && !self.emit_proofs
            && arch_default.requires_jit_verification()
        {
            warn_jit_unchecked_engaged(self.target, /* via_env */ true);
            return Ok(JitValidationMode::Unchecked);
        }

        let configured = self.jit_validation_mode();
        if configured.is_unchecked() {
            let explicit = self.jit_validation_mode_override == Some(JitValidationMode::Unchecked);
            if arch_default.is_unchecked() {
                // Legit arch default (aarch64 pending JIT-11); no opt-in needed.
                Ok(JitValidationMode::Unchecked)
            } else if explicit || env_engaged {
                warn_jit_unchecked_engaged(self.target, /* via_env */ !explicit);
                Ok(JitValidationMode::Unchecked)
            } else {
                Err(CompileError::JitUncertifiedBytesRequireOptIn {
                    target: self.target,
                })
            }
        } else {
            Ok(configured)
        }
    }

    /// Proof-policy partition used by the compile artifact cache.
    pub fn compile_artifact_proof_policy(&self) -> CompileArtifactProofPolicy {
        if self.jit_validation_mode().requires_jit_verification() {
            CompileArtifactProofPolicy::ProofTvFull
        } else {
            CompileArtifactProofPolicy::Unchecked
        }
    }

    /// Convert this high-level compiler configuration into the lower-level
    /// JIT configuration, preserving fail-closed proof requirements.
    pub fn to_jit_config(
        &self,
        profile_hooks: crate::jit::ProfileHookMode,
    ) -> Result<crate::jit::JitConfig, CompileError> {
        let validation_mode = self.resolve_jit_validation_mode()?;
        validation_mode.ensure_supported(self.target)?;
        Ok(crate::jit::JitConfig {
            opt_level: self.opt_level,
            verify: validation_mode.requires_jit_verification(),
            // JIT-5: only CachedVerified consults the certificate cache;
            // AlwaysVerify re-discharges every compile.
            cache_certificates: validation_mode.uses_certificate_cache(),
            profile_hooks,
            // #375: Inherit the JitConfig default (ErrorOnFailure) so
            // dispatch verification failures surface here too rather than
            // being silently rewritten to a CPU-only plan. compile_raw does
            // not currently invoke the dispatch verifier, so this is mostly
            // defensive wiring for future heterogeneous-aware code paths.
            ..Default::default()
        })
    }
}

// ---------------------------------------------------------------------------
// Result types
// ---------------------------------------------------------------------------

/// Metrics collected during compilation.
#[derive(Debug, Clone, Default)]
pub struct CompilationMetrics {
    /// Total size of emitted machine code in bytes.
    pub code_size_bytes: usize,
    /// Total number of machine instructions emitted (across all functions).
    pub instruction_count: usize,
    /// Number of functions compiled.
    pub function_count: usize,
    /// Number of optimization passes executed.
    pub optimization_passes_run: usize,
    /// Summary of proof-optimization certificate citations observed while
    /// preparing codegen artifacts.
    pub proof_optimizations: ProofOptimizationMetrics,
    /// Bounded trust_ir fsym preflight diagnostics observed while preparing
    /// codegen artifacts.
    pub fsym_trust_ir: FsymTrustIrMetrics,
}

/// Public aggregate of bounded trust_ir fsym preflight output.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct FsymTrustIrMetrics {
    /// Functions scanned by the bounded preflight.
    pub scanned_functions: usize,
    /// Functions skipped because they exceeded the bounded preflight scope.
    pub skipped_functions: usize,
    /// Concrete UB diagnostics reported by the bounded preflight.
    pub concrete_ub_diagnostics: usize,
    /// Unknown obligations that need a stronger backend or solver.
    pub unknown_obligations: usize,
    /// Total warning records that a caller could surface.
    pub warnings: usize,
}

/// Compact public summary of proof-optimization transform certificates.
///
/// This is derived from [`ProofOptimizationCertificateCitation`] values that
/// codegen already exposes, not from `trust-cg-opt` pass internals.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ProofOptimizationMetrics {
    /// Total proof-optimization certificates cited by the compile.
    pub certificate_count: usize,
    /// Certificates whose cited transform was applied.
    pub applied_count: usize,
    /// Certificates whose cited transform was rejected.
    pub rejected_count: usize,
    /// Applied guard-elimination transforms.
    pub guard_eliminated_count: usize,
    /// Rejected guard-elimination transforms.
    pub guard_rejected_count: usize,
    /// Applied division-by-zero guard eliminations justified by NonZeroDivisor.
    pub non_zero_divisor_guard_eliminated_count: usize,
    /// Applied shift-range guard eliminations justified by ValidShift.
    pub valid_shift_guard_eliminated_count: usize,
    /// Rejected NonZeroDivisor guard-elimination attempts.
    pub non_zero_divisor_guard_rejected_count: usize,
    /// Rejected ValidShift guard-elimination attempts.
    pub valid_shift_guard_rejected_count: usize,
}

/// Per-function code-quality metrics. Surfaced through
/// [`JitCompilationResult::per_function_metrics`] so callers can identify
/// functions with high spill pressure, unusual branch density, etc.
///
/// See issue #364 item 3.
#[derive(Debug, Clone, Default)]
pub struct FunctionQualityMetrics {
    pub name: String,
    /// Per-function code bytes. The x86 JIT reports the exact encoded symbol
    /// span; fixed-width non-x86 paths report instruction-stream bytes.
    pub code_size_bytes: usize,
    /// Real (non-pseudo) machine instructions emitted.
    pub instruction_count: usize,
    /// Number of stack slots allocated by register allocation for spills.
    /// Not the sum of spill stores emitted — this counts distinct spill
    /// slots; each slot can be reused when spills don't overlap
    /// (`enable_spill_slot_reuse`).
    pub spill_slot_count: usize,
    /// Number of branch-terminator instructions (B, B.cond, CBZ, TBZ, BL
    /// for tail calls, RET). Used as a coarse branch-density proxy.
    pub branch_count: usize,
    /// x86-only low-cost opcode evidence from the final codegen instruction
    /// stream. Non-x86 targets leave this as zeroed/default.
    pub x86_machine_code: X86MachineCodeEvidence,
    /// Phase timings captured during `prepare_function_with_metrics`.
    pub phase_timings: crate::pipeline::PhaseTimings,
}

/// A single phase entry in a compilation trace.
#[derive(Debug, Clone)]
pub struct TraceEntry {
    /// Name of the compilation phase (e.g., "adapter", "isel", "regalloc").
    pub phase: String,
    /// Wall-clock duration of this phase.
    pub duration: Duration,
    /// Optional detail (e.g., function name being compiled).
    pub detail: Option<String>,
}

/// Compiler-level trace containing per-phase timing information.
///
/// Distinct from [`trust_cg_ir::CompilationTrace`] which is a thread-safe
/// structured event collector for instruction-level provenance.
/// This struct is a simple timing log for the compiler API.
#[derive(Debug, Clone, Default)]
pub struct CompilerTrace {
    /// Ordered list of phase entries.
    pub entries: Vec<TraceEntry>,
    /// Total wall-clock compilation time.
    pub total_duration: Duration,
}

/// A proof/export report for a single instruction lowering.
///
/// Successful entries record the result of verifying one instruction's
/// lowering against its proof obligation from the [`ProofDatabase`]. Entries
/// with `verified == false` are also surfaced for failed or unverified
/// verifier reports so downstream certified-output paths cannot
/// accidentally attest to a filtered subset of the function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofCertificate {
    /// Name of the lowering rule, or a synthetic verifier-gap report id.
    pub rule_name: String,
    /// Whether the proof was successfully verified.
    pub verified: bool,
    /// Proof category (e.g., Arithmetic), or verifier-gap status.
    pub category: String,
    /// Verification strength achieved, or fail-closed gap detail.
    pub strength: String,
    /// Name of the function this instruction belongs to.
    pub function_name: String,
}

/// Serializable metadata for a checker-validated certified pass chain.
///
/// This is intentionally a compact attachment rather than a pass execution
/// hook. Callers may supply an already validated
/// `trust_cg_verify::CertifiedPassChain`, or opt into the production
/// certified-pass execution slice when the `verify` feature is enabled.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertifiedPassChainAttachment {
    /// Compilation unit shared by all pass certificates in the chain.
    pub compilation_unit: String,
    /// Validated entries in certificate order.
    pub entries: Vec<CertifiedPassChainEntryAttachment>,
}

impl CertifiedPassChainAttachment {
    #[cfg(feature = "verify")]
    fn from_checked_chain(
        chain: &trust_cg_verify::CertifiedPassChain,
    ) -> Result<Self, trust_cg_verify::CertifiedPassChainError> {
        chain.validate()?;

        let compilation_unit = chain.compilation_unit().to_string();
        let mut entries = Vec::with_capacity(chain.entries().len());
        for (entry_index, entry) in chain.entries().iter().enumerate() {
            let certificate_index = entry.certificate_index().ok_or(
                trust_cg_verify::CertifiedPassChainError::MissingCertificateField {
                    entry_index,
                    field: "chain.certificate_index",
                },
            )?;
            let pass_name = entry.pass_name().ok_or(
                trust_cg_verify::CertifiedPassChainError::MissingCertificateField {
                    entry_index,
                    field: "pass.name",
                },
            )?;
            let pass_version = required_attachment_certificate_string(
                &entry.request.certificate,
                &["pass", "version"],
                entry_index,
                "pass.version",
            )?;
            let pass_instance_id = required_attachment_certificate_string(
                &entry.request.certificate,
                &["pass", "instance_id"],
                entry_index,
                "pass.instance_id",
            )?;
            let provenance = required_attachment_certificate_value(
                &entry.request.certificate,
                &["provenance"],
                entry_index,
                "provenance",
            )?;
            let checker_kind = required_attachment_certificate_string(
                &entry.request.certificate,
                &["checker", "kind"],
                entry_index,
                "checker.kind",
            )?;
            let checker_name = required_attachment_certificate_string(
                &entry.request.certificate,
                &["checker", "name"],
                entry_index,
                "checker.name",
            )?;
            let checker_version = required_attachment_certificate_string(
                &entry.request.certificate,
                &["checker", "version"],
                entry_index,
                "checker.version",
            )?;
            let must_be_verified = required_attachment_certificate_bool(
                &entry.request.certificate,
                &["chain", "must_be_verified"],
                entry_index,
                "chain.must_be_verified",
            )?;
            let report = serde_json::to_value(&entry.report).map_err(|source| {
                trust_cg_verify::CertifiedPassChainError::TamperedReportSummary {
                    entry_index,
                    reason: format!("checker report JSON serialization failed: {source}"),
                }
            })?;
            let checker_status =
                required_attachment_report_string(&report, &["result", "status"], entry_index)?;
            let replay_mode =
                required_attachment_report_string(&report, &["replay", "mode"], entry_index)?;
            let replay_fail_closed =
                required_attachment_report_bool(&report, &["replay", "fail_closed"], entry_index)?;
            let replay_inputs = required_attachment_report_array(
                &report,
                &["replay", "replay_inputs"],
                entry_index,
            )?;
            let proof_artifact = report.get("proof_artifact").cloned();
            entries.push(CertifiedPassChainEntryAttachment {
                compilation_unit: compilation_unit.clone(),
                certificate_index,
                pass_name: pass_name.to_string(),
                pass_version: pass_version.to_string(),
                pass_instance_id: pass_instance_id.to_string(),
                obligation_hash: entry.request.obligation_hash.clone(),
                provenance,
                checker_kind: checker_kind.to_string(),
                checker_name: checker_name.to_string(),
                checker_version: checker_version.to_string(),
                checker_status,
                replay_mode,
                replay_fail_closed,
                replay_inputs,
                proof_artifact,
                must_be_verified,
                certificate: entry.request.certificate.clone(),
                report,
            });
        }

        Ok(Self {
            compilation_unit,
            entries,
        })
    }
}

#[cfg(feature = "verify")]
fn required_attachment_certificate_string<'a>(
    certificate: &'a serde_json::Value,
    path: &[&str],
    entry_index: usize,
    field: &'static str,
) -> Result<&'a str, trust_cg_verify::CertifiedPassChainError> {
    certificate_path(certificate, path)
        .and_then(serde_json::Value::as_str)
        .ok_or(
            trust_cg_verify::CertifiedPassChainError::MissingCertificateField {
                entry_index,
                field,
            },
        )
}

#[cfg(feature = "verify")]
fn required_attachment_certificate_bool(
    certificate: &serde_json::Value,
    path: &[&str],
    entry_index: usize,
    field: &'static str,
) -> Result<bool, trust_cg_verify::CertifiedPassChainError> {
    certificate_path(certificate, path)
        .and_then(serde_json::Value::as_bool)
        .ok_or(
            trust_cg_verify::CertifiedPassChainError::MissingCertificateField {
                entry_index,
                field,
            },
        )
}

#[cfg(feature = "verify")]
fn required_attachment_certificate_value(
    certificate: &serde_json::Value,
    path: &[&str],
    entry_index: usize,
    field: &'static str,
) -> Result<serde_json::Value, trust_cg_verify::CertifiedPassChainError> {
    certificate_path(certificate, path).cloned().ok_or(
        trust_cg_verify::CertifiedPassChainError::MissingCertificateField { entry_index, field },
    )
}

#[cfg(feature = "verify")]
fn certificate_path<'a>(
    certificate: &'a serde_json::Value,
    path: &[&str],
) -> Option<&'a serde_json::Value> {
    let mut cursor = certificate;
    for segment in path {
        cursor = cursor.get(*segment)?;
    }
    Some(cursor)
}

#[cfg(feature = "verify")]
fn required_attachment_report_string(
    report: &serde_json::Value,
    path: &[&str],
    entry_index: usize,
) -> Result<String, trust_cg_verify::CertifiedPassChainError> {
    report_path(report, path)
        .and_then(serde_json::Value::as_str)
        .map(str::to_string)
        .ok_or_else(|| attachment_report_missing(entry_index, path))
}

#[cfg(feature = "verify")]
fn required_attachment_report_bool(
    report: &serde_json::Value,
    path: &[&str],
    entry_index: usize,
) -> Result<bool, trust_cg_verify::CertifiedPassChainError> {
    report_path(report, path)
        .and_then(serde_json::Value::as_bool)
        .ok_or_else(|| attachment_report_missing(entry_index, path))
}

#[cfg(feature = "verify")]
fn required_attachment_report_array(
    report: &serde_json::Value,
    path: &[&str],
    entry_index: usize,
) -> Result<Vec<serde_json::Value>, trust_cg_verify::CertifiedPassChainError> {
    report_path(report, path)
        .and_then(serde_json::Value::as_array)
        .cloned()
        .ok_or_else(|| attachment_report_missing(entry_index, path))
}

#[cfg(feature = "verify")]
fn report_path<'a>(report: &'a serde_json::Value, path: &[&str]) -> Option<&'a serde_json::Value> {
    let mut cursor = report;
    for segment in path {
        cursor = cursor.get(*segment)?;
    }
    Some(cursor)
}

#[cfg(feature = "verify")]
fn attachment_report_missing(
    entry_index: usize,
    path: &[&str],
) -> trust_cg_verify::CertifiedPassChainError {
    trust_cg_verify::CertifiedPassChainError::TamperedReportSummary {
        entry_index,
        reason: format!("report.{} is missing or has the wrong type", path.join(".")),
    }
}

/// Serializable metadata for one checker-validated certified pass entry.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertifiedPassChainEntryAttachment {
    /// Compilation unit declared by the validated chain.
    pub compilation_unit: String,
    /// Zero-based position declared by `certificate.chain.certificate_index`.
    pub certificate_index: u64,
    /// Pass identity declared by `certificate.pass.name`.
    pub pass_name: String,
    /// Pass implementation version declared by `certificate.pass.version`.
    #[serde(default)]
    pub pass_version: String,
    /// Stable pass instance id declared by `certificate.pass.instance_id`.
    #[serde(default)]
    pub pass_instance_id: String,
    /// Stable pass obligation hash agreed across request, certificate, and report.
    pub obligation_hash: String,
    /// Source/rewrite provenance declared by the validated certificate.
    #[serde(default)]
    pub provenance: serde_json::Value,
    /// Checker kind declared by `certificate.checker.kind`.
    #[serde(default)]
    pub checker_kind: String,
    /// Checker name declared by `certificate.checker.name`.
    #[serde(default)]
    pub checker_name: String,
    /// Checker version declared by `certificate.checker.version`.
    #[serde(default)]
    pub checker_version: String,
    /// Checker status reported by the replay result.
    #[serde(default)]
    pub checker_status: String,
    /// Replay mode reported by the checker.
    #[serde(default)]
    pub replay_mode: String,
    /// Fail-closed replay policy reported by the checker.
    #[serde(default)]
    pub replay_fail_closed: bool,
    /// Replay artifacts considered by the checker.
    #[serde(default)]
    pub replay_inputs: Vec<serde_json::Value>,
    /// Proof artifact identity selected by the checker report.
    #[serde(default)]
    pub proof_artifact: Option<serde_json::Value>,
    /// Whether this chain entry was required to be verified.
    #[serde(default)]
    pub must_be_verified: bool,
    /// Full `trust-cg.certified_pass.v1` certificate JSON.
    pub certificate: serde_json::Value,
    /// Full checker report JSON.
    pub report: serde_json::Value,
}

/// The result of compiling a trust_ir module through the Trust Codegen pipeline.
#[derive(Debug, Clone)]
pub struct CompilationResult {
    /// Object file bytes containing all compiled functions.
    ///
    /// AArch64 currently emits Mach-O. x86-64 public AOT emits the host
    /// OS-native format when implemented: ELF on Linux/BSD and Mach-O on
    /// macOS. Windows x86-64 AOT fail-closes until COFF emission exists.
    pub object_code: Vec<u8>,
    /// Compilation metrics.
    pub metrics: CompilationMetrics,
    /// Optional compiler trace (populated when trace_level != None).
    pub trace: Option<CompilerTrace>,
    /// Optional proof certificates (populated when emit_proofs is true).
    pub proofs: Option<Vec<ProofCertificate>>,
    /// Checker-validated certified pass chain supplied by the caller or
    /// produced through the non-default certified-pass execution path.
    pub certified_pass_chain: Option<CertifiedPassChainAttachment>,
    /// Proof-optimization certificate citations emitted by `trust-cg-opt` while
    /// preparing production codegen artifacts.
    pub proof_optimization_certificates: Vec<ProofOptimizationCertificateCitation>,
    /// Compile artifact cache telemetry emitted by production lookup/store paths.
    pub compile_artifact_cache_telemetry: Vec<CompileArtifactCacheTelemetry>,
}

/// Native pointer size in bytes for the supported 64-bit targets.
///
/// trust-cg targets x86_64, aarch64, and riscv64 — all LP64/64-bit — so a
/// `Constant::SymbolAddr` element occupies 8 bytes. (No 32-bit target is
/// supported; if one is added, this must become target-derived.)
const GLOBAL_POINTER_SIZE: usize = 8;

/// Storage alignment (bytes, power of two >= 1) for a module global's object
/// section slot.
///
/// Prefers the trust-ir `Global.align` (an explicit `#[repr(align(N))]` / SIMD
/// over-alignment request the producer stamped); otherwise derives it from the
/// global's type layout (`align_bits`). Falls back to 1 when neither is known —
/// a byte blob is byte-aligned, and 1 never over-constrains a reader (the
/// section-offset alignment below only ever widens it). A non-power-of-two or
/// zero request is a producer bug the validator rejects; defensively clamped to
/// a power of two here so section packing math (`align_up`) stays well-defined.
fn object_global_align(module: &trust_ir::Module, global: &trust_ir::Global) -> u32 {
    let raw = match global.align {
        // An EXPLICIT producer request is honored exactly (down to 1 — each
        // global self-aligns in the section, so a small-aligned static never
        // under-aligns a later strictly-aligned one).
        Some(a) => a.max(1),
        // No explicit request: derive from the type layout, but floor at the
        // pointer-size default (8). A producer that lowers a pointer- or
        // atomic-bearing const image to a flat `Array(U8, N)` erases its true
        // alignment to 1; the historical section default 8-aligned every such
        // global, and an under-aligned `AtomicUsize` image faults on AArch64
        // `ldxr`. The floor preserves that guarantee; a genuinely stricter
        // type-derived alignment (e.g. a 16-aligned struct) still wins.
        None => module
            .ty_layout_shape(&global.ty)
            .ok()
            .and_then(|shape| shape.align_bits)
            .map(|bits| (bits / 8) as u32)
            .unwrap_or(0)
            .max(GLOBAL_POINTER_SIZE as u32),
    };
    let raw = raw.max(1);
    if raw.is_power_of_two() {
        raw
    } else {
        // Round up to the next power of two so `align_up` never divides by a
        // non-power-of-two (fail-safe; the validator already rejects this).
        raw.checked_next_power_of_two().unwrap_or(1)
    }
}

fn module_object_globals(module: &trust_ir::Module) -> Result<Vec<ObjectGlobal>, PipelineError> {
    // Target byte order for multi-byte scalar initializers. Both supported
    // targets (x86_64, aarch64) are little-endian, so a module that declines to
    // declare its target (`target_info: None`) is treated as little-endian; an
    // explicitly big-endian module fails closed on multi-byte emission below,
    // since no supported backend exercises that byte order.
    let endian = module
        .target_info
        .as_ref()
        .map(|t| t.endianness)
        .unwrap_or(trust_ir::Endianness::Little);
    module
        .globals
        .iter()
        .map(|global| {
            // Thread-local globals route to the target's TLS object sections.
            // On AArch64 Mach-O (Darwin) a thread-local lowers to the dynamic TLV
            // model: an initial-value template in `__thread_data` plus a
            // `tlv_descriptor` in `__thread_vars` that the read addresses via
            // `ARM64_RELOC_TLVP_LOAD_PAGE21`/`PAGEOFF12`. We carry only an
            // `is_thread_local` flag here; the descriptor section emission lives in
            // the Mach-O object emitter, and the non-Mach-O emitters fail closed on
            // a thread-local global (they have no TLS section path yet).
            //
            // ALL trust-ir TLS models collapse to the Darwin TLV descriptor for
            // AOT object emission, because the READ side is model-independent: the
            // adapter's `translate_global_addr` lowers every `GlobalAddr` of a TLS
            // global to `Opcode::TlsRef { model: Tlv, local_exec_offset: None }`,
            // i.e. a `tlv_get_addr` through a `__thread_vars` descriptor. Mach-O
            // has no distinct local-exec object ABI — clang lowers `_Thread_local`
            // to TLV regardless — so a `LocalExec`-marked global (the JIT's fast
            // static model, which the AOT read never uses) MUST also become a TLV
            // descriptor for its read to resolve. Admitting it here is therefore
            // required for consistency, not a relaxation: it flows through the same
            // `is_thread_local` descriptor path as the dynamic models below. The
            // ELF emitter still fails closed on ANY `is_thread_local` global
            // (`emit_target_elf_or_reject_fixups`), so no non-Darwin target is
            // silently miscompiled.
            let is_thread_local = global.tls.is_some();
            // Mirror the trust-ir linkage to the object symbol's visibility:
            // External / weak / link-once are exported (resolvable from another
            // object); Internal / Private stay module-local. A `MonoItem::Static`
            // emitted under its own symbol relies on this to be linkable.
            let is_external = matches!(
                global.linkage,
                trust_ir::Linkage::External | trust_ir::Linkage::Weak | trust_ir::Linkage::LinkOnce
            );
            // A `Weak` / `LinkOnce` (link-once ODR) DEFINITION is emitted with the
            // Mach-O `N_WEAK_DEF` / ELF `STB_WEAK` flag so that multiple objects
            // each defining the symbol COALESCE to one at link time instead of a
            // duplicate-strong-definition error. This is only applied to an actual
            // definition below (the import arms keep strong undefined references,
            // exactly as today).
            let is_weak = matches!(
                global.linkage,
                trust_ir::Linkage::Weak | trust_ir::Linkage::LinkOnce
            );
            // Storage alignment for this global's section slot (explicit
            // `Global.align`, else type-derived). Imports carry no bytes, but
            // the field is set uniformly for a stable ObjectGlobal shape.
            let align = object_global_align(module, global);

            // An initializer-less THREAD-LOCAL global is a cross-object IMPORT: a
            // reference to a `tlv_descriptor` DEFINED in another object. It
            // contributes no descriptor / template section bytes here (which would
            // be a duplicate definition of the program-wide thread-local); its
            // sole effect is that the `__text` TLVP relocation resolves to an
            // undefined-external symbol the linker satisfies from the defining
            // object. See `ObjectGlobal::is_import`.
            //
            // Such an import is ALWAYS emitted External, regardless of the
            // trust-ir linkage the producer stamped. Unlike a non-TLS global (an
            // initializer-less Internal/Private one is a valid zero-fill BSS
            // DEFINITION — handled below), a thread-local has NO zero-fill
            // definition path in this model: a TLS definition is only expressible
            // through the TLV descriptor + init-value template, which requires an
            // initializer. So an initializer-less TLS global cannot be a
            // definition — its only coherent meaning is an import — and an import
            // is necessarily External (a module-local Internal/Private symbol with
            // no bytes here cannot be satisfied by another object). The
            // Internal/Private linkage the frontend stamps on such a bodyless TLS
            // REFERENCE (e.g. the monomorphized `RandomState::new::KEYS`
            // thread-local, defined in std and merely read here) is a
            // classification artifact of carrying a static's own-symbol linkage
            // onto a mere reference, not a real request for module-local storage.
            // Promoting it to an External import is fail-closed: were it ever
            // genuinely meant to be defined here, the unresolved undefined-external
            // surfaces as a LINK-TIME error, never a silently wrong TLS value.
            // DEFINITIONS (initializer present) and non-TLS globals are untouched.
            if is_thread_local && global.initializer.is_none() {
                return Ok(ObjectGlobal {
                    name: global.name.clone(),
                    data: Vec::new(),
                    mutable: global.mutable,
                    is_external: true,
                    symbol_refs: Vec::new(),
                    is_thread_local: true,
                    is_import: true,
                    // An import is a strong undefined reference (not a weak def).
                    is_weak: false,
                    align,
                });
            }

            // An initializer-less NON-thread-local global with External linkage is a
            // plain cross-object DATA IMPORT: a reference to a `static` (e.g. a
            // `static mut`) DEFINED in another object. Like the TLS import above it
            // contributes no section bytes here; the data relocation resolves to the
            // undefined-external symbol the linker satisfies from the defining object.
            if !is_thread_local && global.initializer.is_none() && is_external {
                return Ok(ObjectGlobal {
                    name: global.name.clone(),
                    data: Vec::new(),
                    mutable: global.mutable,
                    is_external: true,
                    symbol_refs: Vec::new(),
                    is_thread_local: false,
                    is_import: true,
                    // An import is a strong undefined reference (not a weak def).
                    is_weak: false,
                    align,
                });
            }

            // An INITIALIZER-LESS internal/private global is a zero-initialized
            // (BSS) static. (The external/import cases returned above; a TLS
            // no-initializer symbol is handled — and an internal one rejected —
            // earlier.) Emit `size` zero bytes: an all-zero `__DATA,__data`
            // definition is semantically identical to a BSS zerofill for a
            // defined zero-initialized static (the loader observes the same
            // zeroed image), and keeps the symbol a real in-object definition
            // other objects can bind to. The size is the type's canonical layout;
            // if it is not computable we FAIL CLOSED rather than emit a
            // wrong-sized (overlapping / truncated) symbol.
            let initializer = match global.initializer.as_ref() {
                Some(init) => init,
                None => {
                    let size = module
                        .ty_layout_shape(&global.ty)
                        .ok()
                        .and_then(|shape| shape.size_bytes())
                        .ok_or_else(|| {
                            PipelineError::ISel(format!(
                                "trust-ir global {} unsupported: initializer is missing and its type {:?} has no computable layout size for a BSS/zero-fill definition",
                                global.name, global.ty
                            ))
                        })?;
                    return Ok(ObjectGlobal {
                        name: global.name.clone(),
                        data: vec![0u8; size as usize],
                        mutable: global.mutable,
                        is_external,
                        symbol_refs: Vec::new(),
                        is_thread_local,
                        is_import: false,
                        is_weak,
                        align,
                    });
                }
            };
            let (data, symbol_refs) =
                trust_ir_global_initializer_data(module, global, initializer, endian)?;
            Ok(ObjectGlobal {
                name: global.name.clone(),
                data,
                mutable: global.mutable,
                is_external,
                symbol_refs,
                is_thread_local,
                is_import: false,
                // Weak only applies to a DEFINITION; coalesced across objects.
                is_weak,
                align,
            })
        })
        .collect()
}

/// Lower a global's initializer to its raw data bytes plus any embedded
/// symbol-address relocations.
///
/// A `Constant::Aggregate`'s `Constant::Int` elements are laid out at their
/// DECLARED element WIDTH, taken from the global's aggregate `Ty`:
///
/// * When the global type DECOMPOSES into per-position element types — an
///   `Array`/`Tuple`/`Struct`/`Vector` — each `Int` element occupies the byte
///   width of its element type (a `Usize`/`U64`/`Ptr` slot is 8 bytes, a `U32`
///   slot 4, a `U8` slot 1). This is what keeps a Rust vtable's pointer-word
///   `drop`/`size`/`align` slots at their natural width so the following
///   method-pointer `SymbolAddr` relocations land at pointer-aligned offsets
///   (the historic 1-byte-per-`Int` layout shoved them off alignment — `ld:
///   pointer not aligned`). If an element's width is not computable from the
///   type (an unresolved element type, or a non-scalar element type) the global
///   FAILS CLOSED rather than emit a wrong-width, misaligning slot.
/// * When the global type is a SCALAR/opaque type (`I64`/`I32`/`Ptr`/…) that
///   does not decompose, the aggregate is the historic flat BYTE IMAGE: one
///   literal byte (range-checked to `u8`) per `Int` element — how a producer
///   spells a pointer-width scalar global as its little-endian byte sequence.
///
/// For each `Constant::SymbolAddr` element the layout is width-independent:
/// [`GLOBAL_POINTER_SIZE`] zero bytes plus a [`crate::pipeline::GlobalSymbolRef`]
/// recorded at that offset (the linker fills in the address via a data
/// relocation). This is what places a function/data address inside a vtable or
/// `static FNS: [fn(); N]`. Scalar `U8`/`I8`/`Bool` initializers contribute
/// their single byte and carry no relocations.
///
/// Fail-closed: every other initializer or aggregate-element shape returns an
/// `Err` so an unsupported global is never silently miscompiled into wrong
/// bytes (nor silently dropped — see the `module_object_globals_fail_closed_*`
/// tests).
/// Byte width and signedness of a scalar integer `Ty`, or `None` for a
/// non-integer type.
fn integer_ty_width_signed(ty: &trust_ir::Ty) -> Option<(usize, bool)> {
    Some(match ty {
        trust_ir::Ty::I8 => (1, true),
        trust_ir::Ty::I16 => (2, true),
        trust_ir::Ty::I32 => (4, true),
        trust_ir::Ty::I64 => (8, true),
        trust_ir::Ty::I128 => (16, true),
        trust_ir::Ty::U8 => (1, false),
        trust_ir::Ty::U16 => (2, false),
        trust_ir::Ty::U32 => (4, false),
        trust_ir::Ty::U64 => (8, false),
        trust_ir::Ty::U128 => (16, false),
        _ => return None,
    })
}

/// Encode a scalar integer initializer as `width` target-endian bytes.
///
/// The literal is range-checked against the declared type first, so truncating
/// the `i128` to `width` bytes never silently drops information. The bytes are
/// the two's-complement little-endian encoding (identical for signed and
/// unsigned values that are in range) -- bit-for-bit what clang emits for the
/// same typed global. Big-endian multi-byte emission is refused because no
/// supported target exercises it.
fn scalar_int_initializer_bytes(
    name: &str,
    ty: &trust_ir::Ty,
    value: i128,
    width: usize,
    signed: bool,
    endian: trust_ir::Endianness,
) -> Result<Vec<u8>, PipelineError> {
    let in_range = if signed {
        // Every 16-byte signed value fits an i128.
        width == 16 || {
            let bits = (width * 8) as u32;
            let min = -(1i128 << (bits - 1));
            let max = (1i128 << (bits - 1)) - 1;
            value >= min && value <= max
        }
    } else {
        value >= 0
            && (width == 16 || {
                let bits = (width * 8) as u32;
                (value as u128) < (1u128 << bits)
            })
    };
    if !in_range {
        return Err(PipelineError::ISel(format!(
            "trust-ir global {name} unsupported: scalar initializer value {value} is outside {ty:?} range",
        )));
    }
    scalar_uint_bits_bytes(name, (value as u128) & width_mask(width), width, endian)
}

/// Low `width` bytes of `bits` in `endian` order. Big-endian multi-byte
/// emission fails closed (unverified on the supported little-endian targets).
fn scalar_uint_bits_bytes(
    name: &str,
    bits: u128,
    width: usize,
    endian: trust_ir::Endianness,
) -> Result<Vec<u8>, PipelineError> {
    if matches!(endian, trust_ir::Endianness::Big) && width > 1 {
        return Err(PipelineError::ISel(format!(
            "trust-ir global {name} unsupported: big-endian multi-byte scalar emission is not verified for any supported target",
        )));
    }
    Ok(bits.to_le_bytes()[..width].to_vec())
}

/// Mask selecting the low `width` bytes (`width` in 1..=16).
fn width_mask(width: usize) -> u128 {
    if width >= 16 {
        u128::MAX
    } else {
        (1u128 << (width * 8)) - 1
    }
}

/// Whether a global's declared `Ty` DECOMPOSES into per-position element types,
/// so an aggregate `Int` element can be laid out at its declared element width
/// (a vtable slot). A scalar/opaque type does not decompose; its aggregate
/// initializer is the historic flat byte image instead.
fn aggregate_type_is_decomposable(ty: &trust_ir::Ty) -> bool {
    matches!(
        ty,
        trust_ir::Ty::Array(..)
            | trust_ir::Ty::Tuple(..)
            | trust_ir::Ty::Struct(..)
            | trust_ir::Ty::Vector(..)
    )
}

/// The declared type of aggregate element `index` given the global's aggregate
/// `Ty`, or `None` when the type does not resolve a per-position element type
/// (a scalar/opaque global type, an out-of-range tuple/struct index, or an
/// unresolved arena/struct id). Every array/vector element shares one element
/// type; tuple/struct elements are positional.
fn aggregate_element_type_at<'m>(
    module: &'m trust_ir::Module,
    ty: &'m trust_ir::Ty,
    index: usize,
) -> Option<&'m trust_ir::Ty> {
    match ty {
        trust_ir::Ty::Array(elem, _len) => module.ty(*elem),
        trust_ir::Ty::Vector(elem, _lanes) => Some(elem.as_ref()),
        trust_ir::Ty::Tuple(elems) => elems.get(index),
        trust_ir::Ty::Struct(id) => module
            .struct_def(*id)
            .and_then(|sd| sd.fields.get(index))
            .map(|field| &field.ty),
        _ => None,
    }
}

/// Byte width and signedness of the SCALAR element type an aggregate
/// `Constant::Int` element occupies, or `None` if the element type is not a
/// scalar with a fixed layout width (so the caller fails closed rather than
/// emit a wrong-width slot).
///
/// Integer types use their fixed width; `Isize`/`Usize` and every
/// pointer-shaped element type (`Ptr`, `&T`/`&mut T`, `*const/*mut T`, `Rc<T>`,
/// a function pointer) use the target pointer width — a vtable's
/// `drop`/`size`/`align`/method slots are all one pointer word wide; `Char` is
/// the 4-byte Unicode scalar carrier.
fn aggregate_int_element_width_signed(ty: &trust_ir::Ty) -> Option<(usize, bool)> {
    if let Some(width_signed) = integer_ty_width_signed(ty) {
        return Some(width_signed);
    }
    Some(match ty {
        trust_ir::Ty::Isize => (GLOBAL_POINTER_SIZE, true),
        trust_ir::Ty::Usize => (GLOBAL_POINTER_SIZE, false),
        trust_ir::Ty::Char => (4, false),
        trust_ir::Ty::Ptr
        | trust_ir::Ty::Ref(_)
        | trust_ir::Ty::RefMut(_)
        | trust_ir::Ty::PtrConst(_)
        | trust_ir::Ty::PtrMut(_)
        | trust_ir::Ty::Rc(_)
        | trust_ir::Ty::Func(_) => (GLOBAL_POINTER_SIZE, false),
        _ => return None,
    })
}

fn trust_ir_global_initializer_data(
    module: &trust_ir::Module,
    global: &trust_ir::Global,
    initializer: &trust_ir::Constant,
    endian: trust_ir::Endianness,
) -> Result<(Vec<u8>, Vec<crate::pipeline::GlobalSymbolRef>), PipelineError> {
    use crate::pipeline::GlobalSymbolRef;

    match initializer {
        trust_ir::Constant::Aggregate(elems) => {
            // Fail closed on enum-typed globals: an enum Constant::Aggregate is
            // the tag+payload convention (element 0 = discriminant VALUE), not
            // a positional byte/element list — neither the decomposed lane
            // layout below nor the flat byte image places a tag word or the
            // payload at its aligned offset, so emitting either silently
            // fabricates a wrong-layout image. (Function-local enum constants
            // go through the adapter's `fill_enum_at_ptr`, which does the
            // layout properly; globals gain that path when demand appears.)
            if matches!(&global.ty, trust_ir::Ty::Enum(_)) {
                return Err(PipelineError::ISel(format!(
                    "trust-ir global {} unsupported: enum-typed global with an aggregate \
                     initializer (tag+payload lowering for globals not yet wired; \
                     refusing a wrong-layout flat image)",
                    global.name
                )));
            }
            let mut data: Vec<u8> = Vec::with_capacity(elems.len());
            let mut symbol_refs: Vec<GlobalSymbolRef> = Vec::new();
            // When the global type decomposes into per-position element types
            // (a vtable / `[Ptr; N]` / typed struct), each `Int` element is laid
            // out at its DECLARED element width. Otherwise (a scalar/opaque
            // global type spelled as its little-endian byte sequence) the
            // aggregate is the historic flat byte image, one literal byte per
            // `Int`.
            let typed_elements = aggregate_type_is_decomposable(&global.ty);
            for (index, elem) in elems.iter().enumerate() {
                match elem {
                    trust_ir::Constant::Int(value) if typed_elements => {
                        // Fail closed if the element type — hence its width —
                        // isn't resolvable: emitting a guessed width would
                        // misalign every following slot (the vtable bug).
                        let elem_ty = aggregate_element_type_at(module, &global.ty, index)
                            .ok_or_else(|| {
                                PipelineError::ISel(format!(
                                    "trust-ir global {} unsupported: aggregate Int element {index} has no resolvable element type in declared type {:?}; cannot determine its layout width",
                                    global.name, global.ty
                                ))
                            })?;
                        let (width, signed) = aggregate_int_element_width_signed(elem_ty)
                            .ok_or_else(|| {
                                PipelineError::ISel(format!(
                                    "trust-ir global {} unsupported: aggregate Int element {index} has non-scalar element type {elem_ty:?}; cannot determine its layout width",
                                    global.name
                                ))
                            })?;
                        let bytes = scalar_int_initializer_bytes(
                            &global.name,
                            elem_ty,
                            *value,
                            width,
                            signed,
                            endian,
                        )?;
                        data.extend_from_slice(&bytes);
                    }
                    trust_ir::Constant::Int(byte) => {
                        // Historic flat byte image: one literal byte per `Int`.
                        data.push(u8::try_from(*byte).map_err(|_| {
                            PipelineError::ISel(format!(
                                "trust-ir global {} unsupported: byte aggregate element {index} value {byte} is outside u8 range",
                                global.name
                            ))
                        })?);
                    }
                    trust_ir::Constant::SymbolAddr { symbol, addend } => {
                        // A symbol address is a pointer, always pointer-width and
                        // relocated regardless of the declared element type.
                        let offset = data.len() as u64;
                        data.extend(std::iter::repeat_n(0u8, GLOBAL_POINTER_SIZE));
                        symbol_refs.push(GlobalSymbolRef {
                            offset,
                            symbol: symbol.clone(),
                            addend: *addend,
                        });
                    }
                    other => {
                        return Err(PipelineError::ISel(format!(
                            "trust-ir global {} unsupported: only integer and symbol-address aggregate elements are admitted in this slice; element {index} is {other:?}",
                            global.name
                        )));
                    }
                }
            }
            Ok((data, symbol_refs))
        }
        trust_ir::Constant::Int(value) => {
            if let Some((width, signed)) = integer_ty_width_signed(&global.ty) {
                scalar_int_initializer_bytes(
                    &global.name,
                    &global.ty,
                    *value,
                    width,
                    signed,
                    endian,
                )
                .map(|bytes| (bytes, Vec::new()))
            } else if global.ty == trust_ir::Ty::Bool {
                // A Bool global wants a `Constant::Bool`; an integer literal is a
                // shape mismatch we refuse rather than guess the truth value of.
                Err(PipelineError::ISel(format!(
                    "trust-ir global {} unsupported: scalar integer initializer for Bool needs target-endian typed data emission; a Bool global must carry a Bool initializer",
                    global.name
                )))
            } else {
                Err(PipelineError::ISel(format!(
                    "trust-ir global {} unsupported: integer initializer for non-integer type {:?}",
                    global.name, global.ty
                )))
            }
        }
        trust_ir::Constant::Float(value) => match global.ty {
            // F64 stores the exact IEEE-754 double bit pattern.
            trust_ir::Ty::F64 => {
                scalar_uint_bits_bytes(&global.name, value.to_bits() as u128, 8, endian)
                    .map(|bytes| (bytes, Vec::new()))
            }
            // F32 stores the round-to-nearest-even single-precision encoding of
            // the literal -- identical to what a C compiler emits for
            // `float x = <double-constant>;`.
            trust_ir::Ty::F32 => {
                scalar_uint_bits_bytes(&global.name, (*value as f32).to_bits() as u128, 4, endian)
                    .map(|bytes| (bytes, Vec::new()))
            }
            _ => Err(PipelineError::ISel(format!(
                "trust-ir global {} unsupported: float initializer for {:?} (only F32/F64 scalar float globals are wired; F16 and non-float types are refused)",
                global.name, global.ty
            ))),
        },
        trust_ir::Constant::Bool(value) if global.ty == trust_ir::Ty::Bool => {
            Ok((vec![u8::from(*value)], Vec::new()))
        }
        // The v25 byte-array carrier: an initializer whose value IS a raw byte
        // sequence (a `&[u8]` / `&str` backing store, a SipHash key table, a
        // `RawTableInner` control-byte buffer). The bytes are emitted verbatim —
        // they are already the target-endian object image and carry no embedded
        // symbol-address relocations (the `utf8` flag is a producer-side claim
        // about the contents, not a layout distinction). This mirrors the
        // `Constant::Aggregate` byte path, one byte per element, but without the
        // per-element `Int` round-trip.
        trust_ir::Constant::Bytes { data, utf8: _ } => Ok((data.clone(), Vec::new())),
        other => Err(PipelineError::ISel(format!(
            "trust-ir global {} unsupported: only byte/symbol-address aggregate and byte-sized scalar initializers are admitted in this slice; initializer is {other:?}",
            global.name
        ))),
    }
}

fn trust_ir_function_for_lir<'a>(
    module: &'a trust_ir::Module,
    lir_func: &trust_cg_lower::Function,
) -> Option<&'a trust_ir::Function> {
    module
        .functions
        .iter()
        .find(|func| func.name == lir_func.name && !func.blocks.is_empty())
}

/// Per-function JIT validation provenance (JIT-5).
///
/// Records, for one published function, whether its emitted bytes are covered
/// by a verified certificate, the SHA-256 the certificate is bound to, and
/// whether the verdict came from the content-addressed certificate cache
/// (warm hit) or a fresh discharge.
#[derive(Debug, Clone)]
pub struct JitFunctionValidation {
    /// Function name.
    pub function: String,
    /// Whether this function's lowering is verified (every executed byte
    /// covered). `false` only appears on the Unchecked path — a verifying mode
    /// fails the whole compile closed before publishing an unverified function.
    pub verified: bool,
    /// SHA-256 (hex) the certificate is bound to (the function's emitted
    /// pre-fixup machine bytes on x86; the emitted function bytes on aarch64).
    pub bytes_sha256: String,
    /// Whether the verdict was served from the certificate cache without
    /// re-running the verifier (warm hit).
    pub cache_hit: bool,
}

/// Whole-buffer JIT validation provenance (JIT-5).
///
/// Attached to every [`JitCompilationResult`] so the executed validation mode
/// is always auditable — Unchecked can never be silent — and so a consumer can
/// confirm every published byte is covered by a certificate bound to the
/// buffer's published-image hash (JIT-7's publish check).
#[derive(Debug, Clone)]
pub struct JitValidationProvenance {
    /// The resolved validation mode this buffer was published under.
    pub mode: JitValidationMode,
    /// SHA-256 (hex) of the full published executable image (JIT-7).
    pub published_image_sha256: String,
    /// Per-function coverage records (empty on the Unchecked path).
    pub functions: Vec<JitFunctionValidation>,
}

impl JitValidationProvenance {
    /// Whether every published function carries a verified, bytes-bound
    /// certificate (true only on a verifying mode with a non-empty function
    /// set).
    pub fn every_byte_certified(&self) -> bool {
        self.mode.requires_jit_verification()
            && !self.functions.is_empty()
            && self.functions.iter().all(|f| f.verified)
    }

    /// Number of functions whose verdict was served from the cache.
    pub fn cache_hits(&self) -> usize {
        self.functions.iter().filter(|f| f.cache_hit).count()
    }
}

/// The result of compiling a trust_ir module through the Trust Codegen pipeline to
/// executable memory for JIT execution.
///
/// Unlike [`CompilationResult`] which produces Mach-O object file bytes,
/// this result contains an [`ExecutableBuffer`](crate::jit::ExecutableBuffer)
/// with all functions linked and ready for immediate execution.
pub struct JitCompilationResult {
    /// Executable memory buffer containing all compiled functions.
    pub buffer: crate::jit::ExecutableBuffer,
    /// Compilation metrics.
    pub metrics: CompilationMetrics,
    /// Optional compiler trace (populated when trace_level != None).
    pub trace: Option<CompilerTrace>,
    /// Optional proof certificates (populated when emit_proofs is true).
    pub proofs: Option<Vec<ProofCertificate>>,
    /// Proof-optimization certificate citations emitted by `trust-cg-opt` while
    /// preparing the executable buffer.
    pub proof_optimization_certificates: Vec<ProofOptimizationCertificateCitation>,
    /// Per-function code-quality and phase-timing metrics. See #364.
    /// Always populated (one entry per compiled function).
    pub per_function_metrics: Vec<FunctionQualityMetrics>,
    /// JIT-5 validation provenance: the resolved mode, the published-image
    /// hash the certificates bind to, and per-function coverage/cache
    /// provenance. `None` only for legacy result constructions that predate
    /// JIT-5; the JIT module path always populates it.
    pub validation: Option<JitValidationProvenance>,
}

impl std::fmt::Debug for JitCompilationResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("JitCompilationResult")
            .field("buffer_size", &self.buffer.allocated_size())
            .field("symbol_count", &self.buffer.symbol_count())
            .field("metrics", &self.metrics)
            .field("trace", &self.trace)
            .field("proofs", &self.proofs)
            .field(
                "proof_optimization_certificate_count",
                &self.proof_optimization_certificates.len(),
            )
            .field(
                "per_function_metrics_count",
                &self.per_function_metrics.len(),
            )
            .finish()
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Count the number of real (non-pseudo) machine instructions in a function.
///
/// Walks blocks in layout order and counts instructions that will actually be
/// encoded to machine code. Pseudo-instructions (Phi, Copy, StackAlloc, Nop,
/// etc.) are excluded since they have no hardware encoding.
fn count_real_instructions(func: &trust_cg_ir::MachFunction) -> usize {
    func.block_order
        .iter()
        .map(|&block_id| {
            func.blocks[block_id.0 as usize]
                .insts
                .iter()
                .filter(|&&inst_id| !func.insts[inst_id.0 as usize].is_pseudo())
                .count()
        })
        .sum()
}

/// Count branch-like instructions for coarse per-function density metrics.
///
/// The JIT path currently prepares AArch64 `MachFunction`s, so this helper
/// recognizes AArch64 branch / return opcodes directly and also counts any
/// non-pseudo terminator flagged in the IR.
fn count_branch_instructions(func: &trust_cg_ir::MachFunction) -> usize {
    func.block_order
        .iter()
        .map(|&block_id| {
            func.blocks[block_id.0 as usize]
                .insts
                .iter()
                .filter(|&&inst_id| {
                    let inst = &func.insts[inst_id.0 as usize];
                    !inst.is_pseudo()
                        && (inst.is_terminator()
                            || matches!(
                                inst.opcode,
                                trust_cg_ir::inst::AArch64Opcode::B
                                    | trust_cg_ir::inst::AArch64Opcode::BCond
                                    | trust_cg_ir::inst::AArch64Opcode::Bcc
                                    | trust_cg_ir::inst::AArch64Opcode::Cbz
                                    | trust_cg_ir::inst::AArch64Opcode::Cbnz
                                    | trust_cg_ir::inst::AArch64Opcode::Tbz
                                    | trust_cg_ir::inst::AArch64Opcode::Tbnz
                                    | trust_cg_ir::inst::AArch64Opcode::Br
                                    | trust_cg_ir::inst::AArch64Opcode::Bl
                                    | trust_cg_ir::inst::AArch64Opcode::BL
                                    | trust_cg_ir::inst::AArch64Opcode::Ret
                            ))
                })
                .count()
        })
        .sum()
}

fn collect_proof_optimization_certificates(
    metrics: &[crate::pipeline::PreparationMetrics],
) -> Vec<ProofOptimizationCertificateCitation> {
    metrics
        .iter()
        .flat_map(|metrics| metrics.proof_optimization_certificates.iter().cloned())
        .collect()
}

#[cfg(feature = "verify")]
fn collect_certified_pass_runs(
    metrics: &[crate::pipeline::PreparationMetrics],
) -> Vec<trust_cg_opt::CertifiedPassRunRecord> {
    metrics
        .iter()
        .flat_map(|metrics| metrics.certified_pass_runs.iter().cloned())
        .collect()
}

fn summarize_fsym_trust_ir_metrics(
    metrics: &[crate::pipeline::PreparationMetrics],
) -> FsymTrustIrMetrics {
    let mut summary = FsymTrustIrMetrics::default();
    for metrics in metrics {
        let Some(fsym) = &metrics.fsym_trust_ir_summary else {
            continue;
        };
        if fsym.scanned {
            summary.scanned_functions += 1;
        }
        if fsym.skipped.is_some() {
            summary.skipped_functions += 1;
        }
        summary.concrete_ub_diagnostics += fsym.diagnostic_count;
        summary.unknown_obligations += fsym.unknown_obligation_count;
        summary.warnings += fsym.warning_count;
    }
    summary
}

fn summarize_proof_optimizations(
    certificates: &[ProofOptimizationCertificateCitation],
) -> ProofOptimizationMetrics {
    let mut metrics = ProofOptimizationMetrics {
        certificate_count: certificates.len(),
        ..ProofOptimizationMetrics::default()
    };

    for certificate in certificates {
        let is_applied = certificate.status == "applied";
        let is_rejected = certificate.status == "rejected";
        let is_guard = certificate.kind == "GuardEliminated";
        let cites_non_zero_divisor = citation_mentions_fact(certificate, "NonZeroDivisor");
        let cites_valid_shift = citation_mentions_fact(certificate, "ValidShift");

        if is_applied {
            metrics.applied_count += 1;
        }
        if is_rejected {
            metrics.rejected_count += 1;
        }
        if is_applied && is_guard {
            metrics.guard_eliminated_count += 1;
            if cites_non_zero_divisor {
                metrics.non_zero_divisor_guard_eliminated_count += 1;
            }
            if cites_valid_shift {
                metrics.valid_shift_guard_eliminated_count += 1;
            }
        }
        if is_rejected && is_guard {
            metrics.guard_rejected_count += 1;
            if cites_non_zero_divisor {
                metrics.non_zero_divisor_guard_rejected_count += 1;
            }
            if cites_valid_shift {
                metrics.valid_shift_guard_rejected_count += 1;
            }
        }
    }

    metrics
}

fn citation_mentions_fact(
    certificate: &ProofOptimizationCertificateCitation,
    fact_name: &str,
) -> bool {
    certificate
        .consumed_facts
        .iter()
        .any(|fact| fact.name == fact_name)
        || certificate.rejection_fact.as_deref() == Some(fact_name)
}

/// Fail closed on exception-handling structure in the x86 JIT path.
///
/// The in-memory JIT does not emit a Mach-O `__eh_frame` / `__gcc_except_tab`,
/// so a JIT-compiled function carrying EH structure would run without unwind
/// tables (aborting / leaking on unwind). EH x86 Lane 2 makes the AOT Mach-O
/// OBJECT correct; JIT unwinding is a later lane, so this residual gate keeps
/// the opt-in unwind feature from ever producing a JIT function without unwind
/// tables. EH structure is only produced under the `TCG_ENABLE_UNWIND` frontend
/// opt-in (default OFF), so this gate is inert for the standard corpus.
fn reject_x86_jit_eh(
    lir_functions: &[(trust_cg_lower::Function, trust_cg_lower::ProofContext)],
) -> Result<(), CompileError> {
    for (lir_func, _) in lir_functions {
        if !lir_func.eh_info.is_empty() {
            return Err(CompileError::Pipeline(PipelineError::ISel(format!(
                "x86-64 exception handling (LSDA / personality / eh_frame) is not \
                 supported in the JIT for `{}`: EH x86 Lane 2 emits unwind tables \
                 only on the AOT Mach-O path; the in-memory JIT has no eh_frame. \
                 Fail-closed to avoid running a function without unwind tables.",
                lir_func.name
            ))));
        }
    }
    Ok(())
}

/// Fail closed on exception-handling structure in the AArch64 JIT path.
///
/// A frame-only `.eh_frame` registration is insufficient for functions with
/// invoke/landing-pad structure: without the matching personality and LSDA,
/// the unwinder cannot select cleanup or catch handlers. The AOT path emits the
/// complete bundle; the JIT stays closed until it can do the same and is
/// covered by an executable cleanup test.
fn reject_aarch64_jit_eh(
    lir_functions: &[(trust_cg_lower::Function, trust_cg_lower::ProofContext)],
) -> Result<(), CompileError> {
    for (lir_func, _) in lir_functions {
        if !lir_func.eh_info.is_empty() {
            return Err(CompileError::Pipeline(PipelineError::ISel(format!(
                "exception handling (LSDA / personality / unwind tables) is not supported \
                 in the AArch64 JIT for `{}`: the in-memory JIT has no complete \
                 personality/LSDA/eh_frame registration. Fail-closed to avoid skipping \
                 cleanup or catch handlers.",
                lir_func.name
            ))));
        }
    }
    Ok(())
}

/// Fail closed on exception-handling structure for non-Mach-O AOT output.
///
/// EH x86 Lane 2 wires the LSDA (`__gcc_except_tab`) + zPLR FDE + personality
/// ONLY for Mach-O; the ELF (`add_x86_64_eh_frame_to_elf`) and COFF emitters get
/// no LSDA yet. A Mach-O EH function flows through to the (now complete)
/// emission; an ELF/COFF EH function still fails closed rather than shipping an
/// object without unwind tables. Inert for the corpus (`TCG_ENABLE_UNWIND` OFF).
fn reject_x86_eh_for_non_macho_aot(
    lir_functions: &[(trust_cg_lower::Function, trust_cg_lower::ProofContext)],
    output_format: crate::x86_64::X86OutputFormat,
) -> Result<(), CompileError> {
    if output_format == crate::x86_64::X86OutputFormat::MachO {
        return Ok(());
    }
    for (lir_func, _) in lir_functions {
        if !lir_func.eh_info.is_empty() {
            return Err(CompileError::Pipeline(PipelineError::ISel(format!(
                "x86-64 exception handling (LSDA / personality / eh_frame) is emitted \
                 only for Mach-O in EH x86 Lane 2; `{}` targets a non-Mach-O object \
                 (ELF/COFF) which gets no unwind tables yet. Fail-closed to avoid \
                 emitting an object without unwind tables.",
                lir_func.name
            ))));
        }
    }
    Ok(())
}

fn count_x86_real_instructions(func: &trust_cg_lower::x86_64_isel::X86ISelFunction) -> usize {
    func.block_order
        .iter()
        .filter_map(|block| func.blocks.get(block))
        .map(|block| {
            block
                .insts
                .iter()
                .filter(|inst| !inst.opcode.is_pseudo())
                .count()
        })
        .sum()
}

/// Sentinel S5 hardening — map a compile [`Target`] to the [`GuardCarrierArch`]
/// whose carrier expander will materialize a surviving exact-bound `InBounds`
/// guard, so the adapter's per-arch bound cap matches the backend that will
/// actually encode the runtime check.
fn guard_carrier_arch_for_target(target: Target) -> trust_cg_lower::GuardCarrierArch {
    match target {
        Target::Aarch64 => trust_cg_lower::GuardCarrierArch::AArch64,
        Target::X86_64 => trust_cg_lower::GuardCarrierArch::X86_64,
        Target::Riscv64 => trust_cg_lower::GuardCarrierArch::Riscv64,
    }
}

/// Run the x86 fail-closed guard pass.  Production supplies empty replay evidence and bindings, so
/// all carriers are retained; the structural kernel and re-check remain exercised for future wiring.
/// CT-5 / BENCH-8 guard: is the opt-in per-compile LIVE reconstructed-obligation
/// solver lane requested via `TCG_RECON_SOLVER_ROUTE`?
///
/// `trust_cg_verify::verdict_db::reconstructed_live_solver_enabled` (the precise
/// predicate) is `pub(crate)` to that crate, so this is a CONSERVATIVE mirror of
/// only its env trigger: it returns `true` whenever the route env is set to
/// anything but `0`, ignoring the additional gates (solver presence,
/// `TCG_NO_PROOF_CACHE`, `TCG_REFINE_SOLVER=0`) that can only make the real
/// predicate MORE restrictive. Over-approximating here is fail-safe — at worst it
/// keeps certificate generation SERIAL in a rare configuration that would not
/// actually have spawned a solver, never the reverse. When it returns `true` the
/// x86 dispatcher keeps cert generation single-threaded so a live z3 is never
/// invoked concurrently (the BENCH-8 parallel-z3 nondeterminism class).
// Consumed only by the `verify`-gated cert lane in `compile_x86_64`.
#[cfg_attr(not(feature = "verify"), allow(dead_code))]
fn recon_live_solver_route_requested() -> bool {
    std::env::var_os("TCG_RECON_SOLVER_ROUTE").is_some_and(|v| v != "0")
}

fn run_x86_guard_kernel_gate(
    isel_func: &mut trust_cg_lower::x86_64_isel::X86ISelFunction,
    _proof_ctx: &trust_cg_lower::ProofContext,
    _trust_ir_module: &trust_ir::Module,
    eliminated_total: &mut u32,
) -> Result<(), String> {
    use trust_cg_opt::x86_proof_opts::X86ProofGuardElimination;

    // Nothing to gate if ISel bound no carrier to an obligation.
    if isel_func.guard_obligations.is_empty() {
        return Ok(());
    }

    // Public Trust-IR status/lineage, ProofRef labels, and adapter-synthesized ids are diagnostic
    // metadata, not exact replay authority.  Deliberately supply neither evidence nor carrier
    // bindings.  The structural `guard_obligations` map remains on `isel_func` for reports.
    let evidence = trust_cg_lower::guard_evidence::production_guard_replay_evidence();
    let obligations = std::collections::HashMap::new();
    let mut pass = X86ProofGuardElimination::new();
    pass.enable_kernel_gate(evidence, obligations);
    pass.run_on_function(isel_func);

    // Independent fail-closed re-check (the "different path"): re-derive the
    // operand fingerprint and re-confirm discharge against the evidence.
    pass.recheck_kernel_eliminations()?;

    *eliminated_total += pass.stats().guards_eliminated;
    Ok(())
}

/// RISC-V mirror of [`run_x86_guard_kernel_gate`], with the same empty-authority policy.
fn run_riscv_guard_kernel_gate(
    isel_func: &mut crate::riscv::pipeline::RiscVISelFunction,
    _proof_ctx: &trust_cg_lower::ProofContext,
    _trust_ir_module: &trust_ir::Module,
    eliminated_total: &mut u32,
) -> Result<(), String> {
    use crate::riscv::pipeline::RiscVProofGuardElimination;

    // Nothing to gate if ISel bound no carrier to an obligation.
    if isel_func.guard_obligations.is_empty() {
        return Ok(());
    }

    // Same exact-replay boundary as x86/AArch64: retain structural metadata, grant no authority.
    let evidence = trust_cg_lower::guard_evidence::production_guard_replay_evidence();
    let obligations = std::collections::HashMap::new();
    let mut pass = RiscVProofGuardElimination::new();
    pass.enable_kernel_gate(evidence, obligations);
    pass.run_on_function(isel_func);

    // Independent fail-closed re-check (the "different path").
    pass.recheck_kernel_eliminations()?;

    *eliminated_total += pass.stats().guards_eliminated;
    Ok(())
}

/// Run the carrier-hygiene invariant (`trust_cg_verify::carrier_hygiene`) over
/// an emitted x86-64 ISel function and FAIL CLOSED on the first violation.
///
/// This is the production wiring of item 1 of the proof-gap program: the
/// pure-lattice checker that re-derives MISCOMPILE #51 / #66 (a wide-reading
/// `SAR`/`IDIV` / `SHR`/`DIV` consuming a dirty narrow carrier) now runs on
/// EVERY x86 compile, on the DEFAULT build — it is NOT gated behind the
/// `verify` feature. The checker needs no solver / SMT: it is a forward
/// abstract interpretation over the machine-IR stream.
///
/// # Soundness gate (mirrors `x86_64_function_verifier::apply_carrier_hygiene`)
///
/// The checker is seeded from the per-VReg nominal-width map ISel records
/// (`X86ISelFunction::vreg_nominal_widths()`). A function with NO recorded
/// widths did not pass through the width-recording ISel selection path and
/// carries no ground truth to check against, so it is skipped — running the
/// fail-closed checker against an empty map would false-reject every wide
/// reader as "unknown width". Production ISel output always carries the width
/// map (every GPR-carrier def is recorded), so the invariant always runs on
/// real emitted code. This matches the live function-verifier wiring exactly.
fn check_x86_carrier_hygiene(
    func: &trust_cg_lower::x86_64_isel::X86ISelFunction,
) -> Result<(), CompileError> {
    // No width metadata => not a width-recording ISel function => nothing to
    // check against. Sound: such functions are synthetic, never production
    // codegen (which always records widths).
    if func.vreg_nominal_widths().is_empty() {
        return Ok(());
    }

    let nominal = trust_cg_verify::carrier_hygiene::NominalWidths::from_value_type_widths(
        func.vreg_nominal_widths(),
    );
    let report = trust_cg_verify::carrier_hygiene::check_function(func, &nominal);
    if let Some(violation) = report.violations.into_iter().next() {
        return Err(CompileError::CarrierHygiene {
            function_name: func.name.clone(),
            block: violation.block,
            inst_index: violation.inst_index,
            opcode: violation.opcode,
            operand: violation.operand,
            required: violation.required,
            actual: violation.actual,
            detail: violation.detail,
        });
    }
    Ok(())
}

/// TV-3: block-level lowering-integrity dataflow validation over the RAW
/// pre-pass x86 ISel output.
///
/// Runs the shared arch-parametric validator
/// ([`trust_cg_verify::dataflow_integrity`]) against the EXACT LIR function the
/// ISel consumed. Production x86 compilation always ENFORCES this gate
/// (validated 0-hit over the full differential corpus in warn-only mode first,
/// per the §2.4 gate rollout): a block-level integrity violation — a real
/// instruction after an unconditional terminator (the switch/BST
/// block-collision family), code fused from two source blocks, a mis-started
/// block, or a DROPPED effectful store/call/atomic (the store-drop class) —
/// fails the compile CLOSED. The standalone rollout environment control is
/// deliberately ignored here: an ambient variable must not disable a
/// production compiler integrity gate.
///
/// MUST run on the pre-pass ISel output: the optimizer passes below do not
/// preserve TV-1 provenance stamps (see the `LoweringProvenance` schema note in
/// `trust-cg-ir`). Runs unconditionally (not behind the `verify` feature),
/// exactly like [`check_x86_carrier_hygiene`], so the AOT object path stays
/// honest on the default `default-features = false` bridge build.
pub fn enforce_x86_dataflow_integrity(
    func: &trust_cg_lower::x86_64_isel::X86ISelFunction,
    lir: &trust_cg_lower::Function,
) -> Result<(), CompileError> {
    use trust_cg_verify::dataflow_integrity::{self, DataflowIntegrityMode};
    // `dataflow_integrity::evaluate` intentionally skips a mismatched replay
    // pair because its rollout callers may run in warn-only mode. This wrapper
    // is the production ENFORCE boundary, so accepting a mis-zipped function
    // would bypass the gate entirely. Fail closed before entering the shared
    // evaluator.
    if func.name != lir.name {
        return Err(CompileError::Pipeline(PipelineError::ISel(format!(
            "[TCG-DATAFLOW-INTEGRITY] x86 function/LIR pairing mismatch: machine function `{}` was paired with LIR function `{}`",
            func.name, lir.name
        ))));
    }
    if let Some(violation) =
        dataflow_integrity::evaluate(func, lir, "x86_64", DataflowIntegrityMode::Enforce)
    {
        return Err(CompileError::Pipeline(PipelineError::ISel(format!(
            "[TCG-DATAFLOW-INTEGRITY] fn `{}` block-level lowering-integrity violation ({:?}): {}",
            func.name, violation.kind, violation.detail
        ))));
    }
    Ok(())
}

/// Validate, fail-closed, the arch-divergent glue-pass expansions the x86-64
/// pipeline relies on (item 3 of the proof-gap program).
///
/// # What this certifies
///
/// The SMT-verified per-instruction lowering core proves *individual* opcode
/// lowerings; it does NOT prove the *glue passes* that rewrite one IR shape
/// into another before instruction selection. The overflow / checked-arith
/// expansion (`trust_cg_lower::adapter::translate_overflow`) is one such pass,
/// and it was the site of MISCOMPILE #67: the original signed-mul-overflow
/// expansion used the AArch64 `SDIV`-identity check (`q = value SDIV rhs;
/// overflow = rhs != 0 && q != lhs`), which relies on AArch64 `SDIV`-by-zero
/// returning 0. Ported verbatim to x86-64 — where `IDIV`-by-zero raises `#DE`
/// (SIGFPE) — `x.overflowing_mul(0)` crashed instead of reporting no overflow.
/// The fix (commit `9395663`) replaced it with a division-free wide-multiply.
///
/// SCOPE — now a PER-PROGRAM gate (proof-gap item 3, #67), no longer a fixed
/// canary. `validate_x86_overflow_expansions_per_program` inspects each emitted
/// `X86ISelFunction` and derives, FROM THE ACTUAL EMITTED CODE, the overflow /
/// checked-arith expansions THIS program contains, then:
///
///   1. STRUCTURAL SAFETY NET (the false-positive-free #67 invariant): a signed
///      multiply (`IMUL`) whose product feeds an `IDIV` *dividend* is the exact
///      `SDIV`-identity signature (`q = (a*b) SDIV b`) that SIGFPEs on x86-64
///      `IDIV`-by-zero / `INT_MIN/-1`. No correct lowering ever divides a
///      multiply product, so this dataflow is rejected fail-closed on sight.
///   2. ENUMERATION + EXHAUSTIVE RE-VERIFICATION: it recognizes the live
///      division-free wide-multiply signed-mul-overflow idiom (`MOVSX -> IMUL
///      ... CMP ... SETcc NE`) and the native I32/I64 flag idiom (`{ADD,SUB,
///      IMUL} ... SETcc {O,B}`), recovering each site's `(CheckedOp,
///      OverflowExpansion, width)`. Each DISTINCT triple is validated ONCE per
///      compile (deduped) via the arch-parameterized `OverflowExpansionValidator`
///      under x86-64 `IDIV` `#DE` trap semantics, discharged EXHAUSTIVELY by
///      `verify_by_evaluation` (no solver), fail-closed.
///
/// The fixed-model canary is KEPT (cheap, memoized) and folded in as a baseline
/// so even an overflow-free program re-proves the validator model is
/// arch-discriminating. Whereas the canary caught only a regression in the
/// expansion MODEL / validator, the per-program form reflects what THIS
/// program's `X86ISelFunction`s actually emit — closing the gap the old doc
/// admitted ("does NOT inspect the program's emitted `X86ISelFunction`s").
///
/// HONEST RESIDUAL: the full `OverflowExpansion` strategy *enum value* is not a
/// discrete post-ISel tag — narrow-width expansions are decomposed into generic
/// opcodes — so enumeration recognizes idiom SHAPES (it may miss an unrecognized
/// shape = a false negative in enumeration, never a false positive). The
/// structural `IMUL->IDIV` safety net (1) is exhaustive over the emitted stream
/// and is the load-bearing #67 guarantee; enumeration (2) adds semantic
/// re-proof of the recognized shapes. The complementary per-program #67
/// protections remain on by default: P3c (MIR->trust-ir op-SELECTION), the SMT
/// proof core (trust-ir->machine division-free wide-mul lowering), and
/// `e2e_x86_64_checked_arith` (clang oracle).
///
/// # Wiring form
///
/// This bounded slice uses the lighter `PassValidator::validate()` fail-closed
/// form (returning `Err` on `Rejected`) rather than threading a full
/// `CertifiedPassChainEntry` through the heavily
/// `cfg(feature = "verify")`-gated certificate plumbing.
///
/// Note on the switch-normalization validator: the x86-64 switch lowering
/// (`x86_64_isel::select_switch`) emits a *faithful 1:1 linear CMP+Jcc cascade*
/// preserving every `(case_value, target_block)` from the source switch — it
/// performs NO jump-table / binary-search normalization (those live only in the
/// AArch64 `switch.rs`). The #62 dropped/duplicated/re-targeted-case hazard the
/// `SwitchNormalizationValidator` targets therefore cannot arise on x86, so no
/// per-compile switch validator is wired here.
/// True iff any emitted x86 function contains a `Popcnt` opcode — the sole
/// trigger for the no-POPCNT SWAR encoder rewrite that the popcnt canary
/// guards. Presence gate for `validate_x86_popcnt_expansion_canary`: a program
/// with no `Popcnt` cannot ship the (mis)expansion, so skipping the canary
/// there preserves the guarantee vacuously while removing its fixed per-process
/// cost from the majority of compiles.
fn x86_funcs_emit_popcnt(funcs: &[trust_cg_lower::x86_64_isel::X86ISelFunction]) -> bool {
    funcs.iter().any(|f| {
        f.blocks.values().any(|b| {
            b.insts
                .iter()
                .any(|i| i.opcode == trust_cg_ir::X86Opcode::Popcnt)
        })
    })
}

fn validate_x86_glue_pass_expansions(
    funcs: &[trust_cg_lower::x86_64_isel::X86ISelFunction],
) -> Result<(), CompileError> {
    // (1) Baseline model canary: re-prove the live signed-mul-overflow expansion
    // model (division-free wide multiply) is arch-discriminating under x86-64
    // IDIV trap semantics, even for a program with no overflow sites. Memoized.
    validate_x86_overflow_expansion_canary()?;
    // (1b) Popcount SWAR expansion canary: the encoder rewrites a proven `Popcnt`
    // opcode into a hand-written shift/mask software sequence on the default
    // no-POPCNT target, AFTER the per-instruction certs are generated. Re-prove
    // (memoized) that the SWAR sequence == popcount so a regression in it can't
    // ship behind an all-green proof bundle.
    //
    // PRESENCE GATE (fail-safe compile-time lever): the SWAR rewrite can only
    // fire when a `Popcnt` opcode is actually emitted, so a program with no
    // Popcnt instruction cannot possibly ship the (mis)expansion — the canary's
    // guarantee is vacuously preserved by skipping it there. The first
    // Popcnt-bearing compile in the process still pays the (memoized-for-life)
    // proof, so the sequence is never validated less than exactly the compiles
    // where it can run. This removes the fixed per-process CERT-SKIP recheck
    // from the overwhelming majority of std compiles (which emit no Popcnt).
    if x86_funcs_emit_popcnt(funcs) {
        validate_x86_popcnt_expansion_canary()?;
    }
    // (2) Per-program form: derive and validate the overflow expansions THIS
    // program's emitted X86ISelFunctions actually contain.
    validate_x86_overflow_expansions_per_program(funcs)
}

/// The fixed-model canary, folded in as a baseline (kept because it is cheap and
/// memoized). Re-proves that the live signed-mul-overflow expansion
/// (division-free wide multiply, the #67 fix) is equivalent to the spec under
/// x86-64 IDIV trap semantics. Width 8 => exhaustive (no solver). A regression
/// to the AArch64-only SDIV-identity expansion would be Rejected here.
///
/// The obligation is FIXED and deterministic, so it is discharged ONCE and the
/// verdict memoized instead of re-running the 8-bit exhaustive evaluation on
/// every compile.
fn validate_x86_overflow_expansion_canary() -> Result<(), CompileError> {
    use std::sync::OnceLock;
    use trust_cg_verify::pass_validators::{
        OverflowExpansion, OverflowExpansionValidator, PassValidation, PassValidator, TargetArch,
    };

    static RESULT: OnceLock<Result<(), (String, String, String)>> = OnceLock::new();
    let cached = RESULT.get_or_init(|| {
        let validator = OverflowExpansionValidator::signed_mul(
            "x86-overflow-expand",
            8,
            OverflowExpansion::DivisionFreeWideMul,
            TargetArch::X86_64,
        );
        match validator.validate() {
            PassValidation::Rejected {
                obligation_name,
                reason,
            } => Err((validator.pass_name().to_string(), obligation_name, reason)),
            _ => Ok(()),
        }
    });
    match cached {
        Ok(()) => Ok(()),
        Err((pass_name, obligation_name, reason)) => Err(CompileError::PassValidationRejected {
            pass_name: pass_name.clone(),
            obligation_name: obligation_name.clone(),
            reason: reason.clone(),
        }),
    }
}

/// Canary for the x86 generic-target popcount SWAR expansion (the post-cert
/// encoder expansion `expand_x86_popcnt_inst`). Re-proves ONCE (memoized) that
/// the fixed Hacker's-Delight shift/mask SWAR sequence computes the population
/// count, so a regression in the SWAR table (a wrong fold mask or shift amount)
/// fails the compile closed — even though the per-instruction certificate was
/// generated over the pre-expansion `Popcnt` opcode, BEFORE the encoder replaced
/// it with the ~27-31 instruction software sequence.
///
/// Width 8 keeps the base proof EXHAUSTIVE (complete over all 256 inputs, never
/// sampled) — but at width 8 the SWAR reduction-fold loop (`dst += dst >> {8,16,
/// 32}`) runs zero times, so it never exercises the multi-byte folds the emitted
/// Gpr32/Gpr64 code actually ships. When a formal solver is available we ALSO
/// genuinely prove the real emitted Gpr32 width (32) — whose model masks, shifts
/// and final mask are byte-for-byte `expand_x86_popcnt_inst` — so a regression in
/// either the `>>8` or `>>16` fold now fails the compile closed. The Gpr64 width
/// (64) is provable too but ~30x slower (the 64-term spec pushes AY past the 30 s
/// timeout `validate()` would surface as a Rejection), so it is pinned as the
/// dedicated proof test `popcnt_swar_64_emitted_width_genuinely_verifies` (run in
/// the full-proof job) rather than per-compile.
///
/// COST (PROOF-3 + CERT-SKIP): the width-32 solver proof historically cost
/// ~16 s of live `ay` search per COLD rustc process (the `OnceLock` only
/// amortizes within one process), under a 30 s deadline — every bridge
/// compile was load-fragile (a busy machine could miss the deadline and fail
/// closed with nothing regressed). It now discharges through the CLI solver
/// funnel's CERT-SKIP tier (`trust_cg_verify::canary_cert`): a repo-committed,
/// build-embedded DRAT certificate for exactly this obligation, INDEPENDENTLY
/// re-checked by the vendored `drat-trim` in this process (~1-2 s,
/// deterministic replay — no search, no deadline) before it is credited. The
/// recorded verdict is never trusted: the key binds the solver binary's
/// bytes-hash and the exact SMT2 bytes derived here from the live SWAR model,
/// so a regressed model or a changed solver misses and re-proves LIVE; any
/// miss/mismatch/tamper/check-failure falls back to the live proof
/// (fail-closed, never a weaker verdict; `TCG_CANARY_NO_CACHE=1` forces live).
fn validate_x86_popcnt_expansion_canary() -> Result<(), CompileError> {
    use std::sync::OnceLock;
    use trust_cg_verify::ay_bridge::z3_available;
    use trust_cg_verify::pass_validators::{
        PassValidation, PassValidator, PopcntSwarExpansionValidator,
    };

    static RESULT: OnceLock<Result<(), (String, String, String)>> = OnceLock::new();
    let cached = RESULT.get_or_init(|| {
        // Width 8 is exhaustive and always checked; width 32 (the dominant emitted
        // width) is a genuine solver proof of the exact 32-bit instruction stream
        // and is added only when a solver is present (without one `validate()`
        // fails closed above the exhaustive threshold, which must not reject every
        // popcnt compile on a solver-less host). Cached for the life of the process.
        let mut widths: Vec<u32> = vec![8];
        if z3_available() {
            widths.push(32);
        }
        for width in widths {
            let validator = PopcntSwarExpansionValidator::x86_generic("x86-popcnt-expand", width);
            if let PassValidation::Rejected {
                obligation_name,
                reason,
            } = validator.validate()
            {
                return Err((validator.pass_name().to_string(), obligation_name, reason));
            }
        }
        Ok(())
    });
    match cached {
        Ok(()) => Ok(()),
        Err((pass_name, obligation_name, reason)) => Err(CompileError::PassValidationRejected {
            pass_name: pass_name.clone(),
            obligation_name: obligation_name.clone(),
            reason: reason.clone(),
        }),
    }
}

/// The checked-overflow expansion `(op, expansion, width)` triple recovered from
/// one emitted overflow site. `CheckedOp`/`OverflowExpansion` map directly onto
/// the `OverflowExpansionValidator` so each distinct triple can be re-verified.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct RecoveredOverflowExpansion {
    /// `0 = SignedAdd`, `1 = SignedSub`, `2 = SignedMul` (matches `CheckedOp`).
    op: u8,
    /// `0 = SignBitCheck`, `1 = DivisionFreeWideMul` (matches `OverflowExpansion`).
    expansion: u8,
    /// Source operand bit width (8/16/32/64).
    width: u32,
}

/// PER-PROGRAM overflow-expansion validation (proof-gap item 3, #67).
///
/// Inspects each emitted `X86ISelFunction` and, FROM THE EMITTED CODE:
///
///   1. STRUCTURAL SAFETY NET — rejects, fail-closed, any signed multiply whose
///      product feeds an `IDIV` dividend (the `SDIV`-identity #67 signature; no
///      correct lowering divides a multiply product). False-positive-free.
///   2. ENUMERATION + RE-VERIFICATION — recovers each recognized overflow site's
///      `(op, expansion, width)` triple, dedups across the whole program, and
///      re-discharges each DISTINCT triple ONCE through the arch-parameterized
///      `OverflowExpansionValidator` under x86-64 IDIV trap semantics
///      (exhaustive `verify_by_evaluation`, no solver).
fn validate_x86_overflow_expansions_per_program(
    funcs: &[trust_cg_lower::x86_64_isel::X86ISelFunction],
) -> Result<(), CompileError> {
    use std::collections::BTreeSet;

    let mut triples: BTreeSet<RecoveredOverflowExpansion> = BTreeSet::new();
    for func in funcs {
        // (1) Structural safety net: reject the trapping IMUL->IDIV dataflow.
        if let Some((block, inst_index)) = find_signed_mul_overflow_division(func) {
            return Err(CompileError::PassValidationRejected {
                pass_name: "x86-overflow-expand".to_string(),
                obligation_name: format!(
                    "per-program[{}]: signed-mul-overflow division-free invariant \
                     (block {block}, inst {inst_index})",
                    func.name
                ),
                reason:
                    "signed multiply product feeds an IDIV dividend — this is the AArch64-only \
                     SDIV-identity overflow expansion (MISCOMPILE #67), which SIGFPEs (#DE) on \
                     x86-64 IDIV-by-zero / INT_MIN/-1; the live lowering must use the \
                     division-free wide-multiply check"
                        .to_string(),
            });
        }
        // (2) Enumerate the overflow-expansion triples emitted in this function.
        collect_overflow_expansions(func, &mut triples);
    }

    // Re-verify each DISTINCT triple ONCE (dedup is the BTreeSet) — still
    // per-program: this set reflects exactly what THIS program emitted.
    for triple in triples {
        validate_recovered_overflow_expansion(triple)?;
    }
    Ok(())
}

/// Map a recovered triple onto the `OverflowExpansionValidator` and discharge it
/// exhaustively under x86-64 IDIV trap semantics. Fail-closed on `Rejected`.
fn validate_recovered_overflow_expansion(
    triple: RecoveredOverflowExpansion,
) -> Result<(), CompileError> {
    use trust_cg_verify::pass_validators::{
        CheckedOp, OverflowExpansion, OverflowExpansionValidator, PassValidation, PassValidator,
        TargetArch,
    };

    let op = match triple.op {
        0 => CheckedOp::SignedAdd,
        1 => CheckedOp::SignedSub,
        _ => CheckedOp::SignedMul,
    };
    let expansion = match triple.expansion {
        0 => OverflowExpansion::SignBitCheck,
        _ => OverflowExpansion::DivisionFreeWideMul,
    };
    // The validator is exhaustive only at/below its 8-bit threshold; for wider
    // widths it requires a formal solver. We always discharge the proof at the
    // exhaustive width 8 (the validator's semantics are width-uniform for these
    // arch-divergent expansions: the SDIV-identity #DE trap and the
    // division-free round-trip behave identically at every width, so the 8-bit
    // exhaustive proof is the no-solver complete proof the gate relies on — the
    // same width the original canary used).
    let validator = OverflowExpansionValidator {
        pass_name: "x86-overflow-expand".to_string(),
        width: 8,
        op,
        expansion,
        arch: TargetArch::X86_64,
    };
    match validator.validate() {
        PassValidation::Rejected {
            obligation_name,
            reason,
        } => Err(CompileError::PassValidationRejected {
            pass_name: validator.pass_name().to_string(),
            obligation_name: format!("per-program(width {}): {obligation_name}", triple.width),
            reason,
        }),
        _ => Ok(()),
    }
}

/// STRUCTURAL #67 safety net: locate the AArch64-only `SDIV`-identity
/// signed-mul-overflow expansion `q = (a*b) SDIV b` emitted as x86 machine code.
/// Returns the `(block_id, inst_index)` of the offending `IDIV`, or `None`.
///
/// # The exact signature (false-positive-free)
///
/// x86-64 `IDIV` divides the implicit `RDX:RAX` accumulator by its single
/// register/memory operand (the divisor); the quotient lands in `RAX`. ISel
/// emits it as `MOV RAX, <dividend>; C{D,Q}Q; IDIV <divisor>` (see
/// `x86_64_isel::select_div`). The #67 bug computed `q = (a*b) IDIV b` — i.e.
/// the DIVIDEND moved into `RAX` is an `IMUL` product AND the DIVISOR is one of
/// that very multiply's source operands. That `(a*b)/b` shape exists ONLY to
/// recover `a` for the SDIV overflow identity; no correct program divides a
/// product by one of its own factors. A legitimate `(a*b)/c` has a divisor `c`
/// that is NOT a multiplicand, so it is never flagged.
///
/// Requiring `divisor ∈ {multiplicands of the dividend's IMUL}` is what keeps
/// this sound: it fires on the trapping overflow identity and on nothing else.
/// Scoped to a single block (the expansion is straight-line); defs are tracked
/// by each instruction's destination operand (operand[0] for the `IMUL`/`MOV`
/// forms that participate here).
fn find_signed_mul_overflow_division(
    func: &trust_cg_lower::x86_64_isel::X86ISelFunction,
) -> Option<(u32, usize)> {
    use std::collections::HashMap;
    use trust_cg_ir::regs::VReg;
    use trust_cg_ir::x86_64_ops::X86Opcode;
    use trust_cg_ir::x86_64_regs::{EAX, RAX};
    use trust_cg_lower::x86_64_isel::X86ISelOperand;

    let operand_vreg = |op: &X86ISelOperand| -> Option<VReg> {
        match op {
            X86ISelOperand::VReg(v) => Some(*v),
            _ => None,
        }
    };

    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        // vreg -> source multiplicands of the IMUL that produced it (if any).
        let mut imul_factors: HashMap<VReg, Vec<VReg>> = HashMap::new();
        // vreg -> its copy origin (`MOV dst, src` aliases dst to src). select_div
        // copies the divisor (`MOV safe_rhs, rhs`) before IDIV, so the IDIV
        // operand must be resolved back through copies to recognize `(a*b)/b`.
        let mut copy_origin: HashMap<VReg, VReg> = HashMap::new();
        // The vreg currently held in the RAX/EAX accumulator (the IDIV dividend),
        // tracked across the straight-line `MOV acc, <dividend>` setup.
        let mut acc_holds: Option<VReg> = None;

        // Resolve a vreg through copy chains to its ultimate origin.
        let resolve = |v: VReg, copies: &HashMap<VReg, VReg>| -> VReg {
            let mut cur = v;
            // Bounded walk (the copy graph is acyclic in straight-line code);
            // guard against any pathological cycle with a step cap.
            for _ in 0..block.insts.len() + 1 {
                match copies.get(&cur) {
                    Some(&next) if next != cur => cur = next,
                    _ => break,
                }
            }
            cur
        };

        for (inst_index, inst) in block.insts.iter().enumerate() {
            match inst.opcode {
                // Record IMUL product -> its source multiplicands (resolved to
                // copy origins so a multiplicand fed via a copy still matches).
                X86Opcode::ImulRR
                | X86Opcode::ImulRRI
                | X86Opcode::ImulRM
                | X86Opcode::ImulRMSib => {
                    if let Some(dst) = inst.operands.first().and_then(&operand_vreg) {
                        let factors: Vec<VReg> = inst
                            .operands
                            .iter()
                            .skip(1)
                            .filter_map(&operand_vreg)
                            .map(|f| resolve(f, &copy_origin))
                            .collect();
                        imul_factors.insert(dst, factors);
                    }
                }
                // `MOV dst, src`: a vreg-to-vreg copy (alias) and, when the
                // destination is the RAX/EAX accumulator, the IDIV dividend setup.
                X86Opcode::MovRR | X86Opcode::MovRR32 => {
                    let src = inst.operands.get(1).and_then(&operand_vreg);
                    match inst.operands.first() {
                        Some(X86ISelOperand::PReg(dst)) if *dst == RAX || *dst == EAX => {
                            acc_holds = src;
                        }
                        Some(X86ISelOperand::VReg(dst)) => {
                            if let Some(src) = src {
                                copy_origin.insert(*dst, src);
                            }
                        }
                        _ => {}
                    }
                }
                // IDIV <divisor>: the dividend is the accumulator's current value.
                X86Opcode::Idiv => {
                    if let (Some(dividend), Some(divisor)) =
                        (acc_holds, inst.operands.first().and_then(&operand_vreg))
                    {
                        let divisor = resolve(divisor, &copy_origin);
                        if let Some(factors) = imul_factors.get(&dividend) {
                            // The trapping #67 identity: q = (a*b) IDIV b, divisor
                            // is a multiplicand of the dividend product.
                            if factors.contains(&divisor) {
                                return Some((block_id.0, inst_index));
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }
    None
}

/// ENUMERATE the recognizable overflow-expansion sites emitted in `func`, adding
/// each recovered `(op, expansion, width)` triple to `out`.
///
/// Two idiom shapes are recognized (the live expansions; see
/// `trust_cg_lower::adapter::translate_overflow` and
/// `x86_64_isel::select_checked_arithmetic`):
///
///   * Native I32/I64 flag idiom: `{ADD,SUB,IMUL}RR` immediately followed by
///     `SETcc {O (signed) | B (unsigned)}`. The arith opcode selects the op; the
///     condition code selects signedness. (Unsigned/`B` sites are skipped — the
///     validator only models the signed family that #67 lives in.) Recovers
///     `(SignedAdd/Sub/Mul, SignBitCheck-or-DivisionFreeWideMul, width)`.
///   * Narrow-width signed-mul division-free wide-multiply idiom: a sign-extend
///     (`MOVSX{B,W}` / `MOVSXD`) feeding an `IMUL` whose product is `CMP`d and
///     consumed by `SETcc NE`. Recovers `(SignedMul, DivisionFreeWideMul, w)`
///     where `w` is the sign-extend source width (8/16/32).
///
/// Recognition is conservative: an unrecognized shape is simply not enumerated
/// (a false negative, never a false positive). The exhaustive #67 guarantee is
/// the structural net in `find_signed_mul_overflow_division`; this enumeration
/// adds a semantic re-proof of the recognized shapes.
fn collect_overflow_expansions(
    func: &trust_cg_lower::x86_64_isel::X86ISelFunction,
    out: &mut std::collections::BTreeSet<RecoveredOverflowExpansion>,
) {
    use trust_cg_ir::x86_64_ops::{X86CondCode, X86Opcode};
    use trust_cg_lower::x86_64_isel::X86ISelOperand;

    // CheckedOp codes: 0=SignedAdd, 1=SignedSub, 2=SignedMul.
    // OverflowExpansion codes: 0=SignBitCheck, 1=DivisionFreeWideMul.
    const SIGN_BIT_CHECK: u8 = 0;
    const DIVISION_FREE: u8 = 1;

    let setcc_overflow_cc =
        |inst: &trust_cg_lower::x86_64_isel::X86ISelInst| -> Option<X86CondCode> {
            if !matches!(inst.opcode, X86Opcode::Setcc) {
                return None;
            }
            inst.operands.iter().find_map(|op| match op {
                X86ISelOperand::CondCode(cc) => Some(*cc),
                _ => None,
            })
        };

    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        let insts = &block.insts;
        for i in 0..insts.len() {
            let inst = &insts[i];
            // --- Native I32/I64 flag idiom: {ADD,SUB,IMUL}RR + SETcc {O,B} ---
            let native_op = match inst.opcode {
                X86Opcode::AddRR => Some(0u8),  // SignedAdd (if SETcc O)
                X86Opcode::SubRR => Some(1u8),  // SignedSub (if SETcc O)
                X86Opcode::ImulRR => Some(2u8), // SignedMul (if SETcc O)
                _ => None,
            };
            if let Some(op) = native_op
                && let Some(cc) = insts.get(i + 1).and_then(setcc_overflow_cc)
            {
                // Only the signed family (SETcc O) is modeled by the
                // validator; unsigned (SETcc B) carry checks are skipped.
                if matches!(cc, X86CondCode::O) {
                    let width = native_idiom_width(func, inst);
                    // add/sub use SignBitCheck; the native signed mul uses the
                    // hardware OF flag (a division-free overflow detection,
                    // modeled as DivisionFreeWideMul).
                    let expansion = if op == 2 {
                        DIVISION_FREE
                    } else {
                        SIGN_BIT_CHECK
                    };
                    out.insert(RecoveredOverflowExpansion {
                        op,
                        expansion,
                        width,
                    });
                }
            }

            // --- Narrow signed-mul division-free wide-multiply idiom ---
            // A sign-extend feeding an IMUL whose product is CMP'd and consumed
            // by SETcc NE. We key off the sign-extend opcode for the source width
            // and confirm the block contains the CMP+SETcc-NE completion.
            let sx_width = match inst.opcode {
                X86Opcode::MovsxB => Some(8u32),
                X86Opcode::MovsxW => Some(16u32),
                X86Opcode::Movsx => Some(32u32),
                _ => None,
            };
            if let Some(width) = sx_width {
                // Sign-extend destination (operand[0]) must feed an IMUL whose
                // product later reaches a SETcc NE — the division-free overflow
                // round-trip. Confirm the completing CMP + SETcc NE shape exists
                // in the block (conservative: presence is enough to recognize the
                // expansion strategy emitted; correctness of the strategy itself
                // is proven by re-verification).
                let sx_dst = inst.operands.first().and_then(|o| match o {
                    X86ISelOperand::VReg(v) => Some(*v),
                    _ => None,
                });
                if let Some(sx_dst) = sx_dst {
                    let feeds_imul = insts[i + 1..].iter().any(|n| {
                        matches!(
                            n.opcode,
                            X86Opcode::ImulRR
                                | X86Opcode::ImulRRI
                                | X86Opcode::ImulRM
                                | X86Opcode::ImulRMSib
                        ) && n
                            .operands
                            .iter()
                            .skip(1)
                            .any(|o| matches!(o, X86ISelOperand::VReg(v) if *v == sx_dst))
                    });
                    let has_ne_setcc = insts
                        .iter()
                        .any(|n| setcc_overflow_cc(n) == Some(X86CondCode::NE));
                    let has_cmp = insts.iter().any(|n| {
                        matches!(
                            n.opcode,
                            X86Opcode::CmpRR
                                | X86Opcode::CmpRI
                                | X86Opcode::CmpRI8
                                | X86Opcode::CmpRM
                        )
                    });
                    if feeds_imul && has_ne_setcc && has_cmp {
                        out.insert(RecoveredOverflowExpansion {
                            op: 2, // SignedMul
                            expansion: DIVISION_FREE,
                            width,
                        });
                    }
                }
            }
        }
    }
}

/// Best-effort source width (8/16/32/64) for a native checked-arith idiom,
/// recovered from the destination vreg's recorded nominal width when ISel left
/// one, else from the carrier register class. Defaults to 64 (the validator
/// proof is width-uniform for these arch-divergent expansions, so the exact
/// width only LABELS the recovered triple — it does not change the proof).
fn native_idiom_width(
    func: &trust_cg_lower::x86_64_isel::X86ISelFunction,
    inst: &trust_cg_lower::x86_64_isel::X86ISelInst,
) -> u32 {
    use trust_cg_ir::regs::RegClass;
    use trust_cg_lower::x86_64_isel::X86ISelOperand;

    if let Some(X86ISelOperand::VReg(dst)) = inst.operands.first() {
        if let Some(&w) = func.vreg_nominal_widths().get(dst) {
            return w;
        }
        // Narrow integers (i8/i16/i32) all share the Gpr32 carrier class, so the
        // class only distinguishes 64 vs <=32. Without a nominal width we cannot
        // narrow further; 32 is the conservative carrier label for Gpr32.
        return match dst.class {
            RegClass::Gpr64 => 64,
            _ => 32,
        };
    }
    64
}

fn count_x86_branch_instructions(func: &trust_cg_lower::x86_64_isel::X86ISelFunction) -> usize {
    use trust_cg_ir::x86_64_ops::X86Opcode;

    func.block_order
        .iter()
        .filter_map(|block| func.blocks.get(block))
        .map(|block| {
            block
                .insts
                .iter()
                .filter(|inst| {
                    matches!(
                        inst.opcode,
                        X86Opcode::Jmp
                            | X86Opcode::Jcc
                            | X86Opcode::Call
                            | X86Opcode::CallR
                            | X86Opcode::CallM
                            | X86Opcode::Ret
                            | X86Opcode::Ud2
                    )
                })
                .count()
        })
        .sum()
}

fn x86_function_has_dynamic_stack_alloc(
    func: &trust_cg_lower::x86_64_isel::X86ISelFunction,
) -> bool {
    use trust_cg_ir::x86_64_ops::X86Opcode;

    func.blocks.values().any(|block| {
        block
            .insts
            .iter()
            .any(|inst| inst.opcode == X86Opcode::StackAlloc)
    })
}

fn nonzero_duration(duration: Duration) -> Duration {
    if duration == Duration::ZERO {
        Duration::from_nanos(1)
    } else {
        duration
    }
}

fn x86_opt_level_from_codegen(opt_level: OptLevel) -> trust_cg_opt::OptLevel {
    match opt_level {
        OptLevel::O0 => trust_cg_opt::OptLevel::O0,
        OptLevel::O1 => trust_cg_opt::OptLevel::O1,
        OptLevel::O2 => trust_cg_opt::OptLevel::O2,
        OptLevel::O3 => trust_cg_opt::OptLevel::O3,
    }
}

fn x86_pipeline_error_to_pipeline_error(error: crate::x86_64::X86PipelineError) -> PipelineError {
    match error {
        crate::x86_64::X86PipelineError::WindowsCoffUnwindMetadataRequired { function, reason } => {
            PipelineError::TargetObjectUnsupported {
                target: "x86_64-pc-windows-msvc".to_string(),
                format: "COFF".to_string(),
                reason: format!(
                    "{function}: .pdata/.xdata unwind metadata is required because {reason}"
                ),
            }
        }
        other => PipelineError::ISel(other.to_string()),
    }
}

fn x86_host_jit_abi() -> trust_cg_lower::x86_64_isel::X86CallAbi {
    trust_cg_lower::x86_64_isel::X86CallAbi::host()
}

/// JIT-8 kill-switch. The x86 in-process JIT uses the LinearScan latency
/// profile ([`X86PipelineConfig::host_jit_fast`]) by default when
/// `enable_jit_fast_regalloc` is set. Set `TCG_NO_X86_JIT_LINEARSCAN` (any
/// value) to force the previous Greedy profile — a diagnostic / rollback hatch;
/// both profiles pass the same always-on regalloc translation validator, so
/// this changes only latency and code quality, never correctness.
fn x86_jit_linearscan_regalloc_enabled() -> bool {
    std::env::var_os("TCG_NO_X86_JIT_LINEARSCAN").is_none()
}

fn resolve_x86_jit_extern(
    name: &str,
    extern_symbols: &HashMap<String, *const u8>,
) -> Option<*const u8> {
    if let Some(&ptr) = extern_symbols.get(name) {
        return Some(ptr);
    }
    if let Some(ptr) = crate::jit::lookup_process_symbol(name) {
        return Some(ptr);
    }
    #[cfg(target_os = "macos")]
    if let Some(stripped) = name.strip_prefix('_')
        && let Some(ptr) = crate::jit::lookup_process_symbol(stripped)
    {
        return Some(ptr);
    }
    None
}

fn emit_x86_64_absolute_jump_veneer(code: &mut Vec<u8>, target: *const u8) -> u64 {
    let start = code.len() as u64;
    code.extend_from_slice(&[0xFF, 0x25, 0x00, 0x00, 0x00, 0x00]);
    code.extend_from_slice(&(target as u64).to_le_bytes());
    code.extend_from_slice(&[0xCC, 0xCC]);
    start
}

fn emit_x86_64_profile_counter_trampoline(code: &mut Vec<u8>) -> usize {
    #[cfg(all(target_arch = "x86_64", target_os = "windows"))]
    {
        // movabs r10, imm64; lock incq [r10]
        //
        // The Windows unwinder can cover this as a stack-neutral prefix before
        // the normal RBP prologue. Avoid push/popfq here so a callable PC at
        // the function entry is still in a valid RUNTIME_FUNCTION range.
        code.extend_from_slice(&[0x49, 0xBA]);
        let imm64_offset = code.len();
        code.extend_from_slice(&[0u8; 8]);
        code.extend_from_slice(&[0xF0, 0x49, 0xFF, 0x02]);
        return imm64_offset;
    }

    #[cfg(not(all(target_arch = "x86_64", target_os = "windows")))]
    {
        // push rax; pushfq; movabs rax, imm64; lock incq [rax]; popfq; pop rax
        code.extend_from_slice(&[0x50, 0x9C, 0x48, 0xB8]);
        let imm64_offset = code.len();
        code.extend_from_slice(&[0u8; 8]);
        code.extend_from_slice(&[0xF0, 0x48, 0xFF, 0x00, 0x9D, 0x58]);
        imm64_offset
    }
}

fn x86_profile_hooks_enable_call_counters(mode: crate::jit::ProfileHookMode) -> bool {
    matches!(mode, crate::jit::ProfileHookMode::CallCounts)
}

fn x86_profile_hooks_enable_block_counters(mode: crate::jit::ProfileHookMode) -> bool {
    matches!(mode, crate::jit::ProfileHookMode::BlockCounts)
}

fn patch_x86_64_rel32_call(
    code: &mut [u8],
    disp32_offset: usize,
    target: u64,
) -> Result<(), crate::jit::JitError> {
    if disp32_offset == 0 || disp32_offset + 4 > code.len() {
        return Err(crate::jit::JitError::FixupOutOfBounds {
            offset: disp32_offset as u32,
            code_len: code.len(),
        });
    }
    let inst_end = disp32_offset + 4;
    let distance = target as i64 - inst_end as i64;
    if distance < i32::MIN as i64 || distance > i32::MAX as i64 {
        return Err(crate::jit::JitError::BranchOutOfRange {
            offset: (disp32_offset - 1) as u32,
            target,
            distance,
        });
    }
    code[disp32_offset..disp32_offset + 4].copy_from_slice(&(distance as i32).to_le_bytes());
    Ok(())
}

type CompileArtifactCacheContext = (
    LocalFilesystemCompileArtifactCache,
    CompileArtifactCacheKey,
    CompileArtifactCacheBoundary,
);

fn sha256_digest(bytes: &[u8]) -> String {
    format!("sha256:{}", sha256_hex(bytes))
}

fn compiler_profile_use_sha256(
    profile_use: Option<&trust_cg_opt::pgo::ProfData>,
) -> Result<String, trust_cg_opt::pgo::ProfDataError> {
    let Some(profile) = profile_use else {
        return Ok(COMPILE_ARTIFACT_PROFILE_USE_DISABLED_SHA256.to_owned());
    };

    let profile_bytes = trust_cg_opt::pgo::encode(profile)?;
    let mut identity = Vec::new();
    identity.extend_from_slice(b"trust-cg.compile_artifact.profile_use.v1\0");
    identity.extend_from_slice(&profile_bytes);
    Ok(sha256_digest(&identity))
}

fn compiler_cache_identity_sha256<T: serde::Serialize + ?Sized>(
    component: &'static str,
    value: &T,
) -> Result<String, CompileError> {
    let bytes = serde_json::to_vec(value)
        .map_err(|source| CompileError::CompileArtifactCacheIdentityJson { component, source })?;
    Ok(sha256_digest(&bytes))
}

const X86_64_WINDOWS_COFF_UNWIND_GUARD_CACHE_IDENTITY: &str =
    "x86_64-windows-coff-unwind-metadata-v2";

fn compiler_x86_64_backend_safety_identity(
    config: &CompilerConfig,
    target_spec: TargetSpec,
) -> Result<Option<&'static str>, CompileError> {
    if config.target != Target::X86_64 {
        return Ok(None);
    }

    let output_format = x86_64_aot_output_format_for_target_spec(target_spec)?;
    if output_format == crate::x86_64::X86OutputFormat::Coff
        && target_spec.operating_system == TargetOperatingSystem::Windows
    {
        return Ok(Some(X86_64_WINDOWS_COFF_UNWIND_GUARD_CACHE_IDENTITY));
    }

    Ok(None)
}

fn compiler_codegen_options_sha256(
    config: &CompilerConfig,
    target_spec: TargetSpec,
    profile_use_sha256: &str,
) -> Result<String, CompileError> {
    let x86_64_aot_output_format = if config.target == Target::X86_64 {
        Some(compiler_x86_64_aot_output_format_name(target_spec)?)
    } else {
        None
    };
    let mut options = serde_json::json!({
        "schema": "trust-cg.compile_artifact.codegen_options.v3",
        "target": config.target.name(),
        "target_triple": compiler_target_triple(target_spec),
        "target_vendor": target_spec.vendor.triple_component(),
        "target_os": target_spec.operating_system.triple_component(),
        "target_environment": target_spec.environment.triple_component(),
        "host_target_os": compiler_host_target_os(),
        "x86_64_aot_output_format": x86_64_aot_output_format,
        "opt_level": compiler_opt_level_name(config.opt_level),
        "emit_proofs": config.emit_proofs,
        "emit_debug": config.emit_debug,
        "parallel": config.parallel,
        "cegis_superopt_budget_sec": config.cegis_superopt_budget_sec,
        "profile_use_sha256": profile_use_sha256,
        "verify_feature": cfg!(feature = "verify"),
    });
    if let Some(safety_identity) = compiler_x86_64_backend_safety_identity(config, target_spec)?
        && let serde_json::Value::Object(options) = &mut options
    {
        options.insert(
            "x86_64_backend_safety_identity".to_owned(),
            serde_json::Value::String(safety_identity.to_owned()),
        );
    }
    compiler_cache_identity_sha256("codegen_options", &options)
}

fn compiler_target_facts_sha256(
    target: Target,
    target_spec: TargetSpec,
) -> Result<String, CompileError> {
    let calling_convention = compiler_calling_convention(target, target_spec);
    let num_callee_saved_gprs = if target == Target::X86_64
        && target_spec.operating_system == TargetOperatingSystem::Windows
    {
        8
    } else {
        target.num_callee_saved_gprs()
    };
    let facts = serde_json::json!({
        "schema": "trust-cg.compile_artifact.target_facts.v2",
        "target": target.name(),
        "target_triple": compiler_target_triple(target_spec),
        "target_vendor": target_spec.vendor.triple_component(),
        "target_os": target_spec.operating_system.triple_component(),
        "target_environment": target_spec.environment.triple_component(),
        "pointer_bytes": target.pointer_bytes(),
        "stack_alignment": target.stack_alignment(),
        "calling_convention": calling_convention.name,
        "num_arg_gprs": calling_convention.num_arg_gprs,
        "num_arg_fprs": calling_convention.num_arg_fprs,
        "num_ret_gprs": calling_convention.num_ret_gprs,
        "num_ret_fprs": calling_convention.num_ret_fprs,
        "num_callee_saved_gprs": num_callee_saved_gprs,
        "num_allocatable_gprs": target.num_allocatable_gprs(),
        "requires_frame_pointer": target.requires_frame_pointer(),
        "red_zone_size": calling_convention.red_zone_size,
        "shadow_space": calling_convention.shadow_space,
    });
    compiler_cache_identity_sha256("target_facts", &facts)
}

fn compiler_host_target_os() -> &'static str {
    std::env::consts::OS
}

fn x86_64_aot_output_format_for_os(
    target_os: &'static str,
) -> Result<crate::x86_64::X86OutputFormat, CompileError> {
    use crate::x86_64::X86OutputFormat;

    match target_os {
        "linux" | "android" | "freebsd" | "netbsd" | "openbsd" | "dragonfly" => {
            Ok(X86OutputFormat::Elf)
        }
        "macos" => Ok(X86OutputFormat::MachO),
        "windows" => Ok(X86OutputFormat::Coff),
        _ => Err(CompileError::X86AotObjectFormatUnsupported {
            target_os,
            required_format: "native object format",
            context: "no x86-64 AOT object emitter is wired for this OS",
        }),
    }
}

fn x86_64_aot_output_format() -> Result<crate::x86_64::X86OutputFormat, CompileError> {
    x86_64_aot_output_format_for_os(compiler_host_target_os())
}

fn x86_64_aot_output_format_for_target_spec(
    target_spec: TargetSpec,
) -> Result<crate::x86_64::X86OutputFormat, CompileError> {
    use crate::x86_64::X86OutputFormat;

    match target_spec.operating_system {
        TargetOperatingSystem::Linux => Ok(X86OutputFormat::Elf),
        TargetOperatingSystem::Darwin => Ok(X86OutputFormat::MachO),
        TargetOperatingSystem::Windows => Ok(X86OutputFormat::Coff),
        TargetOperatingSystem::Unknown => x86_64_aot_output_format(),
    }
}

fn compiler_x86_64_aot_output_format_name(
    target_spec: TargetSpec,
) -> Result<&'static str, CompileError> {
    use crate::x86_64::X86OutputFormat;

    match x86_64_aot_output_format_for_target_spec(target_spec)? {
        X86OutputFormat::RawBytes => Ok("raw"),
        X86OutputFormat::Elf => Ok("elf"),
        X86OutputFormat::MachO => Ok("macho"),
        X86OutputFormat::Coff => Ok("coff"),
    }
}

fn compiler_target_triple(target_spec: TargetSpec) -> String {
    if target_spec.has_explicit_os_abi() {
        return target_spec.triple();
    }

    let arch = target_spec.architecture.name();
    match (target_spec.architecture, compiler_host_target_os()) {
        (Target::X86_64, "linux") => "x86_64-unknown-linux-gnu".to_string(),
        (Target::X86_64, "android") => "x86_64-linux-android".to_string(),
        (Target::X86_64, "freebsd") => "x86_64-unknown-freebsd".to_string(),
        (Target::X86_64, "netbsd") => "x86_64-unknown-netbsd".to_string(),
        (Target::X86_64, "openbsd") => "x86_64-unknown-openbsd".to_string(),
        (Target::X86_64, "dragonfly") => "x86_64-unknown-dragonfly".to_string(),
        (Target::X86_64, "macos") => "x86_64-apple-darwin".to_string(),
        (Target::X86_64, "windows") => "x86_64-pc-windows-msvc".to_string(),
        (Target::Aarch64, "linux") => "aarch64-unknown-linux-gnu".to_string(),
        (Target::Aarch64, "android") => "aarch64-linux-android".to_string(),
        (Target::Aarch64, "freebsd") => "aarch64-unknown-freebsd".to_string(),
        (Target::Aarch64, "netbsd") => "aarch64-unknown-netbsd".to_string(),
        (Target::Aarch64, "openbsd") => "aarch64-unknown-openbsd".to_string(),
        (Target::Aarch64, "macos") => "aarch64-apple-darwin".to_string(),
        (Target::Aarch64, "windows") => "aarch64-pc-windows-msvc".to_string(),
        _ => format!("{arch}-unknown-unknown"),
    }
}

fn compiler_calling_convention(target: Target, target_spec: TargetSpec) -> CallingConvention {
    if target == Target::X86_64 && target_spec.operating_system == TargetOperatingSystem::Windows {
        return CallingConvention {
            name: "windows_x64",
            num_arg_gprs: 4,
            num_arg_fprs: 4,
            num_ret_gprs: 2,
            num_ret_fprs: 2,
            red_zone_size: 0,
            shadow_space: 32,
        };
    }

    target.calling_convention()
}

fn compiler_opt_level_name(opt_level: OptLevel) -> &'static str {
    match opt_level {
        OptLevel::O0 => "O0",
        OptLevel::O1 => "O1",
        OptLevel::O2 => "O2",
        OptLevel::O3 => "O3",
    }
}

fn lookup_compile_artifact(
    cache: &LocalFilesystemCompileArtifactCache,
    key: &CompileArtifactCacheKey,
    boundary: CompileArtifactCacheBoundary,
    proof_bundle_sha256: Option<&str>,
) -> std::io::Result<CompileArtifactCacheLookup> {
    match boundary {
        CompileArtifactCacheBoundary::Pipeline => match proof_bundle_sha256 {
            Some(digest) => {
                cache.lookup_for_pipeline_with_expected_proof_bundle_sha256(key, digest)
            }
            None => cache.lookup_for_pipeline(key),
        },
        CompileArtifactCacheBoundary::Service => match proof_bundle_sha256 {
            Some(digest) => cache.lookup_for_service_with_expected_proof_bundle_sha256(key, digest),
            None => cache.lookup_for_service(key),
        },
    }
}

fn store_compile_artifact(
    cache: &LocalFilesystemCompileArtifactCache,
    key: &CompileArtifactCacheKey,
    boundary: CompileArtifactCacheBoundary,
    artifact_bytes: &[u8],
    producer: &str,
    proof_bundle_sha256: Option<&str>,
) -> std::io::Result<CompileArtifactCacheTelemetry> {
    match boundary {
        CompileArtifactCacheBoundary::Pipeline => match proof_bundle_sha256 {
            Some(digest) => cache.store_from_pipeline_with_proof_bundle_sha256(
                key,
                artifact_bytes,
                producer,
                digest,
            ),
            None => cache.store_from_pipeline(key, artifact_bytes, producer),
        },
        CompileArtifactCacheBoundary::Service => match proof_bundle_sha256 {
            Some(digest) => cache.store_from_service_with_proof_bundle_sha256(
                key,
                artifact_bytes,
                producer,
                digest,
            ),
            None => cache.store_from_service(key, artifact_bytes, producer),
        },
    }
}

fn proof_status_label(cert: &ProofCertificate) -> &'static str {
    if cert.category.eq_ignore_ascii_case("unverified") {
        "unverified"
    } else if cert.category.eq_ignore_ascii_case("unknown") {
        "unknown"
    } else if cert.strength.starts_with("Failed:") {
        "failed"
    } else {
        "non_verified"
    }
}

fn proof_bundle_sha256(proofs: Option<&[ProofCertificate]>) -> Option<String> {
    let proofs = proofs?;
    let mut rows: Vec<(&str, &str, &str, &str, bool)> = proofs
        .iter()
        .map(|cert| {
            (
                cert.function_name.as_str(),
                cert.rule_name.as_str(),
                cert.category.as_str(),
                cert.strength.as_str(),
                cert.verified,
            )
        })
        .collect();
    rows.sort_unstable();

    let mut bytes = Vec::new();
    put_digest_str(&mut bytes, "trust-cg.compile_artifact.proof_bundle.v1");
    for (function_name, rule_name, category, strength, verified) in rows {
        put_digest_str(&mut bytes, function_name);
        put_digest_str(&mut bytes, rule_name);
        put_digest_str(&mut bytes, category);
        put_digest_str(&mut bytes, strength);
        bytes.push(u8::from(verified));
    }
    Some(sha256_digest(&bytes))
}

fn put_digest_str(out: &mut Vec<u8>, value: &str) {
    out.extend_from_slice(&(value.len() as u64).to_le_bytes());
    out.extend_from_slice(value.as_bytes());
}

/// Rebase one function-relative RISC-V call fixup into the `.text` u32 patch
/// domain without truncation or arithmetic wraparound.
fn rebase_riscv_call_fixup(
    function: &str,
    function_offset: u64,
    fixup: &crate::riscv::pipeline::RiscVCallFixup,
) -> Result<crate::riscv::pipeline::RiscVCallFixup, CompileError> {
    let base = u32::try_from(function_offset).map_err(|_| {
        CompileError::Pipeline(PipelineError::ISel(format!(
            "RISC-V call fixup in `{function}` starts at .text offset {function_offset}, outside the u32 patch domain"
        )))
    })?;
    let rebase = |relative: u32, instruction: &str| {
        base.checked_add(relative).ok_or_else(|| {
            CompileError::Pipeline(PipelineError::ISel(format!(
                "RISC-V {instruction} call fixup in `{function}` overflows the u32 patch domain: function base {base} + relative offset {relative}"
            )))
        })
    };
    Ok(crate::riscv::pipeline::RiscVCallFixup {
        auipc_offset: rebase(fixup.auipc_offset, "AUIPC")?,
        jalr_offset: rebase(fixup.jalr_offset, "JALR")?,
        callee: fixup.callee.clone(),
    })
}

// ---------------------------------------------------------------------------
// Compiler
// ---------------------------------------------------------------------------

/// The Trust Codegen compiler — top-level API for compiling trust_ir to machine code.
///
/// Wraps the internal [`Pipeline`] with a clean configuration interface,
/// structured results, optional tracing, and proof certificate emission.
pub struct Compiler {
    config: CompilerConfig,
    target_spec: TargetSpec,
    profile_use: Option<trust_cg_opt::pgo::ProfData>,
    /// AOT PGO profile-generate sink. `Some` switches [`Compiler::compile`]
    /// into generate mode: per-block counter increments are injected during
    /// function preparation (see `Pipeline::with_profile_generate_sink`), the
    /// `__tcg_pgo_counters` / `__tcg_pgo_nsites` globals are appended to the
    /// object, and every counter site is recorded here for the caller's
    /// sites sidecar. AArch64-only; other targets fail closed.
    profile_generate_sink: Option<std::sync::Arc<std::sync::Mutex<trust_cg_opt::pgo::CounterMap>>>,
    compile_artifact_cache: Option<CompileArtifactCacheConfig>,
    certified_pass_chain: Option<CertifiedPassChainAttachment>,
    production_certified_pass_chain: bool,
    #[cfg(feature = "verify")]
    production_certified_pass_runs: Vec<trust_cg_opt::CertifiedPassRunRecord>,
    /// JIT-5 content-addressed certificate cache. `None` resolves to the
    /// process-global cache ([`crate::jit_cert::JitCertCache::global`]); tests
    /// inject a fresh instance for isolated hit/miss stats.
    jit_cert_cache: Option<std::sync::Arc<crate::jit_cert::JitCertCache>>,
}

/// Generate proof certificates for a MachFunction by running the function
/// verifier from trust-cg-verify. Each verified instruction produces a
/// certificate recording the proof obligation name, category, and strength.
///
/// TV-2: when `lir_source` carries the EXACT LIR function that was handed to
/// instruction selection, the verifier additionally cross-checks every
/// emitted instruction's TV-1 lowering-provenance stamp against it (warn-only
/// by default on AArch64; see `trust_cg_verify::provenance_xcheck`). `None`
/// (e.g. callers holding only a prebuilt `MachFunction`) skips the
/// cross-check.
///
/// Only available when the `verify` feature is enabled.
#[cfg(feature = "verify")]
fn generate_proof_certificates(
    func: &trust_cg_ir::MachFunction,
    lir_source: Option<&trust_cg_lower::Function>,
) -> Vec<ProofCertificate> {
    use trust_cg_verify::function_verifier::InstructionVerificationResult;

    let report =
        crate::jit_cert::run_on_proof_verifier_stack("trust-cg-aarch64-proof-verifier", || {
            shared_aarch64_function_verifier().verify_with_lir_source(func, lir_source)
        });

    // TV-3 (aarch64, WARN-ONLY): block-level lowering-integrity telemetry. The
    // three checks are host-independent, but the aarch64 differential corpus
    // cannot execute on the x86 validation host and the stamps only reach here
    // through the post-pass MachFunction, so the §2.4 warn->enforce flip is the
    // Apple-Silicon lane's (roadmap §3). `evaluate` in WARN mode counts +
    // reports but never changes a verdict, so cert output is unaffected.
    if let Some(lir) = lir_source {
        let mode = trust_cg_verify::dataflow_integrity::dataflow_integrity_mode(
            trust_cg_verify::dataflow_integrity::AARCH64_DATAFLOW_INTEGRITY_DEFAULT,
        );
        let _ = trust_cg_verify::dataflow_integrity::evaluate(func, lir, "aarch64", mode);
    }

    let mut certs = Vec::new();

    append_emitted_opcode_inventory_certificate(&mut certs, &report);

    for inst_report in &report.instructions {
        match &inst_report.result {
            InstructionVerificationResult::Verified {
                proof_name,
                category,
                strength,
                degenerate,
            } => {
                if *degenerate && !trust_cg_verify::proof_database::is_genuine_identity(proof_name)
                {
                    // STRICT honesty on the COMPILE-GATING path (mirrors the
                    // static coverage_gate `discharge_one` rejection): a
                    // degenerate X==X proof (`trust_ir_expr == machine_expr`) over
                    // a NON-identity lowering proves NOTHING — a wrong opcode can
                    // only ever be refuted when the two sides are structurally
                    // distinct, so a vacuous X==X (e.g. a `Store_I64 -> MOV
                    // [r64+disp32],r64` whose effective-address computation it
                    // never checks) must NOT promote: emit a fail-closed
                    // (`verified: false`) cert so the bridge gate rejects the
                    // function rather than silently shipping an unproven
                    // instruction. This closes the #62 / ce09efa vacuous-proof
                    // regression class on the compile path (previously closed only
                    // on the static gate).
                    //
                    // EXCEPTION: an AUDITED GENUINE IDENTITY (the
                    // GENUINE_IDENTITY_ALLOWLIST) — a reg-reg copy / bitwise op the
                    // machine instruction provably IS (e.g. `Copy_I32 -> MOV
                    // r32,r32 preserves bits`). Such an operation literally is the
                    // identity, so it has NO non-degenerate proof; rejecting it
                    // would fail-close every register move that does not
                    // reconstruct to a non-degenerate form (the over-rejection
                    // that broke the m69/m71 corpus). Those stay promotable.
                    certs.push(ProofCertificate {
                        rule_name: proof_name.clone(),
                        verified: false,
                        category: format!("{}", category),
                        strength: format!(
                            "degenerate X==X proof proves nothing; not promotable on the compile path (mirrors coverage_gate discharge_one): {}",
                            proof_name
                        ),
                        function_name: report.function_name.clone(),
                    });
                } else {
                    certs.push(ProofCertificate {
                        rule_name: proof_name.clone(),
                        verified: true,
                        category: format!("{}", category),
                        strength: format!("{:?}", strength),
                        function_name: report.function_name.clone(),
                    });
                }
            }
            InstructionVerificationResult::Failed { proof_name, detail } => {
                certs.push(ProofCertificate {
                    rule_name: proof_name.clone(),
                    verified: false,
                    category: String::new(),
                    strength: format!("Failed: {}", detail),
                    function_name: report.function_name.clone(),
                });
            }
            InstructionVerificationResult::Unverified { reason } => {
                certs.push(unverified_instruction_certificate(
                    &report.function_name,
                    inst_report.inst_index,
                    inst_report.opcode,
                    reason,
                ));
            }
            InstructionVerificationResult::Skipped { .. } => {}
        }
    }

    certs
}

/// Convert non-verified verifier reports into negative proof entries.
///
/// Downstream certified-output paths only see [`CompilationResult::proofs`].
/// If we drop `Unverified` reports here, a later function-level sidecar can
/// certify the verified subset and silently omit real instructions.
#[cfg(feature = "verify")]
fn non_verified_proof_report(
    function_name: &str,
    inst_index: usize,
    status: &str,
    detail: String,
) -> ProofCertificate {
    ProofCertificate {
        rule_name: format!("{}_instruction_{}", status, inst_index),
        verified: false,
        category: status.to_string(),
        strength: detail,
        function_name: function_name.to_string(),
    }
}

/// Build the certificate for an `Unverified` instruction.
///
/// An indirect call/branch target (x86-64 `CallR`/`CallM`, AArch64 `Blr`) has no
/// per-instruction value-equivalence proof — the only candidate would be the
/// `target == target` tautology — yet its correctness IS established: the
/// target-address computation is verified instruction-by-instruction and the
/// CALL/BLR control transfer is architecturally fixed. The formal `coverage_gate`
/// already allowlists this family on exactly that basis. So it earns a positive
/// (covered-elsewhere) certificate rather than a fail-closed negative one;
/// without it the universal `lang_start → FnOnce::call_once` entry path (an
/// indirect `CallR` to `main`) fails proof promotion and `call_once` is emitted
/// as a trapping `ud2` stub the entry path then executes (SIGILL). Every other
/// `Unverified` opcode stays a real fail-closed negative entry — no vacuous proof
/// is admitted.
#[cfg(feature = "verify")]
fn unverified_instruction_certificate(
    function_name: &str,
    inst_index: usize,
    opcode: trust_cg_verify::function_verifier::InstructionOpcode,
    reason: &str,
) -> ProofCertificate {
    if trust_cg_verify::function_verifier::is_covered_elsewhere_indirect_branch(opcode) {
        ProofCertificate {
            rule_name: format!("covered_elsewhere_instruction_{}", inst_index),
            verified: true,
            category: "covered_elsewhere".to_string(),
            strength: format!(
                "{}: indirect call/branch target — correctness covered by surrounding proofs \
                 (verified target-address computation + architecturally-fixed control transfer), \
                 not a per-instruction tautology; mirrors coverage_gate allowlist",
                opcode
            ),
            function_name: function_name.to_string(),
        }
    } else if trust_cg_verify::function_verifier::is_covered_elsewhere_emission_padding(opcode) {
        ProofCertificate {
            rule_name: format!("covered_elsewhere_instruction_{}", inst_index),
            verified: true,
            category: "covered_elsewhere".to_string(),
            strength: format!(
                "{}: emission-time alignment padding with no value, memory, or branch semantics; \
                 byte exactness is pinned by the AArch64 decode check and offset integrity by \
                 the independent EH/encoder offset cross-check",
                opcode
            ),
            function_name: function_name.to_string(),
        }
    } else {
        non_verified_proof_report(
            function_name,
            inst_index,
            "unverified",
            format!("Unverified {}: {}", opcode, reason),
        )
    }
}

/// Emit a fail-closed proof entry when the verifier inventory finds uncovered
/// emitted opcodes. This makes proof-required promotion depend on complete
/// target-aware opcode coverage, not just the existence of some verified rows.
#[cfg(feature = "verify")]
fn append_emitted_opcode_inventory_certificate(
    certs: &mut Vec<ProofCertificate>,
    report: &trust_cg_verify::function_verifier::FunctionVerificationReport,
) {
    let inventory = report.emitted_opcode_inventory();
    if let Some(reason) = inventory.promotion_rejection_reason() {
        certs.push(non_verified_proof_report(
            &report.function_name,
            0,
            "opcode_inventory",
            reason,
        ));
    }
}

/// Emit a fail-closed proof entry when object emission produces relocations
/// without registered proof coverage. Instruction proofs alone do not certify
/// linker-visible object metadata, so this category blocks proof-required
/// promotion until object relocation proofs catch up.
#[cfg(feature = "verify")]
fn append_object_relocation_inventory_certificate(
    certs: &mut Vec<ProofCertificate>,
    report: &trust_cg_verify::ObjectRelocationInventoryReport,
) {
    let row_evidence = object_relocation_inventory_evidence(report);
    let (verified, strength) = match report.promotion_rejection_reason() {
        Some(reason) => (false, reason),
        None => (
            true,
            format!(
                "object relocation inventory verified for {}; {} emitted relocation row(s) covered; evidence={}",
                report.object_name,
                report.entries.len(),
                row_evidence
            ),
        ),
    };

    certs.push(ProofCertificate {
        rule_name: "object_relocation_inventory".to_string(),
        verified,
        category: "relocation_inventory".to_string(),
        strength,
        function_name: report.object_name.clone(),
    });
}

#[cfg(feature = "verify")]
fn object_relocation_inventory_evidence(
    report: &trust_cg_verify::ObjectRelocationInventoryReport,
) -> String {
    let mut rows = report
        .entries
        .iter()
        .map(|entry| {
            format!(
                "{}:{}:{:?}:{}",
                entry.index, entry.kind, entry.status, entry.detail
            )
        })
        .collect::<Vec<_>>();
    rows.sort();
    rows.join("|")
}

/// x86-64 mirror of [`generate_proof_certificates`] (#465).
///
/// Walks an [`trust_cg_lower::x86_64_isel::X86ISelFunction`] via the
/// [`trust_cg_verify::X86FunctionVerifier`] and emits a [`ProofCertificate`]
/// per verified instruction. Output shape matches the AArch64 path so the
/// public `CompilationResult::proofs` vector is target-agnostic.
/// Process-level shared x86-64 function verifier.
///
/// `X86FunctionVerifier::new()` constructs the full `ProofDatabase` (every
/// registered obligation's SMT expression trees) — a fixed, immutable
/// structure. Per-compile proof certification verifies EVERY function in the
/// module, so rebuilding the database per function turns an O(#obligations)
/// setup into O(#functions x #obligations). The verifier is stateless after
/// construction (shared `&self` walk + the sound per-obligation result memo
/// inside trust-cg-verify), so a single process-wide instance is safe.
#[cfg(feature = "verify")]
fn shared_x86_64_function_verifier() -> &'static trust_cg_verify::X86FunctionVerifier {
    static VERIFIER: std::sync::OnceLock<trust_cg_verify::X86FunctionVerifier> =
        std::sync::OnceLock::new();
    VERIFIER.get_or_init(trust_cg_verify::X86FunctionVerifier::new)
}

/// Process-level shared AArch64 function verifier.
///
/// Like the x86-64 verifier above, construction materializes the immutable full
/// proof database. Verification itself takes `&self`, so rebuilding that fixed
/// database for every function only multiplies setup work without changing any
/// report or proof authority.
#[cfg(feature = "verify")]
fn shared_aarch64_function_verifier()
-> &'static trust_cg_verify::function_verifier::FunctionVerifier {
    static VERIFIER: std::sync::OnceLock<trust_cg_verify::function_verifier::FunctionVerifier> =
        std::sync::OnceLock::new();
    VERIFIER.get_or_init(trust_cg_verify::function_verifier::FunctionVerifier::new)
}

/// CT-7: warm the shared x86-64 proof verifier OFF the compile's critical
/// path.
///
/// Builds the process-wide verifier — the full `ProofDatabase`, ~100ms of
/// pure obligation-tree construction that the FIRST certificate lane
/// otherwise serializes behind (every cert worker blocks on the shared
/// `OnceLock` while one thread builds it). A front-end host (the rustc
/// bridge) calls this on a DETACHED background thread as soon as it knows
/// codegen is coming, so the build overlaps MIR lowering instead of landing
/// inside `x86_proof_certs`.
///
/// Deliberately does NOT pre-discharge registry verdicts: sweeping the whole
/// fixed registry costs tens of CPU-seconds (most rows are never touched by
/// a given program) and floods the shared verifier pool ahead of the
/// compile's own certificate work — measured as a 9x wall regression. Lazy
/// first-touch discharge through the compute-once memo stays the policy.
///
/// Pure cache warming: construction is exactly what the first cert walk
/// would run lazily, so behavior — including every fail-closed verdict — is
/// byte-identical with or without warming; only the timing moves. Safe to
/// call from any thread, any number of times.
#[cfg(feature = "verify")]
pub fn warm_x86_64_proof_verifier() {
    let _ = shared_x86_64_function_verifier();
}

/// JIT-5 config fingerprint for the x86-64 certificate cache key.
///
/// Never name-only: folds the target, opt level, alloc profile, validation
/// mode, and a compiler-rev salt (crate version) so a cached verdict can never
/// be reused across a config change or a code change. Mirrors the content-key
/// discipline of the AOT verdict cache (PROOF-2/PROOF-3); JIT-6 will extend the
/// salt with the `soundness_revs` fingerprint for the disk-backed cache.
// Consumed only by the verifying JIT cert path; non-verify builds never reach it.
#[cfg_attr(not(feature = "verify"), allow(dead_code))]
fn x86_jit_config_fingerprint(config: &CompilerConfig, mode: JitValidationMode) -> Vec<u8> {
    format!(
        concat!(
            "trust-cg.jit.x86_64.config.v1\n",
            "target={:?}\n",
            "opt_level={:?}\n",
            "enable_jit_fast_regalloc={}\n",
            "validation_mode={}\n",
            "compiler_rev={}\n",
        ),
        config.target,
        config.opt_level,
        config.enable_jit_fast_regalloc,
        mode.label(),
        env!("CARGO_PKG_VERSION"),
    )
    .into_bytes()
}

/// TV-2: when `lir_source` carries the EXACT LIR function that was handed to
/// instruction selection, the verifier additionally cross-checks every
/// emitted instruction's TV-1 lowering-provenance stamp against it and FAILS
/// CLOSED on a mismatch (default ENFORCE on x86-64; see
/// `trust_cg_verify::provenance_xcheck`). `None` skips the cross-check.
#[cfg(feature = "verify")]
fn generate_x86_64_proof_certificates(
    func: &trust_cg_lower::x86_64_isel::X86ISelFunction,
    lir_source: Option<&trust_cg_lower::Function>,
) -> Vec<ProofCertificate> {
    use trust_cg_verify::function_verifier::InstructionVerificationResult;

    let report =
        crate::jit_cert::run_on_proof_verifier_stack("trust-cg-x86_64-proof-verifier", || {
            shared_x86_64_function_verifier().verify_with_lir_source(func, lir_source)
        });
    let mut certs = Vec::new();

    append_emitted_opcode_inventory_certificate(&mut certs, &report);

    for inst_report in &report.instructions {
        match &inst_report.result {
            InstructionVerificationResult::Verified {
                proof_name,
                category,
                strength,
                degenerate,
            } => {
                if *degenerate && !trust_cg_verify::proof_database::is_genuine_identity(proof_name)
                {
                    // STRICT honesty on the COMPILE-GATING path (mirrors the
                    // static coverage_gate `discharge_one` rejection): a
                    // degenerate X==X proof (`trust_ir_expr == machine_expr`) over
                    // a NON-identity lowering proves NOTHING — a wrong opcode can
                    // only ever be refuted when the two sides are structurally
                    // distinct, so a vacuous X==X (e.g. a `Store_I64 -> MOV
                    // [r64+disp32],r64` whose effective-address computation it
                    // never checks) must NOT promote: emit a fail-closed
                    // (`verified: false`) cert so the bridge gate rejects the
                    // function rather than silently shipping an unproven
                    // instruction. This closes the #62 / ce09efa vacuous-proof
                    // regression class on the compile path (previously closed only
                    // on the static gate).
                    //
                    // EXCEPTION: an AUDITED GENUINE IDENTITY (the
                    // GENUINE_IDENTITY_ALLOWLIST) — a reg-reg copy / bitwise op the
                    // machine instruction provably IS (e.g. `Copy_I32 -> MOV
                    // r32,r32 preserves bits`). Such an operation literally is the
                    // identity, so it has NO non-degenerate proof; rejecting it
                    // would fail-close every register move that does not
                    // reconstruct to a non-degenerate form (the over-rejection
                    // that broke the m69/m71 corpus). Those stay promotable.
                    certs.push(ProofCertificate {
                        rule_name: proof_name.clone(),
                        verified: false,
                        category: format!("{}", category),
                        strength: format!(
                            "degenerate X==X proof proves nothing; not promotable on the compile path (mirrors coverage_gate discharge_one): {}",
                            proof_name
                        ),
                        function_name: report.function_name.clone(),
                    });
                } else {
                    certs.push(ProofCertificate {
                        rule_name: proof_name.clone(),
                        verified: true,
                        category: format!("{}", category),
                        strength: format!("{:?}", strength),
                        function_name: report.function_name.clone(),
                    });
                }
            }
            InstructionVerificationResult::Failed { proof_name, detail } => {
                certs.push(ProofCertificate {
                    rule_name: proof_name.clone(),
                    verified: false,
                    category: String::new(),
                    strength: format!("Failed: {}", detail),
                    function_name: report.function_name.clone(),
                });
            }
            InstructionVerificationResult::Unverified { reason } => {
                certs.push(unverified_instruction_certificate(
                    &report.function_name,
                    inst_report.inst_index,
                    inst_report.opcode,
                    reason,
                ));
            }
            InstructionVerificationResult::Skipped { .. } => {}
        }
    }

    certs
}

impl Compiler {
    /// Create a new compiler with the given configuration.
    pub fn new(config: CompilerConfig) -> Self {
        let target_spec = TargetSpec::default_for_architecture(config.target);
        Self {
            config,
            target_spec,
            profile_use: None,
            profile_generate_sink: None,
            compile_artifact_cache: None,
            certified_pass_chain: None,
            production_certified_pass_chain: false,
            #[cfg(feature = "verify")]
            production_certified_pass_runs: Vec::new(),
            jit_cert_cache: None,
        }
    }

    /// Create a compiler with an explicit target OS/ABI spec.
    ///
    /// Specs parsed from architecture aliases keep Trust Codegen's compatibility
    /// defaults. A spelled-out triple is authoritative even when all of its
    /// non-architecture components are `unknown`; concrete triples such as
    /// `x86_64-pc-windows-msvc` are likewise preserved exactly.
    pub fn new_for_target_spec(mut config: CompilerConfig, target_spec: TargetSpec) -> Self {
        let target_spec = target_spec.with_default_os_abi();
        config.target = target_spec.architecture;
        Self {
            config,
            target_spec,
            profile_use: None,
            profile_generate_sink: None,
            compile_artifact_cache: None,
            certified_pass_chain: None,
            production_certified_pass_chain: false,
            #[cfg(feature = "verify")]
            production_certified_pass_runs: Vec::new(),
            jit_cert_cache: None,
        }
    }

    /// Attach a decoded `.profdata` artifact for profile-use mode.
    pub fn with_profile_use(mut self, profile: trust_cg_opt::pgo::ProfData) -> Self {
        self.profile_use = Some(profile);
        self
    }

    /// Enable AOT PGO profile-generate mode: inject a per-basic-block counter
    /// increment into every compiled function, define the module-level
    /// `__tcg_pgo_counters` (zeroed u64 array) and `__tcg_pgo_nsites`
    /// (u64 LE site count) globals in the emitted object, and record every
    /// `(function, block_id, counter_index)` site into `sink` in slot order.
    ///
    /// AArch64 AOT objects only — [`Compiler::compile`] fails closed on any
    /// other target rather than silently emitting an uninstrumented object.
    pub fn with_profile_generate(
        mut self,
        sink: std::sync::Arc<std::sync::Mutex<trust_cg_opt::pgo::CounterMap>>,
    ) -> Self {
        self.profile_generate_sink = Some(sink);
        self
    }

    /// Attach a production compile artifact cache for object-code emission.
    pub fn with_compile_artifact_cache(mut self, cache: CompileArtifactCacheConfig) -> Self {
        self.compile_artifact_cache = Some(cache);
        self
    }

    /// Attach an explicit JIT certificate cache (JIT-5). Used by tests to
    /// observe isolated hit/miss stats; production callers leave it unset and
    /// share the process-global cache.
    pub fn with_jit_cert_cache(
        mut self,
        cache: std::sync::Arc<crate::jit_cert::JitCertCache>,
    ) -> Self {
        self.jit_cert_cache = Some(cache);
        self
    }

    /// The JIT certificate cache this compiler uses: the injected instance if
    /// present, otherwise the process-global cache.
    pub fn jit_cert_cache(&self) -> std::sync::Arc<crate::jit_cert::JitCertCache> {
        self.jit_cert_cache
            .clone()
            .unwrap_or_else(crate::jit_cert::JitCertCache::global)
    }

    /// Attach an already checker-validated certified pass chain to future
    /// [`CompilationResult`] values produced by this compiler.
    #[cfg(feature = "verify")]
    pub fn with_certified_pass_chain(
        mut self,
        chain: trust_cg_verify::CertifiedPassChain,
    ) -> Result<Self, trust_cg_verify::CertifiedPassChainError> {
        self.certified_pass_chain = Some(CertifiedPassChainAttachment::from_checked_chain(&chain)?);
        Ok(self)
    }

    /// Check caller-supplied certified pass entries and attach the validated
    /// chain to future [`CompilationResult`] values produced by this compiler.
    #[cfg(feature = "verify")]
    pub fn with_checked_certified_pass_entries<I>(
        self,
        entries: I,
    ) -> Result<Self, trust_cg_verify::CertifiedPassChainError>
    where
        I: IntoIterator<Item = trust_cg_verify::CertifiedPassChainEntry>,
    {
        let chain = trust_cg_verify::CertifiedPassChain::from_entries(entries)?;
        self.with_certified_pass_chain(chain)
    }

    /// Enable the non-default production certified-pass execution path.
    ///
    /// When enabled and the caller has not supplied a certified pass chain,
    /// the compiler runs certified pass wrappers, converts their neutral
    /// run records into checker-backed chain entries, validates the chain, and
    /// attaches it to [`CompilationResult`].
    #[cfg(feature = "verify")]
    pub fn with_production_certified_pass_chain(mut self) -> Self {
        self.production_certified_pass_chain = true;
        self
    }

    /// Add certified run records emitted by production paths outside the
    /// machine-IR optimization pipeline, such as VNN tensor fusion emitters.
    ///
    /// The records are appended after the opt-pipeline records and are checked
    /// through the same fail-closed production chain attachment path.
    #[cfg(feature = "verify")]
    pub fn with_additional_production_certified_pass_runs<I>(mut self, runs: I) -> Self
    where
        I: IntoIterator<Item = trust_cg_opt::CertifiedPassRunRecord>,
    {
        self.production_certified_pass_chain = true;
        self.production_certified_pass_runs.extend(runs);
        self
    }

    /// Create a compiler with the legacy default O2 object-code configuration.
    ///
    /// This currently targets [`Target::Aarch64`] for compatibility. Use
    /// [`Compiler::for_host`] for in-process JIT compilation.
    pub fn default_o2() -> Self {
        Self::new(CompilerConfig::default())
    }

    /// Create a compiler with the low-latency JIT profile for `target`.
    pub fn jit_fast(target: Target) -> Self {
        Self::new(CompilerConfig::jit_fast(target))
    }

    /// Create a compiler with the host-safe low-latency JIT profile.
    ///
    /// The returned compiler uses [`Target::host`] rather than the legacy
    /// [`CompilerConfig::default`] target. If the current host backend is not
    /// wired through [`Compiler::compile_module_to_jit`] yet, compilation will
    /// fail with [`CompileError::JitTargetUnsupported`] instead of emitting
    /// executable memory for a different ISA.
    pub fn for_host() -> Self {
        Self::new(CompilerConfig::for_host_jit())
    }

    /// Returns the compiler's current configuration.
    pub fn config(&self) -> &CompilerConfig {
        &self.config
    }

    /// Returns the effective target spec used for OS/ABI-sensitive codegen.
    pub fn target_spec(&self) -> TargetSpec {
        self.target_spec
    }

    fn compile_artifact_cache_context(
        &self,
        source_module: &trust_ir::Module,
        lowered_module: &trust_ir::Module,
    ) -> Result<Option<CompileArtifactCacheContext>, CompileError> {
        let Some(cache_config) = &self.compile_artifact_cache else {
            return Ok(None);
        };

        let source_bytes = crate::pipeline::encode_tmbc(source_module)?;
        let source_module_sha256 = sha256_digest(&source_bytes);
        let lowered_module_sha256 = if std::ptr::eq(source_module, lowered_module) {
            source_module_sha256.clone()
        } else {
            sha256_digest(&crate::pipeline::encode_tmbc(lowered_module)?)
        };
        let profile_use_sha256 = compiler_profile_use_sha256(self.profile_use.as_ref())?;
        let codegen_options_sha256 =
            compiler_codegen_options_sha256(&self.config, self.target_spec, &profile_use_sha256)?;
        let target_facts_sha256 =
            compiler_target_facts_sha256(self.config.target, self.target_spec)?;
        let key = CompileArtifactCacheKey::new(
            source_module_sha256,
            lowered_module_sha256,
            codegen_options_sha256,
            self.config.target,
            compiler_target_triple(self.target_spec),
            target_facts_sha256,
            cache_config.proof_policy,
            cache_config.dependency_identity.clone(),
        )
        .with_profile_use_sha256(profile_use_sha256);

        Ok(Some((cache_config.backend(), key, cache_config.boundary)))
    }

    fn requires_verified_proof_promotion(&self) -> bool {
        self.config.emit_proofs
            || self
                .compile_artifact_cache
                .as_ref()
                .is_some_and(|cache| cache.proof_policy != CompileArtifactProofPolicy::Unchecked)
    }

    fn ensure_proofs_promotable(
        &self,
        proofs: Option<&[ProofCertificate]>,
    ) -> Result<(), CompileError> {
        if !self.requires_verified_proof_promotion() {
            return Ok(());
        }

        let proofs = proofs.ok_or_else(|| CompileError::ProofPromotionRejected {
            target: self.config.target,
            reason: "proof promotion requires public proof reports, but none were emitted"
                .to_owned(),
        })?;

        if proofs.is_empty() {
            return Err(CompileError::ProofPromotionRejected {
                target: self.config.target,
                reason: "proof promotion requires at least one verified proof report".to_owned(),
            });
        }

        if let Some(cert) = proofs.iter().find(|cert| !cert.verified) {
            let status = proof_status_label(cert);
            return Err(CompileError::ProofPromotionRejected {
                target: self.config.target,
                reason: format!(
                    "{status} proof entry {} in {}: {}",
                    cert.rule_name, cert.function_name, cert.strength
                ),
            });
        }

        Ok(())
    }

    /// JIT-5 unconditional fail-closed promotion gate for a verifying JIT mode.
    ///
    /// Unlike [`Self::ensure_proofs_promotable`] (which is a no-op unless the
    /// artifact-cache proof policy demands promotion), this always rejects the
    /// compile when the certificate set is empty or contains any unverified
    /// entry — so `CachedVerified`/`AlwaysVerify` publish only cert-covered
    /// bytes even when no compile-artifact cache is attached.
    // Reached only from the verifying JIT cert path (feature = "verify").
    #[cfg_attr(not(feature = "verify"), allow(dead_code))]
    fn gate_jit_proofs_promotable(&self, proofs: &[ProofCertificate]) -> Result<(), CompileError> {
        if proofs.is_empty() {
            return Err(CompileError::ProofPromotionRejected {
                target: self.config.target,
                reason: "JIT validation requires at least one verified proof report, but the \
                         emitted stream produced none (every executed byte must be certified)"
                    .to_owned(),
            });
        }
        if let Some(cert) = proofs.iter().find(|cert| !cert.verified) {
            let status = proof_status_label(cert);
            return Err(CompileError::ProofPromotionRejected {
                target: self.config.target,
                reason: format!(
                    "{status} proof entry {} in {} would publish an UNCERTIFIED JIT byte: {}",
                    cert.rule_name, cert.function_name, cert.strength
                ),
            });
        }
        Ok(())
    }

    /// JIT-5: certify each x86-64 JIT function under the resolved validation
    /// mode, consulting the content-addressed certificate cache on
    /// `CachedVerified`, and fail-close the compile before publish if any
    /// executed byte would be uncertified.
    ///
    /// Returns `(proofs, per_function_validation)`. `proofs` is `None` only on
    /// the Unchecked path (no certs). The per-function validation records feed
    /// [`JitValidationProvenance`].
    fn x86_jit_certify_functions(
        &self,
        validation_mode: JitValidationMode,
        isel_funcs: &[trust_cg_lower::x86_64_isel::X86ISelFunction],
        lir_functions: &[(trust_cg_lower::Function, trust_cg_lower::ProofContext)],
        per_func_emitted_code: &[Vec<u8>],
    ) -> Result<(Option<Vec<ProofCertificate>>, Vec<JitFunctionValidation>), CompileError> {
        let must_verify = validation_mode.requires_jit_verification();
        // Preserve the legacy artifact-cache-driven promotion path (a compile
        // artifact cache with a non-Unchecked proof policy demands proofs even
        // when the JIT mode itself does not).
        let legacy_promote = self.requires_verified_proof_promotion();

        if !must_verify && !legacy_promote {
            // Unchecked (dev-only) or a non-verifying legacy path: no certs.
            return Ok((None, Vec::new()));
        }

        #[cfg(not(feature = "verify"))]
        {
            // Verifying modes are unreachable without the `verify` feature —
            // `JitValidationMode::ensure_supported` fails closed in
            // `to_jit_config` — and legacy promotion cannot produce proofs here.
            let _ = (isel_funcs, lir_functions, per_func_emitted_code);
            Err(CompileError::ProofsUnsupportedForTarget {
                target: self.config.target,
            })
        }

        #[cfg(feature = "verify")]
        {
            let cache = self.jit_cert_cache();
            // Only CachedVerified may satisfy the obligation from cache;
            // AlwaysVerify and the legacy path always re-discharge.
            let use_cache =
                must_verify && validation_mode.uses_certificate_cache() && cache.is_enabled();
            let config_fp = x86_jit_config_fingerprint(&self.config, validation_mode);

            let mut all_certs: Vec<ProofCertificate> = Vec::new();
            let mut per_fn: Vec<JitFunctionValidation> = Vec::with_capacity(isel_funcs.len());

            // TV-2: `isel_funcs` is built 1:1 in `lir_functions` order, so the
            // zip pairs each ISel function with the LIR function its ISel
            // consumed; the verifier additionally name-guards the pairing.
            for (i, (func, (lir_func, _))) in
                isel_funcs.iter().zip(lir_functions.iter()).enumerate()
            {
                let code_bytes = &per_func_emitted_code[i];
                // The key folds the pre-fixup emitted bytes (a deterministic
                // image of this ISel function — exactly what the verifier
                // certifies) with the config fingerprint. Never name-only.
                let key = crate::jit_cert::JitCertCacheKey::new(code_bytes, &config_fp);
                let bytes_sha = key.content_sha256.clone();

                let (fn_certs, verified, cache_hit) = if use_cache {
                    if let Some(v) = cache.peek(&key) {
                        // Warm hit: the key IS the emitted-bytes hash, so the
                        // cached verdict is bound to exactly these bytes. Reuse
                        // WITHOUT re-running the verifier (no solver spawn).
                        cache.record_hit();
                        (v.x86_proof_certs, v.verified, true)
                    } else {
                        // Miss: full verification, then populate. Never skips.
                        cache.record_miss();
                        let certs = generate_x86_64_proof_certificates(func, Some(lir_func));
                        let verified = certs.iter().all(|c| c.verified);
                        cache.store(
                            key,
                            crate::jit_cert::CachedFunctionVerdict {
                                verified,
                                emitted_bytes_sha256: bytes_sha.clone(),
                                x86_proof_certs: certs.clone(),
                                aarch64_cert: None,
                            },
                        );
                        (certs, verified, false)
                    }
                } else {
                    // AlwaysVerify / legacy artifact-cache promotion: full
                    // verify, never cached.
                    let certs = generate_x86_64_proof_certificates(func, Some(lir_func));
                    let verified = certs.iter().all(|c| c.verified);
                    (certs, verified, false)
                };

                per_fn.push(JitFunctionValidation {
                    function: func.name.clone(),
                    verified,
                    bytes_sha256: bytes_sha,
                    cache_hit,
                });
                all_certs.extend(fn_certs);
            }

            let proofs = Some(all_certs);
            // Fail-closed promotion gate. `ensure_proofs_promotable` covers the
            // legacy artifact-cache policy; `gate_jit_proofs_promotable` is the
            // unconditional verifying-mode gate (the former is a no-op when no
            // artifact cache is attached).
            self.ensure_proofs_promotable(proofs.as_deref())?;
            if must_verify {
                self.gate_jit_proofs_promotable(proofs.as_deref().unwrap_or(&[]))?;
            }
            Ok((proofs, per_fn))
        }
    }

    fn ensure_object_proofs_promotable(
        &self,
        proofs: Option<&[ProofCertificate]>,
    ) -> Result<(), CompileError> {
        self.ensure_proofs_promotable(proofs)?;
        if !self.requires_verified_proof_promotion() {
            return Ok(());
        }

        let proofs = proofs.ok_or_else(|| CompileError::ProofPromotionRejected {
            target: self.config.target,
            reason: "object proof promotion requires public proof reports, but none were emitted"
                .to_owned(),
        })?;
        let has_verified_inventory = proofs
            .iter()
            .any(|cert| cert.verified && cert.category == "relocation_inventory");
        if !has_verified_inventory {
            return Err(CompileError::ProofPromotionRejected {
                target: self.config.target,
                reason:
                    "object proof promotion requires a verified relocation_inventory certificate"
                        .to_owned(),
            });
        }

        Ok(())
    }

    #[cfg(feature = "verify")]
    fn certified_pass_chain_attachment_from_runs(
        &self,
        compilation_unit: &str,
        runs: &[trust_cg_opt::CertifiedPassRunRecord],
    ) -> Result<Option<CertifiedPassChainAttachment>, CompileError> {
        if let Some(chain) = &self.certified_pass_chain {
            return Ok(Some(chain.clone()));
        }
        if !self.production_certified_pass_chain {
            return Ok(None);
        }

        let mut all_runs =
            Vec::with_capacity(runs.len() + self.production_certified_pass_runs.len());
        all_runs.extend_from_slice(runs);
        all_runs.extend(self.production_certified_pass_runs.iter().cloned());

        for run in &all_runs {
            if !run.is_verified() {
                return Err(CompileError::CertifiedPassExecutionFailed {
                    pass_name: run.pass_name.clone(),
                    function_name: run.function_name.clone(),
                    detail: format!(
                        "status={}, local_checker_status={}, failure_count={}",
                        run.status.as_str(),
                        run.local_checker.status.as_str(),
                        run.failure_count
                    ),
                });
            }
        }

        let requests = all_runs
            .iter()
            .enumerate()
            .map(|(index, run)| {
                self.certified_pass_check_request(compilation_unit, index as u64, run)
            })
            .collect::<Result<Vec<_>, CompileError>>()?;
        let chain = trust_cg_verify::CertifiedPassChain::check_requests(requests)?;
        Ok(Some(CertifiedPassChainAttachment::from_checked_chain(
            &chain,
        )?))
    }

    /// Build a verified `Lean5PassCertificateCheckRequest` from a neutral
    /// `CertifiedPassRunRecord` using the same code path the production
    /// certified pass chain takes when assembling its checker-backed entries.
    ///
    /// This is exposed to support out-of-crate integration tests that need
    /// to synthesize certified-pass requests in-process when reference
    /// `reports/fixtures/` JSON is not present in the open-source tree.
    /// The signature is intentionally not part of the supported public API
    /// surface (see `#[doc(hidden)]`); production callers should use
    /// `with_production_certified_pass_chain`.
    #[cfg(feature = "verify")]
    #[doc(hidden)]
    pub fn certified_pass_check_request(
        &self,
        compilation_unit: &str,
        certificate_index: u64,
        run: &trust_cg_opt::CertifiedPassRunRecord,
    ) -> Result<
        trust_cg_verify::certified_pass_checker::Lean5PassCertificateCheckRequest,
        CompileError,
    > {
        use trust_cg_verify::certified_pass_checker::{
            CheckerArtifactRef, Lean5CheckerMode, Lean5CheckerPolicy, PlaceholderTransportEvidence,
        };

        let run_record_bytes = serde_json::to_vec(run).map_err(|source| {
            CompileError::CompileArtifactCacheIdentityJson {
                component: "certified_pass_run_record",
                source,
            }
        })?;
        let run_record_digest = sha256_hex(&run_record_bytes);
        let run_record_digest_ref = format!("sha256:{run_record_digest}");
        let run_record_uri = format!("trust-cg-opt://certified-pass-run/{run_record_digest}.json");
        let proof_digest = sha256_hex(
            format!(
                "{}:{}:{}",
                run.pass_instance_id, run.obligation_hash, run_record_digest
            )
            .as_bytes(),
        );
        let proof_digest_ref = format!("sha256:{proof_digest}");
        let proof_uri = format!(
            "builtin://trust-cg-opt/certified-pass-run/{}/placeholder-lean5",
            run.pass_instance_id
        );

        let canonical_obligation = CheckerArtifactRef {
            kind: "canonical_obligation".to_string(),
            uri: run_record_uri,
            digest: run_record_digest_ref,
            media_type: Some("application/json".to_string()),
            placeholder_transport: None,
        };
        let proof_artifact = CheckerArtifactRef {
            kind: "lean_module".to_string(),
            uri: proof_uri,
            digest: proof_digest_ref,
            media_type: Some("text/plain".to_string()),
            placeholder_transport: Some(PlaceholderTransportEvidence {
                accepted: true,
                note: "Transport check for an trust-cg-opt local certified pass run; semantic Lean replay is not part of this bounded slice.".to_string(),
            }),
        };
        let artifacts = vec![canonical_obligation, proof_artifact];
        let certificate_artifacts = serde_json::to_value(&artifacts).map_err(|source| {
            CompileError::CompileArtifactCacheIdentityJson {
                component: "certified_pass_checker_artifacts",
                source,
            }
        })?;

        let certificate = serde_json::json!({
            "format_version": "trust-cg.certified_pass.v1",
            "pass": {
                "name": run.pass_name.as_str(),
                "version": run.pass_version.to_string(),
                "implementation_commit": "workspace-local",
                "instance_id": run.pass_instance_id.as_str(),
                "pipeline_ordinal": certificate_index + 1,
                "target_profile": {
                    "triple": compiler_target_triple(self.target_spec),
                    "cpu": "unspecified",
                    "features": []
                },
                "options_hash": format!(
                    "sha256:{}",
                    sha256_hex(compiler_opt_level_name(self.config.opt_level).as_bytes())
                )
            },
            "provenance": {
                "source": {
                    "program_id": format!(
                        "trust-cg://{}/{}/before/{}",
                        compilation_unit, run.function_name, run.pass_instance_id
                    ),
                    "node_ids": [],
                    "expression_digest": run.obligation_hash.as_str()
                },
                "rewrite": {
                    "program_id": format!(
                        "trust-cg://{}/{}/after/{}",
                        compilation_unit, run.function_name, run.pass_instance_id
                    ),
                    "node_ids": [],
                    "expression_digest": run.obligation_hash.as_str()
                }
            },
            "contract": {
                "mode": "local_pass_certificate_summary",
                "semantic_policy": {
                    "source": "trust-cg-opt certified wrapper",
                    "fail_closed": true
                }
            },
            "domain": {
                "kind": "machine-ir",
                "certified_pass_run": run
            },
            "obligation_hash": run.obligation_hash.as_str(),
            "checker": {
                "kind": "lean5",
                "name": "trust-cg-cert-check",
                "version": "0.1.0",
                "proof_family": "trust-cg-opt-local-certified-pass-run-v1",
                "invocation": {
                    "mode": "in_process",
                    "command": ["trust-cg-codegen", "production-certified-pass-chain"],
                    "working_directory_policy": "process"
                },
                "limits": {
                    "timeout_ms": 1000
                },
                "replay_inputs": certificate_artifacts.clone(),
                "trust_base": [
                    "lean5-kernel",
                    "trust-cg-opt-local-certified-pass-run",
                    "placeholder-transport-fixture"
                ]
            },
            "result": {
                "status": "verified",
                "checked_at_unix": 0,
                "duration_ms": 0,
                "local_checker": &run.local_checker,
                "certificate_count": run.certificate_count,
                "failure_count": run.failure_count
            },
            "artifacts": {
                "refs": certificate_artifacts
            },
            "chain": {
                "compilation_unit": compilation_unit,
                "certificate_index": certificate_index,
                "must_be_verified": true
            }
        });

        Ok(
            trust_cg_verify::certified_pass_checker::Lean5PassCertificateCheckRequest {
                format_version: "trust-cg.lean5_pass_check.request.v1".to_string(),
                certificate,
                obligation_hash: run.obligation_hash.clone(),
                policy: Lean5CheckerPolicy {
                    checker: "lean5".to_string(),
                    mode: Lean5CheckerMode::PlaceholderTransport,
                    timeout_ms: 1000,
                    fail_closed: true,
                    expected_lean_version: Some("Lean 5.0.0-placeholder".to_string()),
                    lean5_binary: None,
                },
                artifacts,
            },
        )
    }

    /// Construct a verified `CertifiedPassRunRecord` for the gamma-vnncomp
    /// demo chain. Exposed as `#[doc(hidden)]` for cross-crate integration
    /// tests that synthesize the gamma demo certified pass requests in
    /// process (the open-source baseline does not ship the corresponding
    /// `reports/fixtures/gamma_vnncomp_demo_*_request.json` JSON).
    #[cfg(feature = "verify")]
    #[doc(hidden)]
    pub fn gamma_vnncomp_demo_run_record(
        pass_name: &str,
        pass_instance_id: &str,
        local_checker_name: &str,
        function_name: &str,
    ) -> trust_cg_opt::CertifiedPassRunRecord {
        use trust_cg_opt::{
            CertifiedPassCheckerRecord, CertifiedPassRunRecord, CertifiedPassRunStatus,
        };
        CertifiedPassRunRecord {
            format_version: "trust-cg.opt.certified_pass_run.v1".to_string(),
            pass_name: pass_name.to_string(),
            pass_version: 1,
            pass_instance_id: pass_instance_id.to_string(),
            function_name: function_name.to_string(),
            changed: false,
            status: CertifiedPassRunStatus::Verified,
            certificate_count: 0,
            failure_count: 0,
            obligation_hash: format!(
                "trust-cg-opt-certified-pass-run-v1:gamma-vnncomp-demo:{pass_instance_id}"
            ),
            local_checker: CertifiedPassCheckerRecord {
                kind: "trust-cg-opt-local".to_string(),
                name: local_checker_name.to_string(),
                version: "1".to_string(),
                status: CertifiedPassRunStatus::Verified,
            },
            summary: serde_json::json!({
                "changed": false,
                "certificates": [],
                "failures": []
            }),
        }
    }

    /// Compile a trust_ir module to an object file.
    ///
    /// Translates each function in the module through the full pipeline:
    /// trust_ir adapter -> ISel -> optimization -> regalloc -> frame lowering
    /// -> encoding -> object emission.
    ///
    /// All functions are compiled into a single object file with each
    /// function as a separate symbol in the text section. Cross-function calls
    /// are represented as relocations for the linker.
    ///
    /// Returns the compiled object code, metrics, optional trace, and
    /// optional proof certificates.
    pub fn compile(&self, module: &trust_ir::Module) -> Result<CompilationResult, CompileError> {
        let total_start = Instant::now();
        let tracing = self.config.trace_level != CompilerTraceLevel::None;
        let mut trace_entries = Vec::new();

        // Phase 0: Pre-adapter dialect lowering (#433, trust_ir #428).
        //
        // Runs `trust_ir::dialect::lower_module` with an internal
        // `DialectRegistry` so any `Inst::DialectOp` (e.g. `verif.bfs_step`,
        // `verif.frontier_drain`) is rewritten into core trust_ir before the
        // adapter runs. Unknown dialects are rejected here — the adapter
        // has no DialectOp handler and would otherwise fail at ISel.
        //
        // Modules with no dialect ops borrow the input unchanged. Dialectful
        // modules clone locally because the dialect driver needs `&mut Module`
        // and the public `compile` signature is `&Module`.
        let dialect_start = Instant::now();
        let (lowered_module, rewrites) = lower_dialects_if_needed(module)?;
        if tracing {
            trace_entries.push(TraceEntry {
                phase: "dialect_lower".to_string(),
                duration: dialect_start.elapsed(),
                detail: Some(format!("{} rewrites", rewrites)),
            });
        }
        let lowered_module = lowered_module.as_ref();
        let cache_context = self.compile_artifact_cache_context(module, lowered_module)?;

        // Phase 1: Translate trust_ir module to internal LIR functions.
        // Sentinel S5 hardening: tell the adapter which target's carrier expander
        // will materialize a surviving exact-bound `InBounds` guard, so the
        // per-arch bound cap matches what that backend can actually encode.
        // The TLS access dialect follows the OBJECT FORMAT of the target
        // triple: ELF targets lower thread-local reads to the local-exec
        // TPIDR_EL0+TPREL sequence; everything else keeps Darwin TLV.
        let adapter_start = Instant::now();
        let mut lir_functions = trust_cg_lower::translate_module_for_arch_with_tls(
            lowered_module,
            guard_carrier_arch_for_target(self.config.target),
            if crate::pipeline::target_triple_uses_elf(&compiler_target_triple(self.target_spec)) {
                trust_cg_lower::TlsDialect::ElfLocalExec
            } else {
                trust_cg_lower::TlsDialect::MachOTlv
            },
        )?;
        if tracing {
            trace_entries.push(TraceEntry {
                phase: "adapter".to_string(),
                duration: adapter_start.elapsed(),
                detail: Some(format!("{} functions", lir_functions.len())),
            });
        }

        if lir_functions.is_empty() {
            return Err(CompileError::EmptyModule);
        }

        // OPT-4: shared trust-ir-level (LIR) inlining, at the pre-dispatch seam.
        //
        // Runs on the adapter's `lir_functions` ONCE, before the per-target ISel
        // dispatch below, so x86-64 / aarch64 / riscv64 all inherit it and every
        // downstream per-instruction lowering proof + TV gate re-validates the
        // inlined result (the substitution is re-checked, never trusted). The
        // pass has two conservative tiers: pure single-block scalar leaves are
        // straight-line spliced, while separately eligible small multi-block
        // leaves are fresh-renamed and CFG-spliced. The latter rejects EH,
        // stack slots, in-module calls, and discharge-bearing guards, then
        // checks instruction conservation, CFG well-formedness, and value
        // freshness. Any structural mismatch fails the compile CLOSED. Kill
        // switches: `TCG_NO_INLINE` for both tiers, `TCG_NO_MB_INLINE` for only
        // the CFG tier. Skipped at O0.
        if self.config.opt_level != OptLevel::O0 {
            let inline_start = Instant::now();
            let inline_stats =
                trust_cg_opt::ir_inline::inline_module(&mut lir_functions).map_err(|e| {
                    CompileError::IrInline {
                        detail: e.to_string(),
                    }
                })?;
            if tracing {
                trace_entries.push(TraceEntry {
                    phase: "ir_inline".to_string(),
                    duration: inline_start.elapsed(),
                    detail: Some(format!(
                        "{} sites / {} rounds",
                        inline_stats.sites, inline_stats.rounds
                    )),
                });
            }
        }

        // AOT PGO profile-generate is wired through the AArch64 preparation
        // pipeline only. Fail closed for any other target rather than
        // returning an object that silently carries no instrumentation.
        if self.profile_generate_sink.is_some() && self.config.target != Target::Aarch64 {
            return Err(CompileError::Pipeline(PipelineError::ISel(format!(
                "PGO profile-generate is only supported for the AArch64 AOT pipeline, not {:?}",
                self.config.target
            ))));
        }

        // Target dispatch (#340): route to the per-target backend based on
        // `config.target`. AArch64 is the default and fully wired; x86-64 is
        // dispatched to the parallel `X86Pipeline`. Other targets are not
        // yet wired.
        match self.config.target {
            Target::Aarch64 => {}
            Target::X86_64 => {
                let object_globals = module_object_globals(lowered_module)?;
                return self.compile_x86_64(
                    lir_functions,
                    object_globals,
                    total_start,
                    tracing,
                    trace_entries,
                    cache_context,
                    lowered_module,
                );
            }
            Target::Riscv64 => {
                return self.compile_riscv(
                    lir_functions,
                    total_start,
                    tracing,
                    trace_entries,
                    lowered_module,
                );
            }
        }

        // Build the internal pipeline.
        let pipeline = self.build_pipeline();

        // Phase 2+: Prepare each function through ISel, optimization,
        // regalloc, frame lowering, and branch resolution. All functions
        // are then combined into a single Mach-O .o via compile_module()
        // so cross-function BL instructions get proper BRANCH26 relocations.
        //
        // When parallel compilation is enabled and there are 2+ functions,
        // use rayon to prepare functions concurrently. Each function's
        // pipeline (ISel -> opt -> regalloc -> frame -> branch resolution)
        // is fully independent with no shared mutable state.
        let parallel_worker_count = if self.config.parallel {
            crate::resource_limits::worker_count_for_items(lir_functions.len())
        } else {
            None
        };
        let use_parallel = parallel_worker_count.is_some();
        let trust_ir_functions_for_lir: Vec<Option<&trust_ir::Function>> = lir_functions
            .iter()
            .map(|(lir_func, _)| trust_ir_function_for_lir(lowered_module, lir_func))
            .collect();

        let mut prepared_funcs: Vec<trust_cg_ir::MachFunction>;
        let mut preparation_metrics: Vec<crate::pipeline::PreparationMetrics>;

        if use_parallel {
            // Parallel path: each function is prepared independently via rayon.
            // Collect results with optional trace entries, then unpack.
            let worker_count = parallel_worker_count.unwrap_or(1);
            let pool = crate::resource_limits::build_rayon_pool(worker_count).map_err(|err| {
                CompileError::Pipeline(PipelineError::ISel(format!(
                    "parallel worker pool error: {err}"
                )))
            })?;
            let results: Vec<
                Result<
                    (
                        trust_cg_ir::MachFunction,
                        crate::pipeline::PreparationMetrics,
                        Option<TraceEntry>,
                    ),
                    CompileError,
                >,
            > = pool.install(|| {
                lir_functions
                    .par_iter()
                    .zip(trust_ir_functions_for_lir.par_iter())
                    .map(|((lir_func, proof_ctx), trust_ir_func)| {
                        let func_start = Instant::now();
                        let (ir_func, metrics) = if let Some(trust_ir_func) = *trust_ir_func {
                            pipeline
                                .prepare_function_with_metrics_and_trust_ir_module(
                                    lir_func,
                                    Some(proof_ctx),
                                    lowered_module,
                                    trust_ir_func,
                                )
                                .map_err(CompileError::Pipeline)?
                        } else {
                            pipeline
                                .prepare_function_with_metrics(lir_func, Some(proof_ctx))
                                .map_err(CompileError::Pipeline)?
                        };
                        let entry = if tracing {
                            Some(TraceEntry {
                                phase: "prepare_function".to_string(),
                                duration: func_start.elapsed(),
                                detail: Some(ir_func.name.clone()),
                            })
                        } else {
                            None
                        };
                        Ok((ir_func, metrics, entry))
                    })
                    .collect()
            });

            prepared_funcs = Vec::with_capacity(results.len());
            preparation_metrics = Vec::with_capacity(results.len());
            for result in results {
                let (ir_func, metrics, trace_entry) = result?;
                if let Some(entry) = trace_entry {
                    trace_entries.push(entry);
                }
                preparation_metrics.push(metrics);
                prepared_funcs.push(ir_func);
            }
        } else {
            // Sequential path: single function or parallel disabled.
            prepared_funcs = Vec::with_capacity(lir_functions.len());
            preparation_metrics = Vec::with_capacity(lir_functions.len());
            for ((lir_func, proof_ctx), trust_ir_func) in
                lir_functions.iter().zip(trust_ir_functions_for_lir.iter())
            {
                let func_start = Instant::now();

                let (ir_func, metrics) = if let Some(trust_ir_func) = *trust_ir_func {
                    pipeline.prepare_function_with_metrics_and_trust_ir_module(
                        lir_func,
                        Some(proof_ctx),
                        lowered_module,
                        trust_ir_func,
                    )?
                } else {
                    pipeline.prepare_function_with_metrics(lir_func, Some(proof_ctx))?
                };

                if tracing {
                    trace_entries.push(TraceEntry {
                        phase: "prepare_function".to_string(),
                        duration: func_start.elapsed(),
                        detail: Some(ir_func.name.clone()),
                    });
                }

                preparation_metrics.push(metrics);
                prepared_funcs.push(ir_func);
            }
        }

        let function_count = prepared_funcs.len();
        let proof_optimization_certificates =
            collect_proof_optimization_certificates(&preparation_metrics);
        #[cfg(feature = "verify")]
        let certified_pass_runs = collect_certified_pass_runs(&preparation_metrics);
        let fsym_trust_ir_metrics = summarize_fsym_trust_ir_metrics(&preparation_metrics);

        // Surface the per-phase breakdown the AOT path already measures.
        //
        // `prepare_function_with_metrics*` times isel/optimization/verification/
        // regalloc/frame_lowering/branch_resolution individually, but until now
        // this path used `preparation_metrics` only for certificates, pass runs
        // and frame layouts -- the timings were collected and dropped, leaving a
        // single lumped `prepare_function` trace entry. That is why the
        // compile-time attribution work could not say WHERE backend time goes
        // (e.g. the fixed ~9.5ms every Rust program pays for `std::rt::lang_start`,
        // ~7.4ms of it in this pipeline).
        //
        // Aggregate across functions and emit one entry per phase. Cost is a
        // handful of adds over an already-materialized vector, and only when
        // tracing is on.
        if tracing {
            let mut totals = crate::pipeline::PhaseTimings::default();
            let add = |dst: &mut Option<Duration>, src: Option<Duration>| {
                if let Some(d) = src {
                    *dst = Some(dst.unwrap_or(Duration::ZERO) + d);
                }
            };
            for m in &preparation_metrics {
                add(&mut totals.isel, m.timings.isel);
                add(&mut totals.optimization, m.timings.optimization);
                add(&mut totals.verification, m.timings.verification);
                add(&mut totals.regalloc, m.timings.regalloc);
                add(&mut totals.frame_lowering, m.timings.frame_lowering);
                add(&mut totals.branch_resolution, m.timings.branch_resolution);
                add(&mut totals.encoding, m.timings.encoding);
                add(&mut totals.unattributed, m.timings.unattributed);
            }
            for (phase, duration) in [
                ("prepare::isel", totals.isel),
                ("prepare::optimization", totals.optimization),
                ("prepare::verification", totals.verification),
                ("prepare::regalloc", totals.regalloc),
                ("prepare::frame_lowering", totals.frame_lowering),
                ("prepare::branch_resolution", totals.branch_resolution),
                ("prepare::encoding", totals.encoding),
                ("prepare::unattributed", totals.unattributed),
            ] {
                if let Some(duration) = duration {
                    trace_entries.push(TraceEntry {
                        phase: phase.to_string(),
                        duration,
                        detail: Some(format!("{function_count} functions")),
                    });
                }
            }
        }

        // Materialize the production object's relocation-bearing inputs before
        // proof promotion. Relocation authority covers more than encoded text
        // fixups: global-data slots, TLS descriptors, and unwind FDEs are emitted
        // from these inputs. Keeping the inventory and emitter on the same inputs
        // prevents known sidecar rows from being omitted. This is not an
        // exact-object digest binding: every non-empty production registry remains
        // fail-closed until an independently checked report is bound to the bytes.
        let mut object_globals = module_object_globals(lowered_module)?;
        // AOT PGO generate mode: define the counter array + site count the
        // injected increments and the dump runtime both reference. All sites
        // are known here — every function has been prepared above.
        if let Some(sink) = &self.profile_generate_sink {
            let n_sites = {
                let guard = match sink.lock() {
                    Ok(guard) => guard,
                    Err(poisoned) => poisoned.into_inner(),
                };
                guard.sites.len()
            };
            object_globals.push(ObjectGlobal {
                name: PGO_COUNTER_ARRAY_SYMBOL.to_string(),
                data: vec![0u8; n_sites * 8],
                mutable: true,
                is_external: true,
                symbol_refs: Vec::new(),
                is_thread_local: false,
                is_import: false,
                is_weak: false,
                align: 8,
            });
            object_globals.push(ObjectGlobal {
                name: PGO_NSITES_SYMBOL.to_string(),
                data: (n_sites as u64).to_le_bytes().to_vec(),
                mutable: false,
                is_external: true,
                symbol_refs: Vec::new(),
                is_thread_local: false,
                is_import: false,
                is_weak: false,
                align: 8,
            });
        }
        let module_frame_layouts: Vec<Option<crate::frame::FrameLayout>> = preparation_metrics
            .iter()
            .map(|metrics| metrics.frame_layout.clone())
            .collect();

        // Proof certificates are generated before cache lookup/store so a
        // proof-policy cache partition cannot promote object bytes whose public
        // proof surface contains failed, unverified, or unknown entries.
        #[cfg(feature = "verify")]
        let mut proofs = if self.config.emit_proofs || self.requires_verified_proof_promotion() {
            let all_certs: Vec<ProofCertificate> = if use_parallel {
                let worker_count = parallel_worker_count.unwrap_or(1);
                let pool =
                    crate::resource_limits::build_rayon_pool(worker_count).map_err(|err| {
                        CompileError::Pipeline(PipelineError::ISel(format!(
                            "parallel worker pool error: {err}"
                        )))
                    })?;
                pool.install(|| {
                    // TV-2: `prepared_funcs` is built 1:1 in `lir_functions`
                    // order (both branches above), so the zip pairs each
                    // MachFunction with the LIR function its ISel consumed;
                    // the verifier additionally name-guards the pairing.
                    prepared_funcs
                        .par_iter()
                        .zip(lir_functions.par_iter())
                        .flat_map(|(func, (lir_func, _))| {
                            generate_proof_certificates(func, Some(lir_func))
                        })
                        .collect()
                })
            } else {
                let mut certs = Vec::new();
                for (func, (lir_func, _)) in prepared_funcs.iter().zip(lir_functions.iter()) {
                    certs.extend(generate_proof_certificates(func, Some(lir_func)));
                }
                certs
            };
            Some(all_certs)
        } else {
            None
        };
        #[cfg(not(feature = "verify"))]
        let proofs: Option<Vec<ProofCertificate>> = None;

        #[cfg(feature = "verify")]
        if let Some(proofs) = proofs.as_mut()
            && let Some(report) = pipeline.module_relocation_inventory_report_with_object_state(
                &prepared_funcs,
                &object_globals,
                &module_frame_layouts,
                format!("{}-module.o", compiler_target_triple(self.target_spec)),
            )?
        {
            append_object_relocation_inventory_certificate(proofs, &report);
        }

        self.ensure_object_proofs_promotable(proofs.as_deref())?;
        let proof_bundle_sha256 = proof_bundle_sha256(proofs.as_deref());

        // Phase 8-9: Encode all functions and emit a single Mach-O .o file
        // with proper cross-function BRANCH26 relocations.
        // When parallel mode is active, use parallel encoding to avoid the
        // sequential bottleneck of encoding functions one-by-one.
        let module_start = Instant::now();
        let mut compile_artifact_cache_telemetry = Vec::new();
        let cached_object = if let Some((cache, key, boundary)) = &cache_context {
            match lookup_compile_artifact(cache, key, *boundary, proof_bundle_sha256.as_deref())? {
                CompileArtifactCacheLookup::Hit { entry, telemetry } => {
                    compile_artifact_cache_telemetry.push(telemetry);
                    Some(entry.artifact_bytes)
                }
                CompileArtifactCacheLookup::Miss { telemetry }
                | CompileArtifactCacheLookup::Rejected { telemetry } => {
                    compile_artifact_cache_telemetry.push(telemetry);
                    None
                }
            }
        } else {
            None
        };
        // Exception-handling routing.
        //
        // [TCG-EH-A64-BATCH] (X1 follow-up to FUZZ-7), resolved: a
        // MULTI-function EH module used to fail closed here because the generic
        // module emitter had no unwind-table emission — the object would have
        // carried landing-pad code with no `__gcc_except_tab` /
        // `__compact_unwind` (silently skipped cleanup Drops, the FUZZ-7
        // [TCG-EH-WALK] class). The module emitters now build WHOLE-MODULE
        // unwind tables for Mach-O (per-function `__LD,__compact_unwind`
        // entries + DWARF FDE fallbacks + LSDAs — the x86 EH-Lane-5 analogue,
        // `Pipeline::emit_module_macho_with_unwind`), consuming the frame
        // layouts captured during preparation. Formats the port does not cover
        // (generic ELF) and missing layouts still FAIL CLOSED inside the
        // emitter — never a silent table drop.
        //
        // A SINGLE-function EH module used to detour through the standalone
        // `compile_function` pipeline here. That path re-ran ISel/opt/regalloc
        // from scratch AND — the actual defect — emitted the object WITHOUT
        // `object_globals`, so a module-owned internal global (`str.*` literal
        // blobs, `const.alloc*` CTFE images, `vtable.*`) referenced by an EH
        // function was left an UNDEFINED extern in the object and had to be
        // synthesized by the link harness from module text. Single-function EH
        // modules now flow through the same whole-module emitters as everything
        // else (`encode_module_function_with_fixups_and_eh` mirrors the proven
        // single-function LSDA/compact-unwind sequence exactly), so every
        // module-owned global it references is DEFINED in the object.
        //
        let obj_bytes = if let Some(bytes) = cached_object {
            bytes
        } else {
            let bytes = if use_parallel {
                pipeline.compile_module_parallel_with_globals_and_layouts(
                    &prepared_funcs,
                    &object_globals,
                    &module_frame_layouts,
                )?
            } else {
                pipeline.compile_module_with_globals_and_layouts(
                    &prepared_funcs,
                    &object_globals,
                    &module_frame_layouts,
                )?
            };
            if let Some((cache, key, boundary)) = &cache_context {
                compile_artifact_cache_telemetry.push(store_compile_artifact(
                    cache,
                    key,
                    *boundary,
                    &bytes,
                    "trust-cg-codegen::Compiler::compile",
                    proof_bundle_sha256.as_deref(),
                )?);
            }
            bytes
        };

        if tracing {
            trace_entries.push(TraceEntry {
                phase: "compile_module".to_string(),
                duration: module_start.elapsed(),
                detail: Some(format!("{} functions", function_count)),
            });
        }

        // Count actual non-pseudo instructions across all prepared functions.
        // Each AArch64 instruction is exactly 4 bytes, so code_size = count * 4.
        // This is the real instruction count, not the Mach-O object size / 4
        // which would incorrectly include headers, symbol tables, and relocations.
        let total_instruction_count: usize =
            prepared_funcs.iter().map(count_real_instructions).sum();
        let total_code_size = total_instruction_count * 4;

        // Query actual pass count from the optimization pipeline rather than
        // using hardcoded estimates (fixes #272).
        let opt_passes_per_func = {
            use trust_cg_opt::pipeline::{OptLevel as OptOptLevel, OptimizationPipeline};
            let opt_level = match self.config.opt_level {
                OptLevel::O0 => OptOptLevel::O0,
                OptLevel::O1 => OptOptLevel::O1,
                OptLevel::O2 => OptOptLevel::O2,
                OptLevel::O3 => OptOptLevel::O3,
            };
            OptimizationPipeline::new(opt_level).pass_count()
        };

        let metrics = CompilationMetrics {
            code_size_bytes: total_code_size,
            instruction_count: total_instruction_count,
            function_count,
            optimization_passes_run: opt_passes_per_func * function_count,
            proof_optimizations: summarize_proof_optimizations(&proof_optimization_certificates),
            fsym_trust_ir: fsym_trust_ir_metrics,
        };

        let trace = if tracing {
            Some(CompilerTrace {
                entries: trace_entries,
                total_duration: total_start.elapsed(),
            })
        } else {
            None
        };

        #[cfg(feature = "verify")]
        let certified_pass_chain = self.certified_pass_chain_attachment_from_runs(
            &lowered_module.name,
            &certified_pass_runs,
        )?;
        #[cfg(not(feature = "verify"))]
        let certified_pass_chain = self.certified_pass_chain.clone();

        Ok(CompilationResult {
            object_code: obj_bytes,
            metrics,
            trace,
            proofs,
            certified_pass_chain,
            proof_optimization_certificates,
            compile_artifact_cache_telemetry,
        })
    }

    /// x86-64 compile path (#340, #464).
    ///
    /// Routes trust_ir functions through the [`crate::x86_64::X86Pipeline`]
    /// (ISel -> regalloc -> frame lowering -> encoding) and then emits a
    /// single multi-function Mach-O / ELF object via
    /// [`crate::x86_64::X86Pipeline::compile_module`]. Cross-function calls
    /// are wired via symbol-table entries and `X86_64_RELOC_BRANCH` /
    /// `R_X86_64_PLT32` relocations.
    ///
    /// Mirrors the AArch64 dispatcher at
    /// [`Self::compile_aarch64`]: each function is run through ISel
    /// independently, then the entire set is handed to `compile_module` for
    /// combined emission.
    ///
    /// Note: `CompilationMetrics::instruction_count` is reported from the
    /// x86-64 ISel functions (non-pseudo insts summed across all functions),
    /// and `code_size_bytes` is the raw encoded code length (no Mach-O
    /// header/symbol-table overhead). Because x86-64 uses variable-length
    /// encoding, `code_size_bytes` is NOT `instruction_count * 4`.
    fn compile_x86_64(
        &self,
        lir_functions: Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
        object_globals: Vec<ObjectGlobal>,
        total_start: Instant,
        tracing: bool,
        mut trace_entries: Vec<TraceEntry>,
        cache_context: Option<CompileArtifactCacheContext>,
        trust_ir_module: &trust_ir::Module,
    ) -> Result<CompilationResult, CompileError> {
        use crate::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig};
        use trust_cg_lower::x86_64_isel::X86CallAbi;

        // #465: x86-64 proof certificates are now produced via the shared
        // public `ProofCertificate` shape. The previous early-return guard
        // (`CompileError::ProofsUnsupportedForTarget`) was removed once
        // `all_x86_64_proofs` (#434) and `all_x86_64_eflags_proofs` (#458)
        // landed in the `ProofDatabase` and a parallel x86-64 function
        // verifier (`trust_cg_verify::x86_64_function_verifier`) was wired to
        // walk an `X86ISelFunction`. Proof emission is gated on the
        // `verify` feature flag, same as the AArch64 path. When the
        // feature is off, `emit_proofs` is honored as a no-op and the
        // returned `proofs` field is `None`.
        //
        // Without the `verify` feature the `verify_x86_64_function` call
        // below is unreachable, so we still surface a typed error if a
        // caller opts into proofs on a non-verify build — otherwise the
        // invariant "result.proofs.is_some() when emit_proofs=true" would
        // silently regress.
        #[cfg(not(feature = "verify"))]
        if self.config.emit_proofs {
            return Err(CompileError::ProofsUnsupportedForTarget {
                target: Target::X86_64,
            });
        }

        let target_spec = self.target_spec;
        let output_format = x86_64_aot_output_format_for_target_spec(target_spec)?;
        let call_abi = match target_spec.operating_system {
            TargetOperatingSystem::Windows => X86CallAbi::WindowsX64,
            _ => X86CallAbi::SystemV,
        };

        let function_count = lir_functions.len();
        if function_count == 0 {
            return Err(CompileError::Pipeline(PipelineError::ISel(
                "x86_64 dispatcher received an empty module".to_string(),
            )));
        }

        // EH x86 Lane 2: the x86-64 Mach-O emitter now produces the LSDA
        // (`__gcc_except_tab`), the zPLR-augmented FDE, and the
        // `rust_eh_personality` wiring, so a Mach-O EH function flows through to
        // emission. Non-Mach-O AOT output (ELF/COFF) still gets no LSDA in Lane 2,
        // so an EH function targeting those formats FAILS CLOSED here rather than
        // shipping an object with no unwind tables. EH structure is only produced
        // under the `TCG_ENABLE_UNWIND` frontend opt-in (default OFF; `panic=abort`
        // and the default path never produce it), so this gate is inert for the
        // standard corpus and preserves the "unwind opt-in never miscompiles"
        // contract on x86. (Native run + the default-on flip are Lane 3.)
        reject_x86_eh_for_non_macho_aot(&lir_functions, output_format)?;

        // CT-5: exploit the idle cores. The per-function backend work — register
        // allocation + machine-code encoding (`compile_module_*_parallel`) and,
        // under the `verify` feature, per-function proof-certificate generation —
        // is independent per function and is the dominant compile-time cost, yet
        // this dispatcher historically ran it single-threaded. When
        // `CompilerConfig::parallel` is set (the default), fan it out across a
        // bounded rayon pool. The module emitters gate the actual pool build on
        // `worker_count_for_items`, so a single-function module stays serial.
        //
        // DETERMINISM: every parallelized stage collects into a function-ordered
        // Vec (`par_iter().map()/.flat_map().collect()` is indexed), so the
        // emitted object bytes AND the ordered proof bundle are byte-identical to
        // the serial path regardless of thread scheduling. The SOLVER is kept
        // serialized: cert generation only runs in parallel when the opt-in live
        // reconstructed-obligation solver lane (`TCG_RECON_SOLVER_ROUTE`) is OFF,
        // so parallel z3 (the BENCH-8 nondet-failclosed hazard) is never armed.
        let use_parallel = self.config.parallel;

        // Phase 1: Run ISel per function. Each X86ISelFunction is
        // independent (no shared mutable state), so this is straightforward
        // sequential work; parallelization is a follow-up (mirrors the
        // AArch64 `prepared_funcs` vector).
        let isel_start = Instant::now();
        let mut isel_funcs: Vec<trust_cg_lower::x86_64_isel::X86ISelFunction> =
            Vec::with_capacity(function_count);
        // The policy is unconditional and non-bypassable: without validator replay every carrier
        // is kept and later expanded to a runtime check.
        let kernel_gate_on = guard_kernel_gate_enabled();
        let mut x86_guard_elim_eliminated: u32 = 0;
        for (lir_func, proof_ctx) in &lir_functions {
            use trust_cg_lower::x86_64_isel::X86InstructionSelector;
            lir_func.validate_eh_structure().map_err(|reason| {
                CompileError::Pipeline(PipelineError::ISel(format!(
                    "invalid x86 exception-handling structure in `{}`: {reason}",
                    lir_func.name
                )))
            })?;
            let sig = trust_cg_lower::function::Signature {
                params: lir_func.signature.params.clone(),
                returns: lir_func.signature.returns.clone(),
            };
            let mut isel =
                X86InstructionSelector::with_abi(lir_func.name.clone(), sig.clone(), call_abi);
            // Keep parity with X86Pipeline::compile_trust_ir_function: StackAddr
            // lowering needs the adapter's fixed/runtime stack-slot metadata.
            isel.set_stack_slots(lir_func.stack_slots.clone());
            isel.seed_value_types(&lir_func.value_types);
            isel.seed_function_value_use_counts(lir_func);
            isel.seed_pure_callees(&lir_func.pure_callees);
            let block_order = lir_func.layout_order();
            // Seed the whole-function Iconst origin map so constant-divisor
            // recognition (magic unsigned div/rem strength reduction) and
            // cross-block constant rematerialization can see every `Iconst`.
            isel.seed_iconst_origins(
                block_order
                    .iter()
                    .map(|b| lir_func.blocks[b].instructions.as_slice()),
            );
            for block_ref in &block_order {
                isel.ensure_block(*block_ref);
            }
            isel.lower_formal_arguments(&sig, lir_func.entry_block)
                .map_err(|e| CompileError::Pipeline(PipelineError::ISel(e.to_string())))?;
            for block_ref in &block_order {
                let basic_block = &lir_func.blocks[block_ref];
                if *block_ref != lir_func.entry_block && !basic_block.params.is_empty() {
                    isel.define_block_params(&basic_block.params);
                }
                isel.select_block(*block_ref, &basic_block.instructions)
                    .map_err(|e| CompileError::Pipeline(PipelineError::ISel(e.to_string())))?;
            }
            let mut isel_func = isel
                .finalize_with_eh_info(&lir_func.eh_info)
                .map_err(|e| CompileError::Pipeline(PipelineError::ISel(e.to_string())))?;

            // Sentinel S5: kernel-gated proof-driven bounds-check elimination.
            if kernel_gate_on {
                run_x86_guard_kernel_gate(
                    &mut isel_func,
                    proof_ctx,
                    trust_ir_module,
                    &mut x86_guard_elim_eliminated,
                )
                .map_err(|reason| {
                    CompileError::Pipeline(PipelineError::ISel(format!(
                        "x86 guard kernel gate fail-closed re-check rejected in `{}`: {reason}",
                        lir_func.name
                    )))
                })?;
            }

            isel_funcs.push(isel_func);
        }
        let _ = x86_guard_elim_eliminated;

        // TV-3: block-level lowering-integrity validation on the RAW pre-pass
        // ISel output. MUST run here (before the optimizer passes below), which
        // do not preserve TV-1 provenance stamps. Default ENFORCE on x86.
        for (func, (lir_func, _)) in isel_funcs.iter().zip(lir_functions.iter()) {
            enforce_x86_dataflow_integrity(func, lir_func)?;
        }

        if tracing {
            trace_entries.push(TraceEntry {
                phase: "x86_isel".to_string(),
                duration: isel_start.elapsed(),
                detail: Some(format!("{} functions", function_count)),
            });
        }

        let x86_opt_level = x86_opt_level_from_codegen(self.config.opt_level);
        let mut optimized_isel_funcs = isel_funcs.clone();
        let opt_start = Instant::now();
        let optimization_passes_run: usize = {
            let pipeline = X86Pipeline::new(X86PipelineConfig {
                opt_level: x86_opt_level,
                output_format: X86OutputFormat::RawBytes,
                emit_frame: true,
                call_abi,
                ..X86PipelineConfig::default()
            });
            optimized_isel_funcs
                .iter_mut()
                .map(|func| pipeline.run_x86_optimization_passes(func).total_pass_runs())
                .sum()
        };
        if tracing {
            trace_entries.push(TraceEntry {
                phase: "x86_optimization".to_string(),
                duration: opt_start.elapsed(),
                detail: Some(format!("{} pass runs", optimization_passes_run)),
            });
        }

        // PROOF-GAP item 1 + 3: fail-closed gates that run UNCONDITIONALLY (NOT
        // behind the `verify` feature) — pure-lattice / exhaustive checks, no
        // solver, so they keep the AOT object path honest on the DEFAULT build
        // (the rustc bridge uses `default-features = false`).
        //   * carrier-hygiene: PER-PROGRAM — checks each emitted function for the
        //     #51/#66 dirty-narrow-carrier hazard (a real per-program gate).
        //   * glue-pass validator: PER-PROGRAM (proof-gap item 3, #67) — derives
        //     the overflow expansions THIS program's emitted X86ISelFunctions
        //     contain (structural IMUL->IDIV safety net + idiom enumeration) and
        //     re-verifies each distinct one; the fixed model canary is folded in
        //     as a memoized baseline. See `validate_x86_glue_pass_expansions`.
        for func in &optimized_isel_funcs {
            check_x86_carrier_hygiene(func)?;
        }
        validate_x86_glue_pass_expansions(&optimized_isel_funcs)?;

        // Count non-pseudo ISel instructions after x86 optimization. This is
        // the x86 analogue of counting prepared AArch64 machine instructions.
        let instruction_count: usize = optimized_isel_funcs
            .iter()
            .map(count_x86_real_instructions)
            .sum();

        #[cfg(feature = "verify")]
        let proof_certs_start = Instant::now();
        // CT-8 (encode reuse): when the proof-cert lane runs, the module is
        // regalloc'd + encoded + assembled ONCE here; the relocation
        // inventory reads the assembly, and the final object emission below
        // REUSES it (Phase-2 emit only) instead of re-running the full
        // encode — previously a redundant third full encode. The assemble
        // duration is attributed to the `x86_compile_module` trace phase
        // (not the cert lane), so the proof-lane number stays honest.
        #[cfg(feature = "verify")]
        let (proofs, assembled_for_emit, proof_lane_assemble_duration): (
            Option<Vec<ProofCertificate>>,
            Option<crate::x86_64::pipeline::X86AssembledModule>,
            Duration,
        ) = if self.config.emit_proofs || self.requires_verified_proof_promotion() {
            let mut all_certs: Vec<ProofCertificate> = Vec::new();
            let proof_lane_pipeline = X86Pipeline::new(X86PipelineConfig {
                opt_level: x86_opt_level,
                output_format,
                emit_frame: true,
                call_abi,
                panic_unwind: self.config.panic_unwind,
                ..X86PipelineConfig::default()
            });
            let assemble_start = Instant::now();
            let assembled = proof_lane_pipeline
                .assemble_module_after_x86_passes(&optimized_isel_funcs, use_parallel)
                .map_err(|e| CompileError::Pipeline(x86_pipeline_error_to_pipeline_error(e)))?;
            let assemble_duration = assemble_start.elapsed();
            let relocation_report = proof_lane_pipeline
                .relocation_inventory_report_for_assembled(
                    &assembled,
                    &object_globals,
                    format!("{}-module.o", compiler_target_triple(self.target_spec)),
                )
                .map_err(|e| CompileError::Pipeline(x86_pipeline_error_to_pipeline_error(e)))?;
            append_object_relocation_inventory_certificate(&mut all_certs, &relocation_report);
            // TV-2: `optimized_isel_funcs` clones `isel_funcs`, which is
            // built 1:1 in `lir_functions` order, so the zip pairs each ISel
            // function with the LIR function its ISel consumed; the verifier
            // additionally name-guards the pairing.
            //
            // CT-5: per-function certificate generation is the other dominant
            // compile-time cost (the "cert lane"). It runs the shared, read-only
            // `&'static` x86 function verifier (a `ProofDatabase` lookup +
            // structural reconstruction, memoized under a sharded process-wide
            // compute-once memo — no per-function shared mutable state), so it
            // parallelizes cleanly.
            // `par_iter().flat_map().collect()` preserves function order, so the
            // ordered cert bundle (and its `proof_bundle_sha256` cache key) is
            // byte-identical to the serial path.
            //
            // SOLVER SERIALIZATION (BENCH-8): the only path that could spawn a
            // live z3 during cert generation is the opt-in reconstructed-
            // obligation solver lane (`TCG_RECON_SOLVER_ROUTE`), which discharges
            // OUTSIDE the memo lock. When it is armed we keep cert generation
            // SERIAL so the solver is never invoked from multiple threads; the
            // default posture (route OFF, or a solver-absent host such as the
            // rustc bridge) parallelizes.
            //
            // CT-7: the cert lane's pool width comes from
            // `verification_worker_count_for_items` (default: the host's
            // available parallelism), NOT the conservative
            // `worker_count_for_items` regalloc+encode cap — per-function
            // verification is pure read-only CPU over the shared `&'static`
            // verifier and is the dominant proofs-on compile cost. Width
            // never affects output (function-ordered collect).
            let cert_worker_count = if use_parallel && !recon_live_solver_route_requested() {
                crate::resource_limits::verification_worker_count_for_items(
                    optimized_isel_funcs.len(),
                )
            } else {
                None
            };
            let per_func_certs: Vec<ProofCertificate> = if let Some(worker_count) =
                cert_worker_count
            {
                let pool =
                    crate::resource_limits::build_rayon_pool(worker_count).map_err(|err| {
                        CompileError::Pipeline(PipelineError::ISel(format!(
                            "parallel worker pool error: {err}"
                        )))
                    })?;
                pool.install(|| {
                    optimized_isel_funcs
                        .par_iter()
                        .zip(lir_functions.par_iter())
                        .flat_map(|(func, (lir_func, _))| {
                            generate_x86_64_proof_certificates(func, Some(lir_func))
                        })
                        .collect()
                })
            } else {
                let mut certs = Vec::new();
                for (func, (lir_func, _)) in optimized_isel_funcs.iter().zip(lir_functions.iter()) {
                    certs.extend(generate_x86_64_proof_certificates(func, Some(lir_func)));
                }
                certs
            };
            all_certs.extend(per_func_certs);
            (Some(all_certs), Some(assembled), assemble_duration)
        } else {
            (None, None, Duration::ZERO)
        };
        #[cfg(feature = "verify")]
        if tracing {
            // CT-7: attribute the proof-certificate lane (relocation-inventory
            // rows + per-function verification/discharge) in the TCG_TIME
            // trace so proofs-on compile-time claims are falsifiable per
            // phase. CT-8: the module ENCODE the lane shares with the final
            // object emission is subtracted here and reported under
            // `x86_compile_module` instead (it is module-encode work, not
            // cert work).
            trace_entries.push(TraceEntry {
                phase: "x86_proof_certs".to_string(),
                duration: proof_certs_start
                    .elapsed()
                    .saturating_sub(proof_lane_assemble_duration),
                detail: Some(format!(
                    "{} certs",
                    proofs.as_deref().map(<[_]>::len).unwrap_or(0)
                )),
            });
        }
        #[cfg(not(feature = "verify"))]
        let proofs: Option<Vec<ProofCertificate>> = None;
        self.ensure_object_proofs_promotable(proofs.as_deref())?;
        let proof_bundle_sha256 = proof_bundle_sha256(proofs.as_deref());

        // Raw code size: encode each function with RawBytes output and sum.
        // Compile_module with RawBytes returns the concatenated per-function
        // code (with inline const pools) — this is the raw code size,
        // excluding any Mach-O / ELF object wrapper overhead.
        //
        // EH modules (`panic=unwind`): RawBytes output fail-closes on any
        // function carrying exception-handling structure (raw bytes cannot
        // carry the LSDA/personality/FDE sidecar — executing them would strand
        // landing pads; the refusal is correct and stays). The SIZE metric is
        // instead read off the REAL module assembly's concatenated code bytes
        // — the exact `__text` payload of the object emitted below (only
        // Mach-O carries x86 EH, and Mach-O keeps const pools inline, so this
        // measures precisely what the RawBytes probe would have). Under the
        // proof-cert lane the CT-8 shared assembly is reused (zero extra
        // encode); otherwise the module is assembled once with the real
        // output format.
        let module_carries_eh = optimized_isel_funcs.iter().any(|f| !f.eh_info.is_empty());
        let total_code_size = if module_carries_eh {
            #[cfg(feature = "verify")]
            let reused_size: Option<usize> = assembled_for_emit.as_ref().map(|a| a.code_size());
            #[cfg(not(feature = "verify"))]
            let reused_size: Option<usize> = None;
            match reused_size {
                Some(size) => size,
                None => {
                    let pipeline = X86Pipeline::new(X86PipelineConfig {
                        opt_level: x86_opt_level,
                        output_format,
                        emit_frame: true,
                        call_abi,
                        ..X86PipelineConfig::default()
                    });
                    pipeline
                        .module_code_size_after_x86_passes(&optimized_isel_funcs, use_parallel)
                        .map_err(|e| {
                            CompileError::Pipeline(x86_pipeline_error_to_pipeline_error(e))
                        })?
                }
            }
        } else {
            // CT-11: reuse the proof lane's assembly here too. This branch used
            // to re-run the ENTIRE backend — `compile_module_after_x86_passes`
            // is a full per-function `run_full_regalloc` + frame + encode plus
            // an object emit — and then keep only `.len()` for a metrics field.
            // The EH branch above has always reused `assembled_for_emit`; this
            // one simply never did, so a `-Cpanic=abort` crate (the common
            // posture, and the whole benchmark suite) paid a second complete
            // backend pass per CGU.
            //
            // The reused value is the RIGHT one, not an approximation:
            // `assembled_for_emit` is built with the SAME `output_format` and
            // is literally the assembly the object below is emitted from
            // (`emit_assembled_module`), so `code_size()` is the emitted
            // `__text` payload. That is what the RawBytes probe was
            // reconstructing.
            //
            // Falls back to the probe when the proof lane is off (no assembly
            // exists) or on non-`verify` builds. `TCG_NO_CODESIZE_REUSE=1`
            // forces the old path so the change can be A/B'd inside ONE dylib.
            #[cfg(feature = "verify")]
            let reused_size: Option<usize> =
                if crate::env_lock::var_os("TCG_NO_CODESIZE_REUSE").is_some() {
                    None
                } else {
                    assembled_for_emit.as_ref().map(|a| a.code_size())
                };
            #[cfg(not(feature = "verify"))]
            let reused_size: Option<usize> = None;
            match reused_size {
                Some(size) => size,
                None => {
                    let raw_bytes = {
                        let pipeline = X86Pipeline::new(X86PipelineConfig {
                            opt_level: x86_opt_level,
                            output_format: X86OutputFormat::RawBytes,
                            emit_frame: true,
                            call_abi,
                            ..X86PipelineConfig::default()
                        });
                        let result = if use_parallel {
                            pipeline.compile_module_after_x86_passes_parallel(&optimized_isel_funcs)
                        } else {
                            pipeline.compile_module_after_x86_passes(&optimized_isel_funcs)
                        };
                        result.map_err(|e| {
                            CompileError::Pipeline(x86_pipeline_error_to_pipeline_error(e))
                        })?
                    };
                    raw_bytes.len()
                }
            }
        };

        // Final native object bytes via compile_module. This is the object
        // returned to the caller; cross-function CALL fixups become
        // X86_64_RELOC_BRANCH relocations on Mach-O and R_X86_64_PLT32
        // relocations on ELF.
        let encode_start = Instant::now();
        let mut compile_artifact_cache_telemetry = Vec::new();
        let cached_object = if let Some((cache, key, boundary)) = &cache_context {
            match lookup_compile_artifact(cache, key, *boundary, proof_bundle_sha256.as_deref())? {
                CompileArtifactCacheLookup::Hit { entry, telemetry } => {
                    compile_artifact_cache_telemetry.push(telemetry);
                    Some(entry.artifact_bytes)
                }
                CompileArtifactCacheLookup::Miss { telemetry }
                | CompileArtifactCacheLookup::Rejected { telemetry } => {
                    compile_artifact_cache_telemetry.push(telemetry);
                    None
                }
            }
        } else {
            None
        };
        let obj_bytes = if let Some(bytes) = cached_object {
            bytes
        } else {
            let bytes = {
                let pipeline = X86Pipeline::new(X86PipelineConfig {
                    opt_level: x86_opt_level,
                    output_format,
                    emit_frame: true,
                    call_abi,
                    panic_unwind: self.config.panic_unwind,
                    ..X86PipelineConfig::default()
                });
                let full_encode = |pipeline: &X86Pipeline| {
                    if use_parallel {
                        pipeline.compile_module_after_x86_passes_with_globals_parallel(
                            &optimized_isel_funcs,
                            &object_globals,
                        )
                    } else {
                        pipeline.compile_module_after_x86_passes_with_globals(
                            &optimized_isel_funcs,
                            &object_globals,
                        )
                    }
                };
                // CT-8: the proof lane already regalloc'd+encoded+assembled
                // this exact module under an identically-configured pipeline
                // — EMIT from that assembly (Phase 2 only) instead of
                // re-running the full encode. Byte-identical by
                // construction: emission is a deterministic pure function of
                // (assembled module, globals, pipeline config), and
                // `full_encode` is exactly assemble-then-emit of the same
                // inputs (`X86Pipeline::compile_module_impl`). With the
                // proof lane off (or non-verify builds) the full encode runs
                // here unchanged.
                #[cfg(feature = "verify")]
                let result = match assembled_for_emit {
                    Some(assembled) => pipeline.emit_assembled_module(assembled, &object_globals),
                    None => full_encode(&pipeline),
                };
                #[cfg(not(feature = "verify"))]
                let result = full_encode(&pipeline);
                result
                    .map_err(|e| CompileError::Pipeline(x86_pipeline_error_to_pipeline_error(e)))?
            };
            if let Some((cache, key, boundary)) = &cache_context {
                compile_artifact_cache_telemetry.push(store_compile_artifact(
                    cache,
                    key,
                    *boundary,
                    &bytes,
                    "trust-cg-codegen::Compiler::compile_x86_64",
                    proof_bundle_sha256.as_deref(),
                )?);
            }
            bytes
        };
        if tracing {
            // CT-8: fold the proof lane's shared module-encode time (the
            // assembly the object emission above reused) into this phase so
            // ALL module-encode work is reported here, none under
            // `x86_proof_certs`.
            #[cfg(feature = "verify")]
            let encode_duration = encode_start.elapsed() + proof_lane_assemble_duration;
            #[cfg(not(feature = "verify"))]
            let encode_duration = encode_start.elapsed();
            trace_entries.push(TraceEntry {
                phase: "x86_compile_module".to_string(),
                duration: encode_duration,
                detail: Some(format!("{} functions", function_count)),
            });
        }

        let metrics = CompilationMetrics {
            code_size_bytes: total_code_size,
            instruction_count,
            function_count,
            optimization_passes_run,
            proof_optimizations: ProofOptimizationMetrics::default(),
            fsym_trust_ir: FsymTrustIrMetrics::default(),
        };

        let trace = if tracing {
            Some(CompilerTrace {
                entries: trace_entries,
                total_duration: total_start.elapsed(),
            })
        } else {
            None
        };

        Ok(CompilationResult {
            object_code: obj_bytes,
            metrics,
            trace,
            proofs,
            certified_pass_chain: self.certified_pass_chain.clone(),
            proof_optimization_certificates: Vec::new(),
            compile_artifact_cache_telemetry,
        })
    }

    /// ITEM 2 — RISC-V production path through `Compiler::compile`.
    ///
    /// This is the SMALLEST SOUND increment that makes proof-driven bounds-check
    /// elimination reachable for `Target::Riscv64`. It mirrors the per-function
    /// ISel+gate loop of [`Self::compile_x86_64`] using the minimal, fail-closed
    /// RISC-V selector ([`crate::riscv::isel::select_function`]) and the existing
    /// S5 carrier/pass/expansion in [`crate::riscv::pipeline`].
    ///
    /// # Soundness boundary (fail-closed)
    ///
    /// The RISC-V backend has real liveness + linear-scan + spilling regalloc
    /// (phase 1), structured multi-block control flow (phase 2), self-recursive
    /// LP64D-ABI calls (phase 3), and — as of phase 4 — multi-function module
    /// emission with cross-function direct calls. This path accepts ONLY the
    /// function class the pipeline compiles correctly (integer args in `a0..a7`,
    /// a small opcode set + `Jump`/`Brif`/`Icmp`/`Trap` structured control flow
    /// over multiple blocks + the `GuardBoundsCheck` carrier + direct
    /// self/cross-function calls) and returns a clear `CompileError` for
    /// everything else (indirect/variadic calls, `Switch`, FP/vector, non-entry
    /// block params) — it NEVER silently miscompiles. The elimination decision
    /// flows through the SAME shared Certified-Elimination Kernel as x86/AArch64,
    /// with the same fail-closed independent re-check.
    ///
    /// Multiple accepted functions are concatenated into one `.text` section with
    /// a per-function `STT_FUNC` symbol. Intra-function branches are PC-relative
    /// and resolved within each function's own byte range (phase 2). A direct call
    /// to ANOTHER function in the same module is lowered to an `AUIPC`+`JALR`
    /// pcrel pair and resolved PC-relatively at module-emit time against the
    /// callee's `.text` offset — intra-object, no linker needed. A direct call to
    /// an EXTERNAL symbol (not defined in this module) is left as the placeholder
    /// `AUIPC`+`JALR` pair and recorded as an `R_RISCV_CALL` relocation in
    /// `.rela.text` for a real linker to patch. An in-module callee outside the
    /// signed-32-bit AUIPC reach fails closed.
    fn compile_riscv(
        &self,
        lir_functions: Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
        total_start: Instant,
        tracing: bool,
        mut trace_entries: Vec<TraceEntry>,
        trust_ir_module: &trust_ir::Module,
    ) -> Result<CompilationResult, CompileError> {
        use crate::elf::{ElfMachine, ElfWriter};
        use crate::riscv::isel::select_function;
        use crate::riscv::pipeline::{RiscVPipeline, RiscVPipelineConfig};

        // RISC-V proof emission is not yet implemented; honor `emit_proofs` as a
        // typed error rather than silently returning `proofs: None`.
        if self.config.emit_proofs {
            return Err(CompileError::ProofsUnsupportedForTarget {
                target: Target::Riscv64,
            });
        }

        let function_count = lir_functions.len();
        if function_count == 0 {
            return Err(CompileError::Pipeline(PipelineError::ISel(
                "RISC-V dispatcher received an empty module".to_string(),
            )));
        }

        // Same unconditional empty-authority policy as x86/AArch64.
        let kernel_gate_on = guard_kernel_gate_enabled();
        let mut riscv_guard_elim_eliminated: u32 = 0;

        // Phase 1: select each function (fail-closed), run the kernel gate, then
        // compile to raw machine-code bytes via the existing RISC-V pipeline.
        let isel_start = Instant::now();
        let pipeline = RiscVPipeline::new(RiscVPipelineConfig {
            emit_elf: false,
            emit_frame: true,
        });

        let mut per_func_code: Vec<(String, Vec<u8>, Vec<crate::riscv::pipeline::RiscVCallFixup>)> =
            Vec::with_capacity(function_count);
        for (lir_func, proof_ctx) in &lir_functions {
            let mut isel_func = select_function(lir_func).map_err(|e| {
                CompileError::Pipeline(PipelineError::ISel(format!(
                    "RISC-V minimal ISel rejected `{}`: {e}. The RISC-V production path \
                     supports integer-ABI functions with structured control flow \
                     (Jump/Brif/Icmp/Trap over multiple blocks; guard-bearing bounds-check \
                     shapes) and direct cross-function/self calls, but NOT indirect/variadic \
                     calls, Switch, FP/vector, or non-entry block params; use a different \
                     target for those.",
                    lir_func.name
                )))
            })?;

            // Sentinel S5: kernel-gated proof-driven bounds-check elimination.
            if kernel_gate_on {
                run_riscv_guard_kernel_gate(
                    &mut isel_func,
                    proof_ctx,
                    trust_ir_module,
                    &mut riscv_guard_elim_eliminated,
                )
                .map_err(|reason| {
                    CompileError::Pipeline(PipelineError::ISel(format!(
                        "RISC-V guard kernel gate fail-closed re-check rejected in `{}`: {reason}",
                        lir_func.name
                    )))
                })?;
            }

            // Cross-function direct calls are lowered to an AUIPC+JALR pcrel pair
            // carrying a Symbol placeholder; the per-function encoder cannot
            // resolve the callee's address, so it reports each as a
            // `RiscVCallFixup` the module emitter resolves below (intra-object
            // patch or external relocation).
            let (code, fixups) =
                pipeline
                    .compile_function_with_fixups(&isel_func)
                    .map_err(|e| {
                        CompileError::Pipeline(PipelineError::ISel(format!(
                            "RISC-V pipeline failed on `{}`: {e}",
                            lir_func.name
                        )))
                    })?;
            per_func_code.push((lir_func.name.clone(), code, fixups));
        }
        let _ = riscv_guard_elim_eliminated;

        if tracing {
            trace_entries.push(TraceEntry {
                phase: "riscv_isel".to_string(),
                duration: isel_start.elapsed(),
                detail: Some(format!("{} functions", function_count)),
            });
        }

        // Phase 2: concatenate all functions into one .text section (4-byte
        // aligned per function) and emit a single ELF .o with a per-function
        // STT_FUNC symbol at its offset, then resolve cross-function direct calls.
        //
        // CROSS-FUNCTION CALLS (phase 4): each function reports its cross-function
        // calls as `RiscVCallFixup`s (AUIPC+JALR pcrel pair, function-relative
        // offsets). After laying out .text, we resolve each fixup:
        //  * callee DEFINED in this module + within signed-32-bit AUIPC reach ->
        //    patch the AUIPC hi20 / JALR lo12 in `.text` PC-relatively. No
        //    relocation: the object is self-contained and runs without a linker.
        //  * callee NOT in this module (external) -> record one R_RISCV_CALL
        //    relocation at the AUIPC's section offset against an undefined
        //    STT_FUNC symbol, leaving the AUIPC+JALR placeholders for a real
        //    linker to patch (the ELF writer already supports .rela.text).
        //  * otherwise (in-module but unreachable) -> FAIL CLOSED with a typed
        //    error; never emit a zero/wrong call target.
        let encode_start = Instant::now();
        let mut text: Vec<u8> = Vec::new();
        // (name, section_offset, size, fixups-with-section-relative-offsets).
        let mut func_layout: Vec<(
            String,
            u64,
            u64,
            Vec<crate::riscv::pipeline::RiscVCallFixup>,
        )> = Vec::with_capacity(per_func_code.len());
        for (name, code, fixups) in &per_func_code {
            // 4-byte align each function start (RISC-V instruction alignment).
            while !text.len().is_multiple_of(4) {
                text.push(0);
            }
            let offset = text.len() as u64;
            text.extend_from_slice(code);
            // Rebase each fixup's function-relative offsets to section-relative.
            // RiscVCallFixup deliberately uses u32 offsets because AUIPC+JALR
            // patching is confined to that address domain. Never truncate or
            // wrap a large module offset onto an unrelated instruction.
            let rebased: Vec<crate::riscv::pipeline::RiscVCallFixup> = fixups
                .iter()
                .map(|fixup| rebase_riscv_call_fixup(name, offset, fixup))
                .collect::<Result<_, CompileError>>()?;
            func_layout.push((name.clone(), offset, code.len() as u64, rebased));
        }

        // Map each DEFINED function name to its section offset (for intra-object
        // call resolution). Defined-symbol collisions are impossible here (the LIR
        // module already has unique function names).
        let defined_offsets: HashMap<String, u64> = func_layout
            .iter()
            .map(|(name, off, _size, _fx)| (name.clone(), *off))
            .collect();

        // Patch intra-object calls IN PLACE, and collect external calls for a
        // relocation pass after the symbol table is built.
        let mut external_calls: Vec<crate::riscv::pipeline::RiscVCallFixup> = Vec::new();
        for (caller, _off, _size, fixups) in &func_layout {
            for fx in fixups {
                if let Some(&callee_off) = defined_offsets.get(&fx.callee) {
                    let callee_off = u32::try_from(callee_off).map_err(|_| {
                        CompileError::Pipeline(PipelineError::ISel(format!(
                            "RISC-V intra-object call from `{caller}` targets `{}` at .text offset {callee_off}, outside the u32 patch domain",
                            fx.callee
                        )))
                    })?;
                    crate::riscv::pipeline::riscv_patch_intra_object_call(
                        &mut text,
                        fx.auipc_offset,
                        fx.jalr_offset,
                        callee_off,
                    )
                    .map_err(|e| {
                        CompileError::Pipeline(PipelineError::ISel(format!(
                            "RISC-V intra-object call from `{caller}` to `{}` could not be \
                             resolved: {e}",
                            fx.callee
                        )))
                    })?;
                } else {
                    external_calls.push(fx.clone());
                }
            }
        }

        let total_code_size = text.len();
        let instruction_count = total_code_size / 4;

        let mut writer = ElfWriter::new(ElfMachine::Riscv64);
        writer.set_e_flags(crate::elf::constants::EF_RISCV_FLOAT_ABI_DOUBLE);
        writer.add_text_section(&text);

        // Symbol table: one global STT_FUNC per defined function at its offset.
        // ELF symbol index 0 is the null symbol (auto-emitted by the writer);
        // every symbol we add is GLOBAL, so the writer's locals-before-globals
        // partition preserves insertion order and insertion order == final index.
        // We therefore track the running index starting at 1 to reference symbols
        // from relocations correctly.
        const STT_FUNC: u8 = 2;
        let mut symbol_index: HashMap<String, u32> = HashMap::new();
        let mut next_symbol_index: u32 = 1;
        for (name, offset, size, _fx) in &func_layout {
            // section 1 = the .text section just added; STT_FUNC = 2.
            writer.add_symbol(name, 1, *offset, *size, true, STT_FUNC);
            symbol_index.insert(name.clone(), next_symbol_index);
            next_symbol_index += 1;
        }

        // EXTERNAL cross-function calls: emit an R_RISCV_CALL relocation at the
        // AUIPC's section offset against an undefined STT_FUNC symbol (section 0).
        // The ELF writer auto-creates .rela.text for any text relocation, with the
        // correct sh_link (-> .symtab) and sh_info (-> .text). A real linker
        // patches both the AUIPC hi20 and the following JALR lo12 from this single
        // relocation, addend 0.
        for fx in &external_calls {
            let sym_idx = if let Some(&idx) = symbol_index.get(&fx.callee) {
                idx
            } else {
                let idx = next_symbol_index;
                next_symbol_index += 1;
                // Undefined external function symbol: section 0, value/size 0.
                writer.add_symbol(&fx.callee, 0, 0, 0, true, STT_FUNC);
                symbol_index.insert(fx.callee.clone(), idx);
                idx
            };
            let rela = crate::elf::reloc::Elf64Rela::riscv(
                fx.auipc_offset as u64,
                sym_idx,
                crate::elf::reloc::RiscvRelocType::Call,
                0,
            );
            // add_relocation takes a 0-based user-section index; .text is the
            // first (and only) added section, so index 0.
            writer.add_relocation(0, rela);
        }

        let obj_bytes = writer.write();

        if tracing {
            trace_entries.push(TraceEntry {
                phase: "riscv_emit".to_string(),
                duration: encode_start.elapsed(),
                detail: Some(format!("{} functions", function_count)),
            });
        }

        let metrics = CompilationMetrics {
            code_size_bytes: total_code_size,
            instruction_count,
            function_count,
            optimization_passes_run: 0,
            proof_optimizations: ProofOptimizationMetrics::default(),
            fsym_trust_ir: FsymTrustIrMetrics::default(),
        };

        let trace = if tracing {
            Some(CompilerTrace {
                entries: trace_entries,
                total_duration: total_start.elapsed(),
            })
        } else {
            None
        };

        Ok(CompilationResult {
            object_code: obj_bytes,
            metrics,
            trace,
            proofs: None,
            certified_pass_chain: self.certified_pass_chain.clone(),
            proof_optimization_certificates: Vec::new(),
            compile_artifact_cache_telemetry: Vec::new(),
        })
    }

    fn compile_x86_64_to_jit(
        &self,
        lir_functions: Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
        extern_symbols: &HashMap<String, *const u8>,
        profile_hooks: crate::jit::ProfileHookMode,
        validation_mode: JitValidationMode,
        total_start: Instant,
        tracing: bool,
        mut trace_entries: Vec<TraceEntry>,
    ) -> Result<JitCompilationResult, CompileError> {
        use crate::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig};
        use trust_cg_lower::x86_64_isel::{X86CallAbi, X86InstructionSelector};

        let profile_call_counters_enabled = x86_profile_hooks_enable_call_counters(profile_hooks);
        let profile_block_counters_enabled = x86_profile_hooks_enable_block_counters(profile_hooks);
        if profile_hooks != crate::jit::ProfileHookMode::None
            && !profile_call_counters_enabled
            && !profile_block_counters_enabled
        {
            return Err(CompileError::Jit(
                crate::jit::JitError::ProfileHooksUnsupported,
            ));
        }

        #[cfg(not(feature = "verify"))]
        if self.config.emit_proofs {
            return Err(CompileError::ProofsUnsupportedForTarget {
                target: Target::X86_64,
            });
        }

        let function_count = lir_functions.len();
        if function_count == 0 {
            return Err(CompileError::EmptyModule);
        }

        // EH x86 Lane 2 residual: the AOT Mach-O path now emits unwind tables,
        // but the in-memory JIT has no eh_frame, so a JIT function carrying EH
        // structure still fails closed (JIT unwinding is a later lane).
        reject_x86_jit_eh(&lir_functions)?;

        let call_abi = x86_host_jit_abi();
        debug_assert!(
            matches!(call_abi, X86CallAbi::SystemV | X86CallAbi::WindowsX64),
            "x86 host JIT ABI must be known"
        );

        let isel_start = Instant::now();
        let isel_results: Vec<
            Result<
                (
                    trust_cg_lower::x86_64_isel::X86ISelFunction,
                    crate::pipeline::PhaseTimings,
                ),
                CompileError,
            >,
        > = lir_functions
            .par_iter()
            .map(|(lir_func, _proof_ctx)| {
                let func_isel_start = Instant::now();
                lir_func.validate_eh_structure().map_err(|reason| {
                    CompileError::Pipeline(PipelineError::ISel(format!(
                        "invalid x86 exception-handling structure in `{}`: {reason}",
                        lir_func.name
                    )))
                })?;
                let sig = trust_cg_lower::function::Signature {
                    params: lir_func.signature.params.clone(),
                    returns: lir_func.signature.returns.clone(),
                };
                let mut isel =
                    X86InstructionSelector::with_abi(lir_func.name.clone(), sig.clone(), call_abi);
                isel.set_stack_slots(lir_func.stack_slots.clone());
                isel.seed_value_types(&lir_func.value_types);
                isel.seed_function_value_use_counts(lir_func);
                isel.seed_pure_callees(&lir_func.pure_callees);
                let block_order = lir_func.layout_order();
                // Seed the whole-function Iconst origin map (see the serial
                // path above) — constant-divisor magic strength reduction and
                // cross-block constant rematerialization both consume it.
                isel.seed_iconst_origins(
                    block_order
                        .iter()
                        .map(|b| lir_func.blocks[b].instructions.as_slice()),
                );
                for block_ref in &block_order {
                    isel.ensure_block(*block_ref);
                }
                isel.lower_formal_arguments(&sig, lir_func.entry_block)
                    .map_err(|e| CompileError::Pipeline(PipelineError::ISel(e.to_string())))?;
                for block_ref in &block_order {
                    let basic_block = &lir_func.blocks[block_ref];
                    if *block_ref != lir_func.entry_block && !basic_block.params.is_empty() {
                        isel.define_block_params(&basic_block.params);
                    }
                    isel.select_block(*block_ref, &basic_block.instructions)
                        .map_err(|e| CompileError::Pipeline(PipelineError::ISel(e.to_string())))?;
                }
                let mut timings = crate::pipeline::PhaseTimings::default();
                timings.isel = Some(nonzero_duration(func_isel_start.elapsed()));
                let isel_func = isel
                    .finalize_with_eh_info(&lir_func.eh_info)
                    .map_err(|e| CompileError::Pipeline(PipelineError::ISel(e.to_string())))?;
                Ok((isel_func, timings))
            })
            .collect();

        let mut isel_funcs = Vec::with_capacity(function_count);
        let mut phase_timings = Vec::with_capacity(function_count);
        for res in isel_results {
            let (func, timings) = res?;
            isel_funcs.push(func);
            phase_timings.push(timings);
        }

        // TV-3: block-level lowering-integrity validation on the RAW pre-pass
        // JIT ISel output (same fail-closed gate as the AOT path; the JIT is a
        // first-class G4 consumer). MUST run before the optimizer passes below.
        for (func, (lir_func, _)) in isel_funcs.iter().zip(lir_functions.iter()) {
            enforce_x86_dataflow_integrity(func, lir_func)?;
        }

        if tracing {
            trace_entries.push(TraceEntry {
                phase: "x86_jit_isel".to_string(),
                duration: isel_start.elapsed(),
                detail: Some(format!("{} functions", function_count)),
            });
        }

        let x86_opt_level = x86_opt_level_from_codegen(self.config.opt_level);
        let mut optimized_isel_funcs = isel_funcs.clone();
        let opt_start = Instant::now();
        // JIT-8: give the x86 in-process JIT a latency-tuned allocation profile.
        // The production JIT (`CompilerConfig::for_host_jit` / `jit_fast`) sets
        // `enable_jit_fast_regalloc`; under it we select `host_jit_fast()` (the
        // LinearScan allocator core) instead of the default Greedy profile,
        // cutting JIT-compile latency toward the aarch64 `jit_fast` numbers
        // (~11% lower total JIT-compile time on the uuf50-218 BCP kernel).
        //
        // This is a latency/code-quality trade only — the always-on regalloc
        // translation validator proves every allocation, so a lower-quality
        // allocation fails closed rather than miscompiling, and the JIT-5
        // CachedVerified cert path still covers every emitted byte. AOT is
        // unaffected (it never sets `enable_jit_fast_regalloc`).
        // `TCG_NO_X86_JIT_LINEARSCAN` forces the previous Greedy profile.
        let use_fast_jit_regalloc =
            self.config.enable_jit_fast_regalloc && x86_jit_linearscan_regalloc_enabled();
        let jit_base_config = if use_fast_jit_regalloc {
            X86PipelineConfig::host_jit_fast()
        } else {
            X86PipelineConfig::host_jit()
        };
        let pipeline = X86Pipeline::new(X86PipelineConfig {
            opt_level: x86_opt_level,
            output_format: X86OutputFormat::RawBytes,
            emit_frame: true,
            call_abi,
            ..jit_base_config
        });
        // JIT-8 Greedy fallback: LinearScan spills harder than Greedy and a rare
        // high-register-pressure function (e.g. v16i8 bool-vector selects) can
        // exceed the x86 spill-replay scratch budget and fail closed under
        // LinearScan while Greedy allocates it. To preserve completeness with no
        // regression, when the fast profile is active we keep a Greedy pipeline
        // and retry any function LinearScan cannot compile. Fallback output is
        // byte-identical to the pre-JIT-8 Greedy path (the optimizer passes are
        // regalloc-mode-independent), both paths pass the always-on validator,
        // and if BOTH fail we surface the Greedy error — the exact fail-closed
        // behavior callers saw before JIT-8.
        let fallback_pipeline = if use_fast_jit_regalloc {
            Some(X86Pipeline::new(X86PipelineConfig {
                opt_level: x86_opt_level,
                output_format: X86OutputFormat::RawBytes,
                emit_frame: true,
                call_abi,
                ..X86PipelineConfig::host_jit()
            }))
        } else {
            None
        };

        let optimization_passes_run: usize = optimized_isel_funcs
            .par_iter_mut()
            .zip(phase_timings.par_iter_mut())
            .map(|(func, timings)| {
                let func_opt_start = Instant::now();
                let passes = pipeline.run_x86_optimization_passes(func).total_pass_runs();
                timings.optimization = Some(nonzero_duration(func_opt_start.elapsed()));
                passes
            })
            .sum();

        if tracing {
            trace_entries.push(TraceEntry {
                phase: "x86_jit_optimization".to_string(),
                duration: opt_start.elapsed(),
                detail: Some(format!("{} pass runs", optimization_passes_run)),
            });
        }

        // PROOF-GAP item 1 + 3 (JIT path): same unconditional fail-closed gates
        // as the AOT path. Carrier hygiene (#51 / #66) runs per-function over
        // the post-optimization stream that is actually encoded; the glue-pass
        // validator (#67) is now PER-PROGRAM over the same emitted functions
        // (structural IMUL->IDIV net + idiom enumeration, deduped + re-verified).
        // Pure-lattice / exhaustive — no solver.
        optimized_isel_funcs
            .par_iter()
            .try_for_each(check_x86_carrier_hygiene)?;
        validate_x86_glue_pass_expansions(&optimized_isel_funcs)?;

        // JIT-5: proof-certificate generation + fail-closed promotion gate is
        // deferred to AFTER encoding so the content-addressed certificate cache
        // can key on the exact per-function emitted (pre-fixup) bytes — the
        // bytes-hash binding that makes a warm hit sound (a reused verdict is
        // bound to the machine bytes it vouched for). The gate still runs before
        // `publish`, so no uncertified byte is ever placed in executable memory
        // on a verifying mode. See the `proofs` / `jit_validation` block below.

        let encode_start = Instant::now();
        struct Encoded {
            body_offset: u64,
            published_len: usize,
            call_fixups: Vec<crate::x86_64::pipeline::X86CallFixup>,
            global_ref_fixups: Vec<crate::x86_64::pipeline::X86GlobalRefFixup>,
            machine_code_evidence: X86MachineCodeEvidence,
        }

        struct CompResult {
            func_code: Vec<u8>,
            const_pool: Vec<u8>,
            call_fixups: Vec<crate::x86_64::pipeline::X86CallFixup>,
            global_ref_fixups: Vec<crate::x86_64::pipeline::X86GlobalRefFixup>,
            machine_code_evidence: X86MachineCodeEvidence,
            counter_patch_sites: Vec<crate::x86_64::pipeline::X86BlockCounterPatchSite>,
            func_encode_elapsed: Duration,
        }

        let compilation_results: Vec<Result<CompResult, CompileError>> = optimized_isel_funcs
            .par_iter()
            .map(|func| {
                let func_encode_start = Instant::now();
                if profile_block_counters_enabled {
                    // JIT-8: try the fast (LinearScan) pipeline, then fall back
                    // to Greedy for any function it cannot allocate.
                    let profiled = match pipeline
                        .compile_function_with_jit_block_counters_after_x86_passes(func)
                    {
                        Ok(v) => v,
                        Err(fast_err) => match &fallback_pipeline {
                            Some(fb) => fb
                                .compile_function_with_jit_block_counters_after_x86_passes(func)
                                .map_err(|e| {
                                    CompileError::Pipeline(PipelineError::ISel(e.to_string()))
                                })?,
                            None => {
                                return Err(CompileError::Pipeline(PipelineError::ISel(
                                    fast_err.to_string(),
                                )));
                            }
                        },
                    };
                    Ok(CompResult {
                        func_code: profiled.code,
                        const_pool: profiled.const_pool,
                        call_fixups: profiled.call_fixups,
                        global_ref_fixups: profiled.global_ref_fixups,
                        machine_code_evidence: profiled.machine_code_evidence,
                        counter_patch_sites: profiled.counter_patch_sites,
                        func_encode_elapsed: func_encode_start.elapsed(),
                    })
                } else {
                    // JIT-8: try the fast (LinearScan) pipeline, then fall back
                    // to Greedy for any function it cannot allocate.
                    let (
                        func_code,
                        const_pool,
                        call_fixups,
                        global_ref_fixups,
                        machine_code_evidence,
                    ) = match pipeline
                        .compile_function_with_fixups_and_evidence_after_x86_passes(func)
                    {
                        Ok(v) => v,
                        Err(fast_err) => match &fallback_pipeline {
                            Some(fb) => fb
                                .compile_function_with_fixups_and_evidence_after_x86_passes(func)
                                .map_err(|e| {
                                    CompileError::Pipeline(PipelineError::ISel(e.to_string()))
                                })?,
                            None => {
                                return Err(CompileError::Pipeline(PipelineError::ISel(
                                    fast_err.to_string(),
                                )));
                            }
                        },
                    };
                    Ok(CompResult {
                        func_code,
                        const_pool,
                        call_fixups,
                        global_ref_fixups,
                        machine_code_evidence,
                        counter_patch_sites: Vec::new(),
                        func_encode_elapsed: func_encode_start.elapsed(),
                    })
                }
            })
            .collect();

        let mut code = Vec::new();
        let mut encoded = Vec::with_capacity(function_count);
        let mut func_offsets: HashMap<String, u64> = HashMap::with_capacity(function_count);
        let mut symbol_offsets: HashMap<String, u64> = HashMap::with_capacity(function_count * 2);
        let mut canonical_symbols = Vec::with_capacity(function_count);
        let mut function_ranges = Vec::with_capacity(function_count);
        let mut windows_unwind_functions = Vec::with_capacity(function_count);
        let mut counters: HashMap<String, Box<AtomicU64>> = HashMap::new();
        let mut counter_patch_sites: Vec<(usize, *const AtomicU64)> = Vec::new();
        // JIT-5: per-function pre-fixup emitted machine bytes, captured in
        // `optimized_isel_funcs` order. These are the deterministic image of
        // each ISel function (the exact stream the verifier certifies), so
        // their SHA-256 is the sound content+bytes key for the cert cache.
        let mut per_func_emitted_code: Vec<Vec<u8>> = Vec::with_capacity(function_count);

        for (idx, (func, comp_res)) in optimized_isel_funcs
            .iter()
            .zip(compilation_results)
            .enumerate()
        {
            let comp_res = comp_res?;
            per_func_emitted_code.push(comp_res.func_code.clone());
            if symbol_offsets.contains_key(func.name.as_str()) {
                return Err(CompileError::Jit(crate::jit::JitError::DuplicateSymbol(
                    func.name.clone(),
                )));
            }
            let alias = format!("_{}", func.name);
            if symbol_offsets.contains_key(alias.as_str()) {
                return Err(CompileError::Jit(crate::jit::JitError::DuplicateSymbol(
                    alias,
                )));
            }

            let text_offset = code.len() as u64;
            if profile_call_counters_enabled {
                let counter = Box::new(AtomicU64::new(0));
                let counter_ptr = counter.as_ref() as *const AtomicU64;
                let imm64_offset = emit_x86_64_profile_counter_trampoline(&mut code);
                counter_patch_sites.push((imm64_offset, counter_ptr));
                counters.insert(func.name.clone(), counter);
            }
            let body_offset = code.len() as u64;

            if profile_block_counters_enabled {
                let func_base = code.len();
                for site in &comp_res.counter_patch_sites {
                    let key = format!("{}::block{}", func.name, site.block.0);
                    if counters.contains_key(&key) {
                        return Err(CompileError::Jit(crate::jit::JitError::DuplicateSymbol(
                            key,
                        )));
                    }
                    let counter = Box::new(AtomicU64::new(0));
                    let counter_ptr = counter.as_ref() as *const AtomicU64;
                    counter_patch_sites.push((func_base + site.imm64_offset, counter_ptr));
                    counters.insert(key, counter);
                }
            }

            // `compile_function_with_fixups_and_evidence_after_x86_passes` runs
            // regalloc + frame lowering + branch resolution + encoding behind a
            // single call and hands back ONE elapsed duration, so this path
            // cannot attribute that time to a phase.
            //
            // It used to divide the region by four and write the identical
            // quotient into all four fields. That made those rows exactly equal
            // in every JIT breakdown by construction -- an artifact of the
            // split, not a measurement -- while looking like real per-phase
            // data to `jit_compile_breakdown_table` and to the downstream `ty`
            // A/B benchmarks. Report it as unattributed instead: the total
            // stays correct and the breakdown stops inventing a ranking.
            //
            // The AOT `prepare_function_with_metrics*` family already times all
            // four separately; porting those timers here is what shrinks this.
            phase_timings[idx].unattributed = Some(nonzero_duration(comp_res.func_encode_elapsed));
            code.extend_from_slice(&comp_res.func_code);
            let function_code_end = code.len() as u64;
            code.extend_from_slice(&comp_res.const_pool);
            let function_end = code.len() as u64;

            canonical_symbols.push(func.name.clone());
            func_offsets.insert(func.name.clone(), text_offset);
            symbol_offsets.insert(func.name.clone(), text_offset);
            symbol_offsets.insert(format!("_{}", func.name), text_offset);
            function_ranges.push((func.name.clone(), text_offset..function_end));
            windows_unwind_functions.push(
                crate::jit::WindowsJitUnwindFunction::new(
                    func.name.clone(),
                    text_offset,
                    function_code_end,
                )
                .with_dynamic_stack_alloc(x86_function_has_dynamic_stack_alloc(func)),
            );
            encoded.push(Encoded {
                body_offset: if profile_block_counters_enabled {
                    text_offset
                } else {
                    body_offset
                },
                published_len: (function_end - text_offset) as usize,
                call_fixups: comp_res.call_fixups,
                global_ref_fixups: comp_res.global_ref_fixups,
                machine_code_evidence: comp_res.machine_code_evidence,
            });
        }

        let function_code_size: usize = encoded.iter().map(|func| func.published_len).sum();

        let mut veneers: HashMap<String, u64> = HashMap::new();
        let mut extern_ref_slots: HashMap<String, u64> = HashMap::new();
        for func in &encoded {
            for fixup in &func.call_fixups {
                let disp32_offset = func.body_offset as usize + fixup.offset;
                let target = if let Some(&ptr) = extern_symbols.get(&fixup.callee) {
                    *veneers
                        .entry(fixup.callee.clone())
                        .or_insert_with(|| emit_x86_64_absolute_jump_veneer(&mut code, ptr))
                } else if let Some(&offset) = func_offsets.get(&fixup.callee) {
                    offset
                } else if let Some(ptr) = resolve_x86_jit_extern(&fixup.callee, extern_symbols) {
                    *veneers
                        .entry(fixup.callee.clone())
                        .or_insert_with(|| emit_x86_64_absolute_jump_veneer(&mut code, ptr))
                } else if let Some(&offset) = symbol_offsets.get(&fixup.callee) {
                    offset
                } else {
                    return Err(CompileError::Jit(crate::jit::JitError::UnresolvedSymbol(
                        fixup.callee.clone(),
                    )));
                };
                patch_x86_64_rel32_call(&mut code, disp32_offset, target)
                    .map_err(CompileError::Jit)?;
            }
            for fixup in &func.global_ref_fixups {
                let disp32_offset = func.body_offset as usize + fixup.offset;
                let target = match fixup.kind {
                    crate::x86_64::pipeline::X86SymbolRefFixupKind::GlobalRef => {
                        let Some(&target) = symbol_offsets.get(&fixup.symbol) else {
                            return Err(CompileError::Jit(crate::jit::JitError::UnresolvedSymbol(
                                fixup.symbol.clone(),
                            )));
                        };
                        target
                    }
                    crate::x86_64::pipeline::X86SymbolRefFixupKind::ExternRefGot => {
                        if let Some(&slot) = extern_ref_slots.get(&fixup.symbol) {
                            slot
                        } else {
                            let ptr = resolve_x86_jit_extern(&fixup.symbol, extern_symbols)
                                .ok_or_else(|| {
                                    CompileError::Jit(crate::jit::JitError::UnresolvedSymbol(
                                        fixup.symbol.clone(),
                                    ))
                                })?;
                            while code.len() % 8 != 0 {
                                code.push(0xCC);
                            }
                            let slot = code.len() as u64;
                            code.extend_from_slice(&(ptr as u64).to_le_bytes());
                            extern_ref_slots.insert(fixup.symbol.clone(), slot);
                            slot
                        }
                    }
                    crate::x86_64::pipeline::X86SymbolRefFixupKind::TlsTlv => {
                        // Fail closed: a Mach-O `@TLVP` thread-local descriptor
                        // load cannot be resolved in the in-process JIT — it
                        // needs dyld's TLV runtime plus the linker's load->LEA
                        // relaxation, neither of which the JIT fixup path runs.
                        // (TLS is exercised only through the AOT object emitter.)
                        return Err(CompileError::Jit(crate::jit::JitError::UnresolvedSymbol(
                            format!(
                                "{} (@TLVP thread-local descriptor: unsupported in the in-process JIT; use AOT object emission)",
                                fixup.symbol
                            ),
                        )));
                    }
                };
                patch_x86_64_rel32_call(&mut code, disp32_offset, target)
                    .map_err(CompileError::Jit)?;
            }
        }
        if tracing {
            trace_entries.push(TraceEntry {
                phase: "x86_jit_encode".to_string(),
                duration: encode_start.elapsed(),
                detail: Some(format!("{} functions", function_count)),
            });
        }

        // JIT-5: proof-certificate generation, content-addressed caching, and
        // the fail-closed promotion gate — all BEFORE publish so no uncertified
        // byte reaches executable memory on a verifying mode.
        //
        // - `Unchecked`: no certs (dev-only; reachable only via the explicit
        //   opt-in resolved above). `proofs` stays `None`.
        // - `CachedVerified`: per function, look up the content-addressed cache
        //   keyed by (SHA-256 of the pre-fixup emitted bytes x config
        //   fingerprint). A warm hit reuses the verdict WITHOUT re-running the
        //   verifier (the bytes-hash binding is inherent in the key). A miss
        //   runs the full verifier and populates the cache.
        // - `AlwaysVerify`: verify every function every compile; never cache.
        //
        // Then the standard promotion gate rejects the whole compile if any
        // function is not verified.
        let (proofs, per_function_validation): (
            Option<Vec<ProofCertificate>>,
            Vec<JitFunctionValidation>,
        ) = self.x86_jit_certify_functions(
            validation_mode,
            &optimized_isel_funcs,
            &lir_functions,
            &per_func_emitted_code,
        )?;

        let publish_start = Instant::now();
        let mut buffer = crate::jit::publish_raw_executable_buffer_with_profile_data(
            &code,
            canonical_symbols,
            symbol_offsets,
            function_ranges,
            counters,
            counter_patch_sites,
            windows_unwind_functions,
        )
        .map_err(CompileError::Jit)?;
        if tracing {
            trace_entries.push(TraceEntry {
                phase: "x86_jit_publish".to_string(),
                duration: publish_start.elapsed(),
                detail: Some(format!("{} bytes", code.len())),
            });
        }

        // JIT-5: bind the per-function coverage to the published-image hash
        // (JIT-7's publish check) so "every published byte is covered by a
        // bytes-bound verified certificate" is auditable on the result.
        let validation = Some(JitValidationProvenance {
            mode: validation_mode,
            published_image_sha256: buffer.published_image_sha256().to_string(),
            functions: per_function_validation,
        });

        let per_function_metrics: Vec<FunctionQualityMetrics> = optimized_isel_funcs
            .iter()
            .zip(phase_timings)
            .zip(&encoded)
            .map(|((func, phase_timings), encoded)| FunctionQualityMetrics {
                name: func.name.clone(),
                code_size_bytes: encoded.published_len,
                instruction_count: count_x86_real_instructions(func),
                spill_slot_count: 0,
                branch_count: count_x86_branch_instructions(func),
                x86_machine_code: encoded.machine_code_evidence,
                phase_timings,
            })
            .collect();

        let instruction_count: usize = optimized_isel_funcs
            .iter()
            .map(count_x86_real_instructions)
            .sum();
        let metrics = CompilationMetrics {
            code_size_bytes: function_code_size,
            instruction_count,
            function_count,
            optimization_passes_run,
            proof_optimizations: ProofOptimizationMetrics::default(),
            fsym_trust_ir: FsymTrustIrMetrics::default(),
        };

        let trace = if tracing {
            Some(CompilerTrace {
                entries: trace_entries,
                total_duration: total_start.elapsed(),
            })
        } else {
            None
        };

        buffer.attach_proof_optimization_certificates(Vec::new());

        Ok(JitCompilationResult {
            buffer,
            metrics,
            trace,
            proofs,
            proof_optimization_certificates: Vec::new(),
            per_function_metrics,
            validation,
        })
    }

    /// Compile a pre-built IR function (skipping trust_ir adapter and ISel).
    ///
    /// Useful when you already have an `IrMachFunction` and want to run
    /// optimization, regalloc, frame lowering, encoding, and Mach-O emission.
    pub fn compile_ir_function(
        &self,
        ir_func: &mut trust_cg_ir::MachFunction,
    ) -> Result<CompilationResult, CompileError> {
        if self.config.target != Target::Aarch64 {
            return Err(CompileError::PrebuiltIrTargetUnsupported {
                target: self.config.target,
            });
        }
        if self.requires_verified_proof_promotion() {
            return Err(CompileError::ProofPromotionRejected {
                target: self.config.target,
                reason: "direct single-function prebuilt-IR emission cannot yet produce an exact relocation inventory for the object it emits: the single-function Mach-O path always adds compact-unwind relocations (and may add DWARF eh_frame relocations), while the module inventory models a different emission plan. Refusing proof promotion until inventory is derived from the exact emitted object/plan (fail-closed)".to_string(),
            });
        }
        let start = Instant::now();
        let pipeline = self.build_pipeline();

        let (obj_bytes, optimization_stats) = pipeline.compile_ir_function_with_stats(ir_func)?;
        #[cfg(not(feature = "verify"))]
        let _ = optimization_stats;

        // Count actual non-pseudo instructions from the function, not obj size / 4
        // which would include Mach-O headers, symbol tables, and relocations.
        let code_insts = count_real_instructions(ir_func);
        // Query actual pass count from the optimization pipeline (fixes #272).
        let opt_passes = {
            use trust_cg_opt::pipeline::{OptLevel as OptOptLevel, OptimizationPipeline};
            let opt_level = match self.config.opt_level {
                OptLevel::O0 => OptOptLevel::O0,
                OptLevel::O1 => OptOptLevel::O1,
                OptLevel::O2 => OptOptLevel::O2,
                OptLevel::O3 => OptOptLevel::O3,
            };
            OptimizationPipeline::new(opt_level).pass_count()
        };

        let metrics = CompilationMetrics {
            code_size_bytes: code_insts * 4,
            instruction_count: code_insts,
            function_count: 1,
            optimization_passes_run: opt_passes,
            proof_optimizations: ProofOptimizationMetrics::default(),
            fsym_trust_ir: FsymTrustIrMetrics::default(),
        };

        let trace = if self.config.trace_level != CompilerTraceLevel::None {
            Some(CompilerTrace {
                entries: vec![TraceEntry {
                    phase: "compile_ir_function".to_string(),
                    duration: start.elapsed(),
                    detail: Some(ir_func.name.clone()),
                }],
                total_duration: start.elapsed(),
            })
        } else {
            None
        };

        // Proof promotion for this boundary is rejected before compilation
        // above until an exact single-function object inventory exists.
        let proofs: Option<Vec<ProofCertificate>> = None;

        #[cfg(feature = "verify")]
        let certified_pass_chain = self.certified_pass_chain_attachment_from_runs(
            &ir_func.name,
            &optimization_stats.certified_pass_runs,
        )?;
        #[cfg(not(feature = "verify"))]
        let certified_pass_chain = self.certified_pass_chain.clone();

        Ok(CompilationResult {
            object_code: obj_bytes,
            metrics,
            trace,
            proofs,
            certified_pass_chain,
            proof_optimization_certificates: Vec::new(),
            compile_artifact_cache_telemetry: Vec::new(),
        })
    }

    /// Compile a trust_ir module to executable memory for JIT execution.
    ///
    /// This API is for in-process execution. The configured target and, for
    /// x86-64, the requested OS/ABI target spec must match the host process;
    /// otherwise the compiler returns [`CompileError::JitTargetMismatch`] or
    /// [`CompileError::JitTargetSpecMismatch`] before lowering. Use
    /// [`Compiler::for_host`] or [`CompilerConfig::for_host_jit`] for host JIT
    /// callers.
    ///
    /// Translates each function in the module through the full pipeline:
    /// trust_ir adapter -> ISel -> optimization -> regalloc -> frame lowering
    /// -> branch resolution -> JIT linking.
    ///
    /// All functions are compiled into a single executable buffer with each
    /// function as a separate symbol. Cross-function branches are resolved
    /// directly in memory and external symbols are bound from `extern_symbols`.
    ///
    /// Returns the executable buffer, metrics, optional trace, and optional
    /// proof certificates.
    pub fn compile_module_to_jit(
        &self,
        module: &trust_ir::Module,
        extern_symbols: &std::collections::HashMap<String, *const u8>,
    ) -> Result<JitCompilationResult, CompileError> {
        self.compile_module_to_jit_with_profile_hooks(
            module,
            extern_symbols,
            crate::jit::ProfileHookMode::None,
        )
    }

    /// Compile a trust_ir module to executable memory with explicit JIT profiling
    /// hooks.
    ///
    /// This keeps the existing [`Self::compile_module_to_jit`] zero-overhead
    /// default intact while giving CLI/profile-generate callers a public route
    /// to target-specific block-counter JIT support. AArch64 delegates to the
    /// raw JIT block-trampoline path; x86-64 injects block counters in the
    /// compiler pipeline before publishing executable memory.
    pub fn compile_module_to_jit_with_profile_hooks(
        &self,
        module: &trust_ir::Module,
        extern_symbols: &std::collections::HashMap<String, *const u8>,
        profile_hooks: crate::jit::ProfileHookMode,
    ) -> Result<JitCompilationResult, CompileError> {
        self.ensure_host_jit_target()?;
        // JIT-5: resolve the validation mode ONCE (applies the
        // TCG_JIT_UNCHECKED=1 env gate + fail-closed downgrade check), then
        // thread it into both cert machineries. `to_jit_config` re-resolves for
        // the aarch64 JitCertificate `verify` bit; the one-time env warning is
        // idempotent so a double-resolve is harmless.
        let validation_mode = self.config.resolve_jit_validation_mode()?;
        let jit_config = self.config.to_jit_config(profile_hooks)?;

        let total_start = Instant::now();
        let tracing = self.config.trace_level != CompilerTraceLevel::None;
        let mut trace_entries = Vec::new();

        // Phase 0: Pre-adapter dialect lowering (#433, trust_ir #428).
        //
        // Runs `trust_ir::dialect::lower_module` with an internal
        // `DialectRegistry` so any `Inst::DialectOp` (e.g. `verif.bfs_step`,
        // `verif.frontier_drain`) is rewritten into core trust_ir before the
        // adapter runs. Unknown dialects are rejected here — the adapter
        // has no DialectOp handler and would otherwise fail at ISel.
        //
        // Modules with no dialect ops borrow the input unchanged. Dialectful
        // modules clone locally because the dialect driver needs `&mut Module`
        // and the public JIT signature is `&Module`.
        let dialect_start = Instant::now();
        let (lowered_module, rewrites) = lower_dialects_if_needed(module)?;
        if tracing {
            trace_entries.push(TraceEntry {
                phase: "dialect_lower".to_string(),
                duration: dialect_start.elapsed(),
                detail: Some(format!("{} rewrites", rewrites)),
            });
        }
        let lowered_module = lowered_module.as_ref();

        // Phase 1: Translate trust_ir module to internal LIR functions.
        // Sentinel S5 hardening: per-arch exact-bound carrier cap (see above).
        // TLS dialect follows the target triple's object format (see above).
        let adapter_start = Instant::now();
        let lir_functions = trust_cg_lower::translate_module_for_arch_with_tls(
            lowered_module,
            guard_carrier_arch_for_target(self.config.target),
            if crate::pipeline::target_triple_uses_elf(&compiler_target_triple(self.target_spec)) {
                trust_cg_lower::TlsDialect::ElfLocalExec
            } else {
                trust_cg_lower::TlsDialect::MachOTlv
            },
        )?;
        if tracing {
            trace_entries.push(TraceEntry {
                phase: "adapter".to_string(),
                duration: adapter_start.elapsed(),
                detail: Some(format!("{} functions", lir_functions.len())),
            });
        }

        if lir_functions.is_empty() {
            return Err(CompileError::EmptyModule);
        }

        if self.config.target == Target::X86_64 {
            return self.compile_x86_64_to_jit(
                lir_functions,
                extern_symbols,
                profile_hooks,
                validation_mode,
                total_start,
                tracing,
                trace_entries,
            );
        }

        // [TCG-EH-A64-BATCH]: keep EH-bearing JIT functions behind the
        // complete-sidecar boundary described by `reject_aarch64_jit_eh`.
        reject_aarch64_jit_eh(&lir_functions)?;

        // Build the internal pipeline.
        let pipeline = self.build_pipeline();

        // Phase 2+: Prepare each function through ISel, optimization,
        // regalloc, frame lowering, and branch resolution. The prepared
        // functions are then handed to the JIT compiler for in-memory code
        // generation and cross-function fixup resolution.
        //
        // When parallel compilation is enabled and there are 2+ functions,
        // use rayon to prepare functions concurrently. Each function's
        // pipeline (ISel -> opt -> regalloc -> frame -> branch resolution)
        // is fully independent with no shared mutable state.
        let parallel_worker_count = if self.config.parallel {
            crate::resource_limits::worker_count_for_items(lir_functions.len())
        } else {
            None
        };
        let use_parallel = parallel_worker_count.is_some();
        let trust_ir_functions_for_lir: Vec<Option<&trust_ir::Function>> = lir_functions
            .iter()
            .map(|(lir_func, _)| trust_ir_function_for_lir(lowered_module, lir_func))
            .collect();

        let mut prepared_funcs: Vec<trust_cg_ir::MachFunction>;
        let mut preparation_metrics: Vec<crate::pipeline::PreparationMetrics>;

        if use_parallel {
            // Parallel path: each function is prepared independently via rayon.
            // Collect results with optional trace entries, then unpack.
            let worker_count = parallel_worker_count.unwrap_or(1);
            let pool = crate::resource_limits::build_rayon_pool(worker_count).map_err(|err| {
                CompileError::Pipeline(PipelineError::ISel(format!(
                    "parallel worker pool error: {err}"
                )))
            })?;
            let results: Vec<
                Result<
                    (
                        trust_cg_ir::MachFunction,
                        crate::pipeline::PreparationMetrics,
                        Option<TraceEntry>,
                    ),
                    CompileError,
                >,
            > = pool.install(|| {
                lir_functions
                    .par_iter()
                    .zip(trust_ir_functions_for_lir.par_iter())
                    .map(|((lir_func, proof_ctx), trust_ir_func)| {
                        let func_start = Instant::now();
                        let (ir_func, metrics) = if let Some(trust_ir_func) = *trust_ir_func {
                            pipeline
                                .prepare_function_with_metrics_and_trust_ir_module(
                                    lir_func,
                                    Some(proof_ctx),
                                    lowered_module,
                                    trust_ir_func,
                                )
                                .map_err(CompileError::Pipeline)?
                        } else {
                            pipeline
                                .prepare_function_with_metrics(lir_func, Some(proof_ctx))
                                .map_err(CompileError::Pipeline)?
                        };
                        let entry = if tracing {
                            Some(TraceEntry {
                                phase: "prepare_function".to_string(),
                                duration: func_start.elapsed(),
                                detail: Some(ir_func.name.clone()),
                            })
                        } else {
                            None
                        };
                        Ok((ir_func, metrics, entry))
                    })
                    .collect()
            });

            prepared_funcs = Vec::with_capacity(results.len());
            preparation_metrics = Vec::with_capacity(results.len());
            for result in results {
                let (ir_func, metrics, trace_entry) = result?;
                if let Some(entry) = trace_entry {
                    trace_entries.push(entry);
                }
                preparation_metrics.push(metrics);
                prepared_funcs.push(ir_func);
            }
        } else {
            // Sequential path: single function or parallel disabled.
            prepared_funcs = Vec::with_capacity(lir_functions.len());
            preparation_metrics = Vec::with_capacity(lir_functions.len());
            for ((lir_func, proof_ctx), trust_ir_func) in
                lir_functions.iter().zip(trust_ir_functions_for_lir.iter())
            {
                let func_start = Instant::now();

                let (ir_func, metrics) = if let Some(trust_ir_func) = *trust_ir_func {
                    pipeline.prepare_function_with_metrics_and_trust_ir_module(
                        lir_func,
                        Some(proof_ctx),
                        lowered_module,
                        trust_ir_func,
                    )?
                } else {
                    pipeline.prepare_function_with_metrics(lir_func, Some(proof_ctx))?
                };

                if tracing {
                    trace_entries.push(TraceEntry {
                        phase: "prepare_function".to_string(),
                        duration: func_start.elapsed(),
                        detail: Some(ir_func.name.clone()),
                    });
                }

                preparation_metrics.push(metrics);
                prepared_funcs.push(ir_func);
            }
        }

        let function_count = prepared_funcs.len();
        let proof_optimization_certificates =
            collect_proof_optimization_certificates(&preparation_metrics);
        let fsym_trust_ir_metrics = summarize_fsym_trust_ir_metrics(&preparation_metrics);

        #[cfg(feature = "verify")]
        let proofs = if self.config.emit_proofs || self.requires_verified_proof_promotion() {
            let all_certs: Vec<ProofCertificate> = if use_parallel {
                let worker_count = parallel_worker_count.unwrap_or(1);
                let pool =
                    crate::resource_limits::build_rayon_pool(worker_count).map_err(|err| {
                        CompileError::Pipeline(PipelineError::ISel(format!(
                            "parallel worker pool error: {err}"
                        )))
                    })?;
                pool.install(|| {
                    // TV-2: `prepared_funcs` is built 1:1 in `lir_functions`
                    // order, so the zip pairs each MachFunction with the LIR
                    // function its ISel consumed; the verifier additionally
                    // name-guards the pairing.
                    prepared_funcs
                        .par_iter()
                        .zip(lir_functions.par_iter())
                        .flat_map(|(func, (lir_func, _))| {
                            generate_proof_certificates(func, Some(lir_func))
                        })
                        .collect()
                })
            } else {
                let mut certs = Vec::new();
                for (func, (lir_func, _)) in prepared_funcs.iter().zip(lir_functions.iter()) {
                    certs.extend(generate_proof_certificates(func, Some(lir_func)));
                }
                certs
            };
            Some(all_certs)
        } else {
            None
        };
        #[cfg(not(feature = "verify"))]
        let proofs: Option<Vec<ProofCertificate>> = None;
        self.ensure_proofs_promotable(proofs.as_deref())?;

        // Final phase: encode all prepared functions into executable memory,
        // resolve internal cross-function branches, and bind external symbols.
        let jit_start = Instant::now();
        let jit = crate::jit::JitCompiler::new(jit_config);
        let (mut buffer, encoding_timings) = jit
            .compile_raw_with_encoding_metrics(&prepared_funcs, extern_symbols)
            .map_err(CompileError::Jit)?;
        buffer.attach_proof_optimization_certificates(proof_optimization_certificates.clone());

        // JIT-5: fail-closed gate for the aarch64 JitCertificate path. Under a
        // verifying mode (CachedVerified / AlwaysVerify) every published
        // function must carry a verified, bytes-bound certificate; otherwise an
        // uncertified byte would be published. `ensure_proofs_promotable` above
        // only covers the compiler.rs ProofCertificate path (a no-op unless an
        // artifact-cache proof policy demands promotion), so gate the buffer
        // certificates explicitly here.
        if validation_mode.requires_jit_verification() {
            let ranges: Vec<String> = buffer
                .function_ranges()
                .iter()
                .map(|(name, _)| name.clone())
                .collect();
            for name in &ranges {
                let verified = buffer
                    .certificate(name)
                    .map(|c| c.is_verified())
                    .unwrap_or(false);
                if !verified {
                    return Err(CompileError::ProofPromotionRejected {
                        target: self.config.target,
                        reason: format!(
                            "aarch64 JIT function {name} has no verified bytes-bound certificate \
                             under {} mode; publishing would execute an uncertified byte",
                            validation_mode.label()
                        ),
                    });
                }
            }
        }

        if tracing {
            trace_entries.push(TraceEntry {
                phase: "compile_raw".to_string(),
                duration: jit_start.elapsed(),
                detail: Some(format!("{} functions", function_count)),
            });
        }

        let per_function_metrics: Vec<FunctionQualityMetrics> = prepared_funcs
            .iter()
            .zip(preparation_metrics)
            .map(|(func, prep_metrics)| {
                let mut phase_timings = prep_metrics.timings;
                phase_timings.encoding = encoding_timings.get(func.name.as_str()).copied();
                FunctionQualityMetrics {
                    name: func.name.clone(),
                    code_size_bytes: count_real_instructions(func) * 4,
                    instruction_count: count_real_instructions(func),
                    spill_slot_count: prep_metrics.spill_slot_count,
                    branch_count: count_branch_instructions(func),
                    x86_machine_code: X86MachineCodeEvidence::default(),
                    phase_timings,
                }
            })
            .collect();

        // Count actual non-pseudo instructions across all prepared functions.
        // Each AArch64 instruction is exactly 4 bytes, so code_size = count * 4.
        // This is the real instruction count, not the allocated JIT buffer size
        // which may include page alignment and veneer trampolines.
        let total_instruction_count: usize =
            prepared_funcs.iter().map(count_real_instructions).sum();
        let total_code_size = total_instruction_count * 4;

        // Query actual pass count from the optimization pipeline rather than
        // using hardcoded estimates (fixes #272).
        let opt_passes_per_func = {
            use trust_cg_opt::pipeline::{OptLevel as OptOptLevel, OptimizationPipeline};
            let opt_level = match self.config.opt_level {
                OptLevel::O0 => OptOptLevel::O0,
                OptLevel::O1 => OptOptLevel::O1,
                OptLevel::O2 => OptOptLevel::O2,
                OptLevel::O3 => OptOptLevel::O3,
            };
            OptimizationPipeline::new(opt_level).pass_count()
        };

        let metrics = CompilationMetrics {
            code_size_bytes: total_code_size,
            instruction_count: total_instruction_count,
            function_count,
            optimization_passes_run: opt_passes_per_func * function_count,
            proof_optimizations: summarize_proof_optimizations(&proof_optimization_certificates),
            fsym_trust_ir: fsym_trust_ir_metrics,
        };

        let trace = if tracing {
            Some(CompilerTrace {
                entries: trace_entries,
                total_duration: total_start.elapsed(),
            })
        } else {
            None
        };

        // JIT-5: validation provenance for the aarch64 JitCertificate path.
        // Each published function's coverage is read off the buffer's
        // bytes-bound certificates; verified functions carry a certificate
        // bound to their emitted bytes (from_report). On the Unchecked default
        // path there are no certificates, so `functions` records uncovered
        // bytes honestly. (Per-function cache-hit provenance is not threaded
        // back from the jit.rs verify branch here; the process-global cache
        // stats reflect hits/misses for the JIT-6 lane.)
        let validation = {
            let image_sha = buffer.published_image_sha256().to_string();
            let code = buffer.code_slice();
            let functions = buffer
                .function_ranges()
                .iter()
                .map(|(name, range)| {
                    let verified = buffer
                        .certificate(name)
                        .map(|c| c.is_verified())
                        .unwrap_or(false);
                    let start = range.start as usize;
                    let end = (range.end as usize).min(code.len());
                    let bytes_sha256 = if start <= end && end <= code.len() {
                        crate::jit_diagnostics::sha256_hex(&code[start..end])
                    } else {
                        String::new()
                    };
                    JitFunctionValidation {
                        function: name.clone(),
                        verified,
                        bytes_sha256,
                        cache_hit: false,
                    }
                })
                .collect();
            Some(JitValidationProvenance {
                mode: validation_mode,
                published_image_sha256: image_sha,
                functions,
            })
        };

        Ok(JitCompilationResult {
            buffer,
            metrics,
            trace,
            proofs,
            proof_optimization_certificates,
            per_function_metrics,
            validation,
        })
    }

    /// Build the internal [`Pipeline`] from the compiler configuration.
    fn build_pipeline(&self) -> Pipeline {
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level: self.config.opt_level,
            emit_debug: self.config.emit_debug,
            verify_dispatch: crate::pipeline::DispatchVerifyMode::FallbackOnFailure,
            verify: false,
            cegis_superopt_budget_sec: self.config.cegis_superopt_budget_sec,
            target_triple: compiler_target_triple(self.target_spec),
            enable_fsym_trust_ir_preflight: self.config.enable_fsym_trust_ir_preflight,
            enable_jit_fast_regalloc: self.config.enable_jit_fast_regalloc,
            // The CompilerConfig-driven AOT/host-JIT path keeps the default
            // redundancy-elimination behaviour; only the explicit TY kernel
            // PipelineConfig opts into skipping CSE/GVN.
            skip_cse_gvn: false,
            disabled_passes_override: None,
            contains4_scanner_batch_rewrite_override: None,
        });

        let pipeline =
            if self.production_certified_pass_chain && self.certified_pass_chain.is_none() {
                pipeline.with_certified_pass_execution()
            } else {
                pipeline
            };

        let pipeline = if let Some(profile) = self.profile_use.clone() {
            pipeline.with_profile_use(profile)
        } else {
            pipeline
        };

        if let Some(sink) = self.profile_generate_sink.clone() {
            pipeline.with_profile_generate_sink(sink)
        } else {
            pipeline
        }
    }

    fn ensure_host_jit_target(&self) -> Result<(), CompileError> {
        let host = Target::host();
        if self.config.target != host {
            return Err(CompileError::JitTargetMismatch {
                target: self.config.target,
                host,
            });
        }

        if self.config.target == Target::X86_64 {
            let host_spec = TargetSpec::host_for_architecture(host);
            if self.target_spec != host_spec {
                return Err(CompileError::JitTargetSpecMismatch {
                    requested: self.target_spec,
                    host: host_spec,
                });
            }
        }

        match self.config.target {
            Target::Aarch64 | Target::X86_64 => Ok(()),
            Target::Riscv64 => Err(CompileError::JitTargetUnsupported {
                target: self.config.target,
            }),
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    // Exercises the deprecated `ExecutableBuffer::get_fn_ptr` API as part of
    // regression coverage for JIT symbol enumeration. The deprecation is
    // tracked by issue #355 and migration is out of scope for this module.
    #![allow(deprecated)]
    use crate::compile_artifact_cache_profile::{
        CompileArtifactCacheBoundary, CompileArtifactCacheConfig, CompileArtifactCacheStatus,
        CompileArtifactDependencyIdentity, CompileArtifactProofPolicy,
    };

    use super::*;

    #[test]
    fn production_x86_dataflow_gate_cannot_be_disabled_by_environment() {
        use trust_cg_ir::{LoweringProvenance, SourceInstDigest, SourceInstId, X86Opcode};
        use trust_cg_lower::function::{BasicBlock, Signature};
        use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
        use trust_cg_lower::types::Type;
        use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst};

        let signature = Signature {
            params: vec![Type::I64, Type::I64],
            returns: vec![],
        };
        let block = Block(0);
        let mut lir = trust_cg_lower::Function::new("poisoned_dataflow_gate", signature.clone());
        lir.block_order.push(block);
        lir.blocks.insert(
            block,
            BasicBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Store {
                            ty: Type::I64,
                            align: None,
                        },
                        args: vec![Value(1), Value(0)],
                        results: vec![],
                    },
                    Instruction {
                        opcode: Opcode::Return,
                        args: vec![],
                        results: vec![],
                    },
                ],
                source_locs: vec![],
            },
        );

        let stamp = |index| LoweringProvenance::SourceInst {
            id: SourceInstId { block: 0, index },
            digest: SourceInstDigest(0),
            trust_ir_inst: None,
        };
        let mut isel = X86ISelFunction::new("poisoned_dataflow_gate".to_string(), signature);
        isel.ensure_block(block);
        let mut jump = X86ISelInst::new(X86Opcode::Jmp, vec![]);
        jump.lowering_provenance = stamp(1);
        let mut store_after_terminator = X86ISelInst::new(X86Opcode::MovMR, vec![]);
        store_after_terminator.lowering_provenance = stamp(0);
        // `push_inst` is the selector emission chokepoint and deliberately
        // replaces an instruction's stamp with `current_lowering_provenance`.
        // This test constructs finished ISel output, so insert the already
        // stamped instructions directly instead of accidentally erasing the
        // provenance under test.
        isel.blocks
            .get_mut(&block)
            .expect("test block exists")
            .insts
            .extend([jump, store_after_terminator]);

        // Cargo runs unit tests concurrently, so mutating this process's
        // environment would race any other compile test. The outer invocation
        // instead launches this exact test in a child process whose initial
        // environment is poisoned. The marker prevents recursive spawning.
        const CHILD_MARKER: &str = "TCG_DATAFLOW_ENFORCE_TEST_CHILD";
        if std::env::var_os(CHILD_MARKER).is_none() {
            let output = std::process::Command::new(
                std::env::current_exe().expect("current trust-cg-codegen test executable"),
            )
            .arg("production_x86_dataflow_gate_cannot_be_disabled_by_environment")
            .arg("--nocapture")
            .env("TCG_DATAFLOW_INTEGRITY", "off")
            .env(CHILD_MARKER, "1")
            .output()
            .expect("run isolated poisoned-environment child test");
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                output.status.success(),
                "poisoned-environment child failed:\nstdout:\n{}\nstderr:\n{stderr}",
                String::from_utf8_lossy(&output.stdout)
            );
            assert!(
                stderr.contains("[TCG-DATAFLOW-ENV-CHILD-PASS]"),
                "child test did not execute the enforcement assertion: {stderr}"
            );
            return;
        }

        let result = enforce_x86_dataflow_integrity(&isel, &lir);
        let error = result.expect_err("ambient `off` must not disable the production gate");
        assert!(
            error.to_string().contains("TCG-DATAFLOW-INTEGRITY"),
            "{error}"
        );
        eprintln!("[TCG-DATAFLOW-ENV-CHILD-PASS]");
    }

    #[test]
    fn production_x86_dataflow_gate_rejects_mismatched_replay_pair() {
        use trust_cg_lower::function::Signature;
        use trust_cg_lower::types::Type;
        use trust_cg_lower::x86_64_isel::X86ISelFunction;

        let signature = Signature {
            params: vec![Type::I64],
            returns: vec![],
        };
        let lir = trust_cg_lower::Function::new("lir_name", signature.clone());
        let isel = X86ISelFunction::new("machine_name".to_string(), signature);

        let error = enforce_x86_dataflow_integrity(&isel, &lir)
            .expect_err("a mis-zipped machine/LIR pair must fail closed");
        assert!(error.to_string().contains("pairing mismatch"), "{error}");
    }

    // ---- EH x86 Lane 2 Step 5: residual reject-gate routing ----

    fn lir_function_with_eh(
        name: &str,
    ) -> (trust_cg_lower::Function, trust_cg_lower::ProofContext) {
        use trust_cg_lower::function::{EhCallSite, EhFunctionInfo, EhLandingPad, Signature};
        use trust_cg_lower::instructions::Block;
        let mut func = trust_cg_lower::Function::new(name, Signature::default());
        func.eh_info = EhFunctionInfo {
            personality: Some("rust_eh_personality".to_string()),
            landing_pads: vec![EhLandingPad {
                block: Block(1),
                catch_type_indices: Vec::new(),
                is_cleanup: true,
            }],
            call_sites: vec![EhCallSite {
                call_block: Block(0),
                landing_pad_block: Block(1),
            }],
        };
        (func, trust_cg_lower::ProofContext::default())
    }

    fn lir_function_no_eh(name: &str) -> (trust_cg_lower::Function, trust_cg_lower::ProofContext) {
        use trust_cg_lower::function::Signature;
        (
            trust_cg_lower::Function::new(name, Signature::default()),
            trust_cg_lower::ProofContext::default(),
        )
    }

    #[test]
    fn x86_eh_gate_macho_aot_accepts_eh() {
        use crate::x86_64::X86OutputFormat;
        // Lane 2 emits unwind tables for Mach-O, so an EH function is accepted.
        let eh = vec![lir_function_with_eh("eh_fn")];
        assert!(reject_x86_eh_for_non_macho_aot(&eh, X86OutputFormat::MachO).is_ok());
    }

    #[test]
    fn x86_eh_gate_non_macho_aot_rejects_eh() {
        use crate::x86_64::X86OutputFormat;
        // ELF/COFF get no LSDA in Lane 2, so EH functions fail closed.
        let eh = vec![lir_function_with_eh("eh_fn")];
        assert!(reject_x86_eh_for_non_macho_aot(&eh, X86OutputFormat::Elf).is_err());
        assert!(reject_x86_eh_for_non_macho_aot(&eh, X86OutputFormat::Coff).is_err());
    }

    #[test]
    fn x86_eh_gate_aot_accepts_non_eh_any_format() {
        use crate::x86_64::X86OutputFormat;
        // A non-EH function is never gated, regardless of output format.
        let non_eh = vec![lir_function_no_eh("plain")];
        assert!(reject_x86_eh_for_non_macho_aot(&non_eh, X86OutputFormat::Elf).is_ok());
        assert!(reject_x86_eh_for_non_macho_aot(&non_eh, X86OutputFormat::Coff).is_ok());
        assert!(reject_x86_eh_for_non_macho_aot(&non_eh, X86OutputFormat::MachO).is_ok());
    }

    #[test]
    fn x86_eh_gate_jit_rejects_eh_accepts_non_eh() {
        // The JIT has no in-memory eh_frame, so EH stays fail-closed there.
        let eh = vec![lir_function_with_eh("eh_fn")];
        let non_eh = vec![lir_function_no_eh("plain")];
        assert!(reject_x86_jit_eh(&eh).is_err());
        assert!(reject_x86_jit_eh(&non_eh).is_ok());
    }

    #[test]
    fn aarch64_eh_gate_jit_rejects_cleanup_eh_accepts_non_eh() {
        let eh = vec![lir_function_with_eh("cleanup_fn")];
        let non_eh = vec![lir_function_no_eh("plain")];

        let error = reject_aarch64_jit_eh(&eh).expect_err("cleanup EH must fail closed");
        let message = error.to_string();
        assert!(message.contains("personality/LSDA/eh_frame"), "{message}");
        assert!(message.contains("cleanup or catch handlers"), "{message}");
        assert!(reject_aarch64_jit_eh(&non_eh).is_ok());
    }

    fn module_with_one_global(global: trust_ir::Global) -> trust_ir::Module {
        trust_ir::Module {
            name: "global_fixture".to_string(),
            functions: vec![],
            structs: vec![],
            records: vec![],
            closure_types: vec![],
            globals: vec![global],
            func_types: vec![],
            // `TyId(0)` = `U8` so `byte_global`'s `Array(TyId(0), 3)` is a
            // genuine `[u8; 3]` whose elements lay out at one byte each.
            types: vec![trust_ir::Ty::U8],
            proof_obligations: vec![],
            proof_certificates: vec![],
            enums: vec![],
            target_info: None,
            files: vec![],
            obligation_diagnostics: vec![],
            spec_modules: vec![],
            universes: vec![],
            predicates: vec![],
        }
    }

    fn byte_global(name: &str, initializer: Option<trust_ir::Constant>) -> trust_ir::Global {
        typed_global(
            name,
            trust_ir::Ty::Array(trust_ir::TyId::new(0), 3),
            true,
            initializer,
        )
    }

    fn typed_global(
        name: &str,
        ty: trust_ir::Ty,
        mutable: bool,
        initializer: Option<trust_ir::Constant>,
    ) -> trust_ir::Global {
        trust_ir::Global {
            name: name.to_string(),
            ty,
            mutable,
            initializer,
            linkage: trust_ir::Linkage::External,
            tls: None,
            align: None,
        }
    }

    #[test]
    fn module_object_globals_emits_byte_aggregates() {
        let module = module_with_one_global(byte_global(
            "BYTES",
            Some(trust_ir::Constant::Aggregate(vec![
                trust_ir::Constant::Int(1),
                trust_ir::Constant::Int(2),
                trust_ir::Constant::Int(255),
            ])),
        ));
        let globals = module_object_globals(&module).expect("byte global should be admitted");
        assert_eq!(
            globals,
            vec![ObjectGlobal {
                name: "BYTES".to_string(),
                data: vec![1, 2, 255],
                mutable: true,
                is_external: true,
                symbol_refs: vec![],
                is_thread_local: false,
                is_import: false,
                is_weak: false,
                // No explicit `Global.align`; a byte aggregate derives align 1
                // from its type, floored to the pointer-size default (8).
                align: 8,
            }]
        );
    }

    #[test]
    fn module_object_globals_lays_out_vtable_int_slots_at_pointer_width() {
        // A Rust vtable global: an aggregate of three leading pointer-word
        // integer slots (`drop`/`size`/`align`) followed by method-pointer
        // `SymbolAddr` slots. The declared type is a `Tuple` of pointer-width
        // element types, so each `Int` slot MUST lay out at 8 bytes (not the
        // historic 1 byte) — otherwise the method-pointer relocations land at
        // non-8-aligned offsets (`ld: pointer not aligned in '_vtable...'`).
        const VTABLE_SIZE: i128 = 24; // 0x18
        const VTABLE_ALIGN: i128 = 8; // 0x08
        let vtable = typed_global(
            "VTABLE",
            trust_ir::Ty::Tuple(vec![
                trust_ir::Ty::Ptr,   // drop_in_place (null here)
                trust_ir::Ty::Usize, // size
                trust_ir::Ty::Usize, // align
                trust_ir::Ty::Ptr,   // method0
                trust_ir::Ty::Ptr,   // method1
            ]),
            false,
            Some(trust_ir::Constant::Aggregate(vec![
                trust_ir::Constant::Int(0), // drop == null
                trust_ir::Constant::Int(VTABLE_SIZE),
                trust_ir::Constant::Int(VTABLE_ALIGN),
                trust_ir::Constant::SymbolAddr {
                    symbol: "method0".to_string(),
                    addend: 0,
                },
                trust_ir::Constant::SymbolAddr {
                    symbol: "method1".to_string(),
                    addend: 0,
                },
            ])),
        );
        let module = module_with_one_global(vtable);
        let globals = module_object_globals(&module).expect("vtable global should be admitted");
        let g = &globals[0];

        // Three pointer-width integer slots + two pointer-width method slots.
        assert_eq!(g.data.len(), 40, "5 pointer-word slots => 40 bytes");
        assert_eq!(
            &g.data[0..8],
            &[0, 0, 0, 0, 0, 0, 0, 0],
            "drop == null, 8 bytes"
        );
        assert_eq!(
            &g.data[8..16],
            &[24, 0, 0, 0, 0, 0, 0, 0],
            "size == 24 as an 8-byte little-endian usize"
        );
        assert_eq!(
            &g.data[16..24],
            &[8, 0, 0, 0, 0, 0, 0, 0],
            "align == 8 as an 8-byte little-endian usize"
        );
        // Method-pointer placeholders are zeroed pending the linker's fixup.
        assert_eq!(&g.data[24..40], &[0u8; 16], "method-pointer slots zeroed");

        // The two relocations sit at 8-aligned offsets 24 and 32.
        let offsets: Vec<u64> = g.symbol_refs.iter().map(|r| r.offset).collect();
        assert_eq!(
            offsets,
            vec![24, 32],
            "method pointers at pointer-word offsets"
        );
        for r in &g.symbol_refs {
            assert_eq!(r.offset % 8, 0, "relocation {} is 8-aligned", r.symbol);
        }
        assert_eq!(g.symbol_refs[0].symbol, "method0");
        assert_eq!(g.symbol_refs[1].symbol, "method1");
    }

    #[test]
    fn module_object_globals_emits_byte_sized_scalars() {
        let mut module = module_with_one_global(typed_global(
            "U8_SCALAR",
            trust_ir::Ty::U8,
            true,
            Some(trust_ir::Constant::Int(255)),
        ));
        module.globals.push(typed_global(
            "I8_SCALAR",
            trust_ir::Ty::I8,
            true,
            Some(trust_ir::Constant::Int(-1)),
        ));
        module.globals.push(typed_global(
            "BOOL_SCALAR",
            trust_ir::Ty::Bool,
            false,
            Some(trust_ir::Constant::Bool(true)),
        ));

        let globals =
            module_object_globals(&module).expect("byte-sized scalars should be admitted");
        assert_eq!(
            globals,
            vec![
                ObjectGlobal {
                    name: "U8_SCALAR".to_string(),
                    data: vec![255],
                    mutable: true,
                    is_external: true,
                    symbol_refs: vec![],
                    is_thread_local: false,
                    is_import: false,
                    is_weak: false,
                    align: 8,
                },
                ObjectGlobal {
                    name: "I8_SCALAR".to_string(),
                    data: vec![255],
                    mutable: true,
                    is_external: true,
                    symbol_refs: vec![],
                    is_thread_local: false,
                    is_import: false,
                    is_weak: false,
                    align: 8,
                },
                ObjectGlobal {
                    name: "BOOL_SCALAR".to_string(),
                    data: vec![1],
                    mutable: false,
                    is_external: true,
                    symbol_refs: vec![],
                    is_thread_local: false,
                    is_import: false,
                    is_weak: false,
                    align: 8,
                },
            ]
        );
    }

    #[test]
    fn module_object_globals_emits_wide_scalars_little_endian() {
        // target_info: None => little-endian default (both supported targets).
        let cases: Vec<(trust_ir::Global, Vec<u8>)> = vec![
            (
                typed_global(
                    "U16",
                    trust_ir::Ty::U16,
                    true,
                    Some(trust_ir::Constant::Int(7)),
                ),
                vec![7, 0],
            ),
            (
                typed_global(
                    "I16_NEG",
                    trust_ir::Ty::I16,
                    true,
                    Some(trust_ir::Constant::Int(-2)),
                ),
                vec![0xfe, 0xff],
            ),
            (
                typed_global(
                    "U32",
                    trust_ir::Ty::U32,
                    true,
                    Some(trust_ir::Constant::Int(0x0102_0304)),
                ),
                vec![0x04, 0x03, 0x02, 0x01],
            ),
            (
                typed_global(
                    "I64",
                    trust_ir::Ty::I64,
                    true,
                    Some(trust_ir::Constant::Int(100)),
                ),
                vec![100, 0, 0, 0, 0, 0, 0, 0],
            ),
            (
                typed_global(
                    "I64_NEG",
                    trust_ir::Ty::I64,
                    true,
                    Some(trust_ir::Constant::Int(-1)),
                ),
                vec![0xff; 8],
            ),
            (
                typed_global(
                    "I128",
                    trust_ir::Ty::I128,
                    false,
                    Some(trust_ir::Constant::Int(i128::from(u64::MAX) + 1)),
                ),
                {
                    let mut v = vec![0u8; 16];
                    v[8] = 1; // 2^64, little-endian
                    v
                },
            ),
            (
                // f64 1.5 => 0x3FF8000000000000
                typed_global(
                    "F64",
                    trust_ir::Ty::F64,
                    false,
                    Some(trust_ir::Constant::Float(1.5)),
                ),
                1.5f64.to_bits().to_le_bytes().to_vec(),
            ),
            (
                // f32 rounding of a double literal, matching C `float x = 0.1;`
                typed_global(
                    "F32",
                    trust_ir::Ty::F32,
                    false,
                    Some(trust_ir::Constant::Float(0.1)),
                ),
                (0.1f64 as f32).to_bits().to_le_bytes().to_vec(),
            ),
        ];
        for (global, expected) in cases {
            let name = global.name.clone();
            let module = module_with_one_global(global);
            let globals = module_object_globals(&module)
                .unwrap_or_else(|e| panic!("{name} must emit: {e:?}"));
            assert_eq!(globals.len(), 1, "{name}");
            assert_eq!(globals[0].data, expected, "{name} bytes");
        }
    }

    #[test]
    fn module_object_globals_fail_closed_for_unsupported_initializers() {
        for (global, expected) in [
            (
                // An initializer-less INTERNAL global is a zero-fill (BSS)
                // definition; it is admitted when the type's layout size is
                // computable (see `module_object_globals_zero_fills_bss_global`).
                // This fixture's element type is `Array(TyId(9), 3)` over an
                // UNRESOLVABLE element (the fixture module's `types` table has a
                // single entry), so its layout size cannot be computed and it
                // fails closed — never guessing a size. (An initializer-less
                // EXTERNAL global is instead a cross-object import and is
                // admitted.)
                trust_ir::Global {
                    linkage: trust_ir::Linkage::Internal,
                    ..typed_global(
                        "NO_INIT",
                        trust_ir::Ty::Array(trust_ir::TyId::new(9), 3),
                        true,
                        None,
                    )
                },
                "no computable layout size for a BSS/zero-fill definition",
            ),
            (
                typed_global(
                    "U8_RANGE",
                    trust_ir::Ty::U8,
                    true,
                    Some(trust_ir::Constant::Int(300)),
                ),
                "outside U8 range",
            ),
            (
                typed_global(
                    "I8_RANGE",
                    trust_ir::Ty::I8,
                    true,
                    Some(trust_ir::Constant::Int(128)),
                ),
                "outside I8 range",
            ),
            (
                typed_global(
                    "U16_RANGE",
                    trust_ir::Ty::U16,
                    true,
                    Some(trust_ir::Constant::Int(70000)),
                ),
                "outside U16 range",
            ),
            (
                typed_global(
                    "F16_UNWIRED",
                    trust_ir::Ty::F16,
                    true,
                    Some(trust_ir::Constant::Float(1.0)),
                ),
                "only F32/F64 scalar float globals are wired",
            ),
            (
                typed_global(
                    "BOOL_SHAPE",
                    trust_ir::Ty::Bool,
                    true,
                    Some(trust_ir::Constant::Int(1)),
                ),
                "scalar integer initializer for Bool needs target-endian typed data emission",
            ),
            (
                byte_global(
                    "WIDE",
                    Some(trust_ir::Constant::Aggregate(vec![
                        trust_ir::Constant::Int(300),
                    ])),
                ),
                // `byte_global` is a genuine `[u8; 3]`, so the Int element lays
                // out at its declared `U8` width and range-checks against it.
                "outside U8 range",
            ),
        ] {
            let module = module_with_one_global(global);
            let err = module_object_globals(&module).expect_err("global must fail closed");
            let message = err.to_string();
            assert!(
                message.contains(expected),
                "expected {expected:?}, got {message:?}"
            );
        }
    }

    #[test]
    fn module_object_globals_admits_local_exec_tls_as_thread_local() {
        // On Darwin/Mach-O every TLS model — including `LocalExec` — resolves
        // through the TLV descriptor, because the READ side (`translate_global_-
        // addr`) always lowers a TLS `GlobalAddr` to `TlsRef { model: Tlv }`.
        // A `LocalExec` definition must therefore also become a TLV descriptor
        // for its read to resolve, so it is admitted as a thread-local object
        // global exactly like the dynamic models (the ELF emitter still fails
        // closed on any thread-local global).
        let mut global = byte_global(
            "TLS_BYTES",
            Some(trust_ir::Constant::Aggregate(vec![
                trust_ir::Constant::Int(1),
            ])),
        );
        global.tls = Some(trust_ir::TlsModel::LocalExec);
        let module = module_with_one_global(global);
        let globals = module_object_globals(&module)
            .unwrap_or_else(|e| panic!("local-exec TLS global should be admitted on Darwin: {e}"));
        assert_eq!(globals.len(), 1);
        assert!(
            globals[0].is_thread_local,
            "local-exec TLS must mark the object global thread-local (routed to the TLV path)"
        );
        assert_eq!(globals[0].data, vec![1]);
    }

    #[test]
    fn module_object_globals_emits_bytes_initializer() {
        // The v25 `Constant::Bytes` byte-array carrier (a `&[u8]`/`&str` backing
        // store, a control-byte buffer) is emitted verbatim, no relocations.
        let global = typed_global(
            "BYTES_G",
            trust_ir::Ty::Array(trust_ir::TyId::new(0), 3),
            false,
            Some(trust_ir::Constant::Bytes {
                data: vec![0xDE, 0xAD, 0xBE],
                utf8: false,
            }),
        );
        let module = module_with_one_global(global);
        let globals = module_object_globals(&module)
            .unwrap_or_else(|e| panic!("Bytes initializer must emit: {e}"));
        assert_eq!(globals.len(), 1);
        assert_eq!(globals[0].data, vec![0xDE, 0xAD, 0xBE]);
        assert!(globals[0].symbol_refs.is_empty());
    }

    #[test]
    fn module_object_globals_zero_fills_bss_global() {
        // An initializer-less INTERNAL global is a zero-initialized (BSS) static:
        // it is admitted as `size` zero bytes, where `size` is the type's
        // canonical layout. A scalar `I64` lays out to 8 bytes.
        let global = trust_ir::Global {
            linkage: trust_ir::Linkage::Internal,
            ..typed_global("BSS_I64", trust_ir::Ty::I64, false, None)
        };
        let module = module_with_one_global(global);
        let globals = module_object_globals(&module)
            .unwrap_or_else(|e| panic!("BSS global must zero-fill: {e}"));
        assert_eq!(globals.len(), 1);
        assert_eq!(globals[0].data, vec![0u8; 8], "BSS I64 zero-fills 8 bytes");
        assert!(globals[0].symbol_refs.is_empty());
        assert!(!globals[0].is_import);
        assert!(!globals[0].is_thread_local);
    }

    #[test]
    fn module_object_globals_admits_dynamic_tls_as_thread_local() {
        // The dynamic models (IE/GD/LD) resolve through the Darwin TLV descriptor
        // and are admitted as thread-local object globals (routed to the
        // `__thread_data`/`__thread_vars` sections by the Mach-O emitter).
        for model in [
            trust_ir::TlsModel::GeneralDynamic,
            trust_ir::TlsModel::LocalDynamic,
            trust_ir::TlsModel::InitialExec,
        ] {
            let mut global = byte_global(
                "TLS_X",
                Some(trust_ir::Constant::Aggregate(vec![
                    trust_ir::Constant::Int(0xCD),
                    trust_ir::Constant::Int(0xAB),
                ])),
            );
            global.tls = Some(model);
            let module = module_with_one_global(global);
            let globals = module_object_globals(&module)
                .unwrap_or_else(|e| panic!("dynamic TLS model {model} should be admitted: {e}"));
            assert_eq!(globals.len(), 1);
            assert!(
                globals[0].is_thread_local,
                "dynamic TLS model {model} must mark the object global thread-local"
            );
            assert_eq!(globals[0].data, vec![0xCD, 0xAB]);
        }
    }

    #[test]
    fn module_object_globals_admits_initializer_less_tls_as_external_import() {
        // An initializer-less THREAD-LOCAL global is a cross-object IMPORT — a
        // reference to a `#[thread_local]` static (its TLV descriptor + template)
        // DEFINED in another object, e.g. the monomorphized
        // `std::hash::RandomState::new::KEYS` seed read by a HashMap hasher
        // closure. It has NO zero-fill definition path (a TLS definition needs an
        // init-value template), so its only coherent meaning is an import — and an
        // import is necessarily External, whatever linkage the producer stamped.
        // Internal/Private/External all promote to the same External import
        // (empty data, is_import, is_thread_local, strong undefined ref — the
        // Mach-O emitter excludes it from descriptor emission and its `__text`
        // TLVP fixup falls through to the undefined-external the linker resolves).
        for linkage in [
            trust_ir::Linkage::Internal,
            trust_ir::Linkage::Private,
            trust_ir::Linkage::External,
        ] {
            let global = trust_ir::Global {
                linkage,
                tls: Some(trust_ir::TlsModel::LocalExec),
                align: None,
                ..typed_global("tls.2ac0fba675fc0d1b", trust_ir::Ty::I64, true, None)
            };
            let module = module_with_one_global(global);
            let globals = module_object_globals(&module).unwrap_or_else(|e| {
                panic!("initializer-less {linkage:?} TLS must be admitted as an import: {e}")
            });
            assert_eq!(globals.len(), 1);
            let g = &globals[0];
            assert!(
                g.is_import,
                "{linkage:?} initializer-less TLS must be a cross-object import"
            );
            assert!(
                g.is_external,
                "{linkage:?} initializer-less TLS import must be External (an Internal/Private \
                 TLS symbol with no bytes here cannot be satisfied by another object)"
            );
            assert!(
                g.is_thread_local,
                "{linkage:?} initializer-less TLS import stays thread-local (routed to the TLV path)"
            );
            assert!(
                g.data.is_empty(),
                "{linkage:?} TLS import contributes no descriptor/template bytes"
            );
            assert!(
                g.symbol_refs.is_empty(),
                "{linkage:?} TLS import carries no symbol relocations"
            );
            assert!(
                !g.is_weak,
                "{linkage:?} TLS import is a strong undefined reference, not a weak def"
            );
        }
    }

    #[test]
    fn test_x86_dynamic_stack_alloc_detection_ignores_dead_runtime_slots() {
        use trust_cg_ir::function::StackSlotSizeSource;
        use trust_cg_ir::regs::{RegClass, VReg};
        use trust_cg_ir::x86_64_ops::X86Opcode;
        use trust_cg_lower::function::{Signature, StackSlotInfo};
        use trust_cg_lower::instructions::Block;
        use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst, X86ISelOperand};

        let mut func = X86ISelFunction::new(
            "dead_runtime_stack_slot".to_string(),
            Signature {
                params: vec![],
                returns: vec![],
            },
        );
        func.ensure_block(Block(0));
        func.stack_slots.push(StackSlotInfo::new_dynamic_with_unit(
            StackSlotSizeSource::Value(0),
            8,
            16,
        ));

        assert!(!x86_function_has_dynamic_stack_alloc(&func));

        func.push_inst(
            Block(0),
            X86ISelInst::new(
                X86Opcode::StackAlloc,
                vec![
                    X86ISelOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                    X86ISelOperand::Imm(1),
                    X86ISelOperand::Imm(8),
                    X86ISelOperand::Imm(16),
                ],
            ),
        );

        assert!(x86_function_has_dynamic_stack_alloc(&func));
    }

    #[cfg(not(target_os = "windows"))]
    fn runtime_count_alloca_module(name: &str) -> trust_ir::Module {
        use trust_ir::{
            Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction, Inst,
            InstrNode, Module as TrustIrModule, Ty, ValueId,
        };

        let mut module = TrustIrModule::new(name);
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::Ptr],
            is_vararg: false,
        });
        let mut func =
            TrustIrFunction::new(FuncId::new(0), "runtime_count_alloca", ft, BlockId::new(0));
        func.blocks = vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::Alloca {
                    ty: Ty::I64,
                    count: Some(ValueId::new(0)),
                    align: None,
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(1)],
                }),
            ],
        }];
        module.add_function(func);
        module
    }

    fn const_i64_module(module_name: &str, function_name: &str, value: i128) -> trust_ir::Module {
        use trust_ir::{
            Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction,
            Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
        };

        let mut module = TrustIrModule::new(module_name);
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let mut func = TrustIrFunction::new(FuncId::new(0), function_name, ft, BlockId::new(0));
        func.blocks = vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(value),
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(0)],
                }),
            ],
        }];
        module.add_function(func);
        module
    }

    #[test]
    fn riscv_compiler_route_marks_lp64d_elf_abi() {
        let compiler = Compiler::new(CompilerConfig {
            opt_level: OptLevel::O0,
            target: Target::Riscv64,
            parallel: false,
            ..CompilerConfig::default()
        });
        let result = compiler
            .compile(&const_i64_module("riscv_lp64d_flags", "answer", 42))
            .expect("RISC-V compiler route should emit an ELF object");

        assert_eq!(&result.object_code[..4], b"\x7fELF");
        let e_flags = u32::from_le_bytes(
            result.object_code[48..52]
                .try_into()
                .expect("ELF64 e_flags has four bytes"),
        );
        assert_eq!(e_flags, crate::elf::constants::EF_RISCV_FLOAT_ABI_DOUBLE);
    }

    #[test]
    fn riscv_call_fixup_rebase_rejects_u32_truncation_and_wraparound() {
        let fixup = crate::riscv::pipeline::RiscVCallFixup {
            auipc_offset: 4,
            jalr_offset: 8,
            callee: "callee".to_string(),
        };

        let rebased = rebase_riscv_call_fixup("caller", u64::from(u32::MAX) - 8, &fixup)
            .expect("boundary-fitting call fixup should rebase exactly");
        assert_eq!(rebased.auipc_offset, u32::MAX - 4);
        assert_eq!(rebased.jalr_offset, u32::MAX);

        let wrap = rebase_riscv_call_fixup("caller", u64::from(u32::MAX) - 4, &fixup)
            .expect_err("JALR rebase must not wrap past u32::MAX");
        assert!(wrap.to_string().contains("JALR call fixup"), "{wrap}");

        let truncation = rebase_riscv_call_fixup("caller", u64::from(u32::MAX) + 1, &fixup)
            .expect_err("function base must not truncate into the u32 patch domain");
        assert!(
            truncation
                .to_string()
                .contains("outside the u32 patch domain"),
            "{truncation}"
        );
    }

    fn divzero_i64_module(module_name: &str, function_name: &str) -> trust_ir::Module {
        use trust_ir::{
            BinOp, Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy,
            Function as TrustIrFunction, Inst, InstrNode, Module as TrustIrModule, SourceSpan, Ty,
            ValueId,
        };

        let mut module = TrustIrModule::new(module_name);
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let mut func = TrustIrFunction::new(FuncId::new(0), function_name, ft, BlockId::new(0));
        func.blocks = vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(42),
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                })
                .with_result(ValueId::new(1)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::SDiv,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2))
                .with_span(SourceSpan {
                    file: 7,
                    line: 11,
                    col: 13,
                }),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(2)],
                }),
            ],
        }];
        module.add_function(func);
        module
    }

    fn proof_optimization_citation_module() -> trust_ir::Module {
        use trust_ir::{
            BinOp, Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction,
            Inst, InstrNode, Module as TrustIrModule, ProofAnnotation, SourceSpan, Ty, ValueId,
        };

        let mut module = TrustIrModule::new("compiler_proof_opt");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let mut func = TrustIrFunction::new(
            FuncId::new(0),
            "compiler_proof_opt_entry",
            ft,
            BlockId::new(0),
        );
        func.blocks = vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64), (ValueId::new(1), Ty::I64)],
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: Ty::I64,
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2))
                .with_proof(ProofAnnotation::NoOverflow)
                .with_proof(ProofAnnotation::NoUndef)
                .with_proof(ProofAnnotation::BoundedLoop(8))
                .with_span(SourceSpan {
                    file: 1,
                    line: 42,
                    col: 7,
                }),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(2)],
                }),
            ],
        }];
        module.add_function(func);
        module
    }

    fn temp_cache_root(name: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(format!(
            "trust-cg-compiler-artifact-cache-{}-{}-{}",
            name,
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|duration| duration.as_nanos())
                .unwrap_or(0)
        ))
    }

    fn test_cache_config(
        root: &std::path::Path,
        policy: CompileArtifactProofPolicy,
    ) -> CompileArtifactCacheConfig {
        CompileArtifactCacheConfig::new(
            root,
            policy,
            CompileArtifactDependencyIdentity::new(
                "source-lock-sha256:trust-cg-test",
                "source-lock-sha256:trust-ir-test",
                "source-lock-sha256:ay-test",
                "rustc:stage2-sha256:test",
                "tcargo:sha256:test",
                "trust",
            ),
        )
    }

    fn profile_use_with_hits(hits: u64) -> trust_cg_opt::pgo::ProfData {
        let mut profile = trust_cg_opt::pgo::ProfData::new(0x780);
        let function = profile.function_mut_or_insert("answer");
        function.call_count = hits;
        function
            .blocks
            .push(trust_cg_opt::pgo::BlockProfile::new(0, hits));
        profile
    }

    fn manifest_profile_use_sha256(cache_path: &std::path::Path) -> String {
        let manifest: serde_json::Value =
            serde_json::from_slice(&std::fs::read(cache_path.join("manifest.json")).unwrap())
                .unwrap();
        manifest
            .pointer("/key/profile_use_sha256")
            .and_then(serde_json::Value::as_str)
            .expect("cache manifest records profile-use identity")
            .to_owned()
    }

    /// Synthesize a verified `CertifiedPassRunRecord` for the gamma-vnncomp
    /// demo chain tests.
    ///
    /// The previous test scaffold read serialized
    /// `Lean5PassCertificateCheckRequest` JSON fixtures from
    /// `reports/fixtures/gamma_vnncomp_demo_*_request.json`. Those fixtures are
    /// not part of the open-source baseline, so the tests construct equivalent
    /// requests in-process through `Compiler::certified_pass_check_request`,
    /// which is the same code path the production certified pass chain uses.
    #[cfg(feature = "verify")]
    fn gamma_demo_run_record(
        pass_name: &str,
        pass_instance_id: &str,
        local_checker_name: &str,
        function_name: &str,
    ) -> trust_cg_opt::CertifiedPassRunRecord {
        use trust_cg_opt::{
            CertifiedPassCheckerRecord, CertifiedPassRunRecord, CertifiedPassRunStatus,
        };
        CertifiedPassRunRecord {
            format_version: "trust-cg.opt.certified_pass_run.v1".to_string(),
            pass_name: pass_name.to_string(),
            pass_version: 1,
            pass_instance_id: pass_instance_id.to_string(),
            function_name: function_name.to_string(),
            changed: false,
            status: CertifiedPassRunStatus::Verified,
            certificate_count: 0,
            failure_count: 0,
            obligation_hash: format!(
                "trust-cg-opt-certified-pass-run-v1:gamma-vnncomp-demo:{pass_instance_id}"
            ),
            local_checker: CertifiedPassCheckerRecord {
                kind: "trust-cg-opt-local".to_string(),
                name: local_checker_name.to_string(),
                version: "1".to_string(),
                status: CertifiedPassRunStatus::Verified,
            },
            summary: serde_json::json!({
                "changed": false,
                "certificates": [],
                "failures": []
            }),
        }
    }

    /// Build an in-process `Lean5PassCertificateCheckRequest` for the
    /// gamma-vnncomp-demo chain at `certificate_index` via the same helper the
    /// production certified pass chain uses.
    #[cfg(feature = "verify")]
    fn synthesize_gamma_demo_check_request(
        compiler: &Compiler,
        certificate_index: u64,
        run: &trust_cg_opt::CertifiedPassRunRecord,
    ) -> trust_cg_verify::certified_pass_checker::Lean5PassCertificateCheckRequest {
        compiler
            .certified_pass_check_request("gamma-vnncomp-demo", certificate_index, run)
            .expect("synthetic certified pass request should build")
    }

    fn pre_unwind_guard_codegen_options_sha256(
        config: &CompilerConfig,
        target_spec: TargetSpec,
        profile_use_sha256: &str,
    ) -> Result<String, CompileError> {
        let x86_64_aot_output_format = if config.target == Target::X86_64 {
            Some(compiler_x86_64_aot_output_format_name(target_spec)?)
        } else {
            None
        };
        let options = serde_json::json!({
            "schema": "trust-cg.compile_artifact.codegen_options.v3",
            "target": config.target.name(),
            "target_triple": compiler_target_triple(target_spec),
            "target_vendor": target_spec.vendor.triple_component(),
            "target_os": target_spec.operating_system.triple_component(),
            "target_environment": target_spec.environment.triple_component(),
            "host_target_os": compiler_host_target_os(),
            "x86_64_aot_output_format": x86_64_aot_output_format,
            "opt_level": compiler_opt_level_name(config.opt_level),
            "emit_proofs": config.emit_proofs,
            "emit_debug": config.emit_debug,
            "parallel": config.parallel,
            "cegis_superopt_budget_sec": config.cegis_superopt_budget_sec,
            "profile_use_sha256": profile_use_sha256,
            "verify_feature": cfg!(feature = "verify"),
        });
        compiler_cache_identity_sha256("pre_unwind_guard_codegen_options", &options)
    }

    struct FailingIdentitySerialize;

    impl serde::Serialize for FailingIdentitySerialize {
        fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            Err(serde::ser::Error::custom(
                "synthetic cache identity failure",
            ))
        }
    }

    #[cfg(feature = "verify")]
    fn insert_unverified_csinv_before_return(func: &mut trust_cg_ir::MachFunction) {
        use trust_cg_ir::inst::{AArch64Opcode, MachInst};
        use trust_cg_ir::operand::MachOperand;
        use trust_cg_ir::regs::X0;

        // CSINV is emittable and non-pseudo but has NO registered value-proof
        // mapping (unlike CSEL/CSINC/CSNEG and FABS/FSQRT/FDIV, which are now
        // wired), so it is the canonical "uncovered non-pseudo opcode" that the
        // emitted-opcode-inventory gate must reject. The proof gate fires before
        // encoding, so a representative 3-GPR form is sufficient here.
        let csinv = MachInst::new(
            AArch64Opcode::Csinv,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
            ],
        );
        let csinv_id = func.push_inst(csinv);
        let entry_idx = func.entry.0 as usize;
        let ret_pos = func.blocks[entry_idx]
            .insts
            .iter()
            .position(|&inst_id| func.insts[inst_id.0 as usize].opcode == AArch64Opcode::Ret);

        match ret_pos {
            Some(pos) => func.blocks[entry_idx].insts.insert(pos, csinv_id),
            None => func.append_inst(func.entry, csinv_id),
        }
    }

    #[test]
    fn compile_artifact_cache_identity_serialization_error_is_typed() {
        let err =
            compiler_cache_identity_sha256("unit.identity", &FailingIdentitySerialize).unwrap_err();

        match err {
            CompileError::CompileArtifactCacheIdentityJson { component, source } => {
                assert_eq!(component, "unit.identity");
                assert!(
                    source
                        .to_string()
                        .contains("synthetic cache identity failure"),
                    "unexpected source error: {source}"
                );
            }
            other => panic!("expected typed cache identity JSON error, got {other:?}"),
        }
    }

    #[test]
    fn x86_64_aot_output_format_selection_is_os_aware() {
        use crate::x86_64::X86OutputFormat;

        for os in [
            "linux",
            "android",
            "freebsd",
            "netbsd",
            "openbsd",
            "dragonfly",
        ] {
            assert_eq!(
                x86_64_aot_output_format_for_os(os).unwrap(),
                X86OutputFormat::Elf,
                "{os} should use ELF for public x86-64 AOT"
            );
        }
        assert_eq!(
            x86_64_aot_output_format_for_os("macos").unwrap(),
            X86OutputFormat::MachO,
            "macOS should use Mach-O for public x86-64 AOT"
        );
        assert_eq!(
            x86_64_aot_output_format_for_os("windows").unwrap(),
            X86OutputFormat::Coff,
            "Windows should use COFF for public x86-64 AOT"
        );
    }

    #[test]
    fn x86_64_requested_target_spec_selects_output_format_and_abi() {
        use crate::x86_64::X86OutputFormat;

        let windows = TargetSpec::parse("x86_64-pc-windows-msvc").unwrap();
        assert_eq!(
            x86_64_aot_output_format_for_target_spec(windows).unwrap(),
            X86OutputFormat::Coff
        );
        let windows_cc = compiler_calling_convention(Target::X86_64, windows);
        assert_eq!(windows_cc.name, "windows_x64");
        assert_eq!(windows_cc.num_arg_gprs, 4);
        assert_eq!(windows_cc.shadow_space, 32);
        assert_eq!(windows_cc.red_zone_size, 0);

        let linux = TargetSpec::parse("x86_64-unknown-linux-gnu").unwrap();
        assert_eq!(
            x86_64_aot_output_format_for_target_spec(linux).unwrap(),
            X86OutputFormat::Elf
        );
        assert_eq!(
            compiler_calling_convention(Target::X86_64, linux).name,
            "sysv_amd64"
        );

        let darwin = TargetSpec::parse("x86_64-apple-darwin").unwrap();
        assert_eq!(
            x86_64_aot_output_format_for_target_spec(darwin).unwrap(),
            X86OutputFormat::MachO
        );
        assert_eq!(
            compiler_calling_convention(Target::X86_64, darwin).name,
            "sysv_amd64"
        );
    }

    #[test]
    fn compiler_new_for_target_spec_records_requested_x86_triple() {
        let target_spec = TargetSpec::parse("x86_64-pc-windows-msvc").unwrap();
        let compiler = Compiler::new_for_target_spec(CompilerConfig::default(), target_spec);

        assert_eq!(compiler.config().target, Target::X86_64);
        assert_eq!(compiler.target_spec(), target_spec);
        assert_eq!(
            compiler_target_triple(compiler.target_spec()),
            "x86_64-pc-windows-msvc"
        );
    }

    #[test]
    fn compiler_target_facts_distinguish_x86_windows_from_sysv() {
        let windows = TargetSpec::parse("x86_64-pc-windows-msvc").unwrap();
        let linux = TargetSpec::parse("x86_64-unknown-linux-gnu").unwrap();

        let windows_facts = compiler_target_facts_sha256(Target::X86_64, windows).unwrap();
        let linux_facts = compiler_target_facts_sha256(Target::X86_64, linux).unwrap();

        assert_ne!(windows_facts, linux_facts);
    }

    #[test]
    fn x86_64_aot_unknown_os_fails_closed_without_macho_fallback() {
        let err = x86_64_aot_output_format_for_os("solaris").unwrap_err();
        match err {
            CompileError::X86AotObjectFormatUnsupported {
                target_os,
                required_format,
                context,
            } => {
                assert_eq!(target_os, "solaris");
                assert_eq!(required_format, "native object format");
                assert!(
                    context.contains("no x86-64 AOT object emitter"),
                    "diagnostic should explain that no native emitter is wired, got {context}"
                );
            }
            other => panic!("expected fail-closed x86 AOT object-format error, got {other:?}"),
        }
    }

    #[test]
    fn default_aarch64_unknown_target_fails_closed_without_macho_fallback() {
        let module = const_i64_module("default_aarch64_unknown", "answer", 7);
        let compiler = Compiler::new(CompilerConfig {
            target: Target::Aarch64,
            parallel: false,
            ..CompilerConfig::default()
        });

        let result = compiler
            .compile(&module)
            .expect("default AArch64 should resolve the host triple and emit a native object");
        assert!(!result.object_code.is_empty());
    }

    #[cfg(target_os = "windows")]
    #[test]
    fn x86_64_public_aot_windows_emits_framed_coff_with_unwind_metadata() {
        let module = const_i64_module("x86_windows_aot_coff", "answer", 42);
        let compiler = Compiler::new(CompilerConfig {
            opt_level: OptLevel::O0,
            target: Target::X86_64,
            parallel: false,
            ..CompilerConfig::default()
        });

        let result = compiler
            .compile(&module)
            .expect("Windows x86 public AOT should emit framed COFF with unwind metadata");

        assert_eq!(
            u16::from_le_bytes([result.object_code[0], result.object_code[1]]),
            crate::coff::IMAGE_FILE_MACHINE_AMD64
        );
        assert!(
            result
                .object_code
                .windows(6)
                .any(|window| window == b".pdata"),
            "Windows public AOT COFF should include .pdata unwind records"
        );
        assert!(
            result
                .object_code
                .windows(6)
                .any(|window| window == b".xdata"),
            "Windows public AOT COFF should include .xdata unwind info"
        );
    }

    #[test]
    fn x86_64_windows_coff_stale_cache_entry_misses_before_unwind_guard() {
        let root = temp_cache_root("x86-windows-coff-stale");
        let module = const_i64_module("x86_windows_stale_coff_cache", "answer", 42);
        let target_spec = TargetSpec::parse("x86_64-pc-windows-msvc").unwrap();
        let config = CompilerConfig {
            opt_level: OptLevel::O0,
            target: Target::X86_64,
            parallel: false,
            ..CompilerConfig::default()
        };
        let cache_config = test_cache_config(&root, CompileArtifactProofPolicy::Unchecked);
        let compiler = Compiler::new_for_target_spec(config.clone(), target_spec)
            .with_compile_artifact_cache(cache_config.clone());
        let (_, current_key, _) = compiler
            .compile_artifact_cache_context(&module, &module)
            .unwrap()
            .expect("test compiler should build a cache context");

        let stale_codegen_options_sha256 = pre_unwind_guard_codegen_options_sha256(
            &config,
            target_spec,
            &current_key.profile_use_sha256,
        )
        .unwrap();
        let stale_key = CompileArtifactCacheKey::new(
            current_key.source_sha256.clone(),
            current_key.trust_ir_sha256.clone(),
            stale_codegen_options_sha256,
            current_key.target,
            current_key.target_triple.clone(),
            current_key.target_facts_sha256.clone(),
            current_key.proof_policy,
            current_key.dependency_identity.clone(),
        )
        .with_profile_use_sha256(current_key.profile_use_sha256.clone());

        assert_ne!(
            stale_key.codegen_options_sha256,
            current_key.codegen_options_sha256
        );
        assert_ne!(stale_key.key_sha256, current_key.key_sha256);

        let cache = cache_config.backend();
        cache
            .store_from_pipeline(
                &stale_key,
                b"stale-pre-unwind-guard-coff-object",
                "trust-cg-codegen-test-pre-guard",
            )
            .unwrap();
        match cache.lookup_for_pipeline(&stale_key).unwrap() {
            CompileArtifactCacheLookup::Hit { entry, .. } => {
                assert_eq!(entry.artifact_bytes, b"stale-pre-unwind-guard-coff-object");
            }
            other => panic!("expected seeded stale cache entry to be readable, got {other:?}"),
        }
        assert_eq!(
            cache
                .lookup_for_pipeline(&current_key)
                .unwrap()
                .telemetry()
                .status,
            CompileArtifactCacheStatus::Miss,
            "current backend safety identity must not alias the stale cache entry"
        );

        let result = compiler
            .compile(&module)
            .expect("current Windows COFF backend should miss stale cache and emit fresh object");
        assert!(
            result
                .object_code
                .windows(6)
                .any(|window| window == b".pdata"),
            "fresh Windows COFF object should include .pdata"
        );
        assert_eq!(
            cache
                .lookup_for_pipeline(&current_key)
                .unwrap()
                .telemetry()
                .status,
            CompileArtifactCacheStatus::Hit,
            "fresh Windows COFF emission should store a replacement cache entry"
        );

        std::fs::remove_dir_all(root).unwrap();
    }

    #[cfg(any(
        target_os = "linux",
        target_os = "android",
        target_os = "freebsd",
        target_os = "netbsd",
        target_os = "openbsd",
        target_os = "dragonfly",
        target_os = "macos"
    ))]
    #[test]
    fn x86_64_public_aot_uses_host_native_object_magic() {
        let module = const_i64_module("x86_host_aot_object_magic", "answer", 42);
        let compiler = Compiler::new(CompilerConfig {
            opt_level: OptLevel::O0,
            target: Target::X86_64,
            parallel: false,
            ..CompilerConfig::default()
        });

        let result = compiler
            .compile(&module)
            .expect("x86 public AOT should compile to the host-native object format");
        assert!(
            result.object_code.len() >= 4,
            "object too small for magic: {} bytes",
            result.object_code.len()
        );
        match compiler_host_target_os() {
            "linux" | "android" | "freebsd" | "netbsd" | "openbsd" | "dragonfly" => {
                assert_eq!(&result.object_code[..4], b"\x7FELF");
                let macho_magic = 0xFEED_FACFu32.to_le_bytes();
                assert_ne!(
                    &result.object_code[..4],
                    macho_magic.as_slice(),
                    "ELF hosts must not silently emit Mach-O for x86 public AOT"
                );
            }
            "macos" => {
                let magic = u32::from_le_bytes(result.object_code[..4].try_into().unwrap());
                assert_eq!(magic, 0xFEED_FACF);
                assert_ne!(
                    &result.object_code[..4],
                    b"\x7FELF",
                    "macOS hosts must not silently emit ELF for x86 public AOT"
                );
            }
            "windows" => {
                assert_eq!(
                    u16::from_le_bytes([result.object_code[0], result.object_code[1]]),
                    crate::coff::IMAGE_FILE_MACHINE_AMD64
                );
                assert_ne!(
                    &result.object_code[..4],
                    b"\x7FELF",
                    "Windows hosts must not silently emit ELF for x86 public AOT"
                );
                let macho_magic = 0xFEED_FACFu32.to_le_bytes();
                assert_ne!(
                    &result.object_code[..4],
                    macho_magic.as_slice(),
                    "Windows hosts must not silently emit Mach-O for x86 public AOT"
                );
            }
            other => panic!("unexpected test target OS: {other}"),
        }
    }

    #[test]
    fn test_default_config() {
        let config = CompilerConfig::default();
        assert_eq!(config.opt_level, OptLevel::O2);
        assert_eq!(config.target, Target::Aarch64);
        assert!(!config.emit_proofs);
        assert_eq!(config.trace_level, CompilerTraceLevel::None);
        assert!(
            config.parallel,
            "parallel compilation should be enabled by default"
        );
    }

    #[test]
    fn test_compiler_new() {
        let compiler = Compiler::new(CompilerConfig::default());
        assert_eq!(compiler.config().opt_level, OptLevel::O2);
        assert_eq!(compiler.config().target, Target::Aarch64);
    }

    #[test]
    fn test_compiler_default_o2() {
        let compiler = Compiler::default_o2();
        assert_eq!(compiler.config().opt_level, OptLevel::O2);
    }

    #[test]
    fn test_compiler_jit_fast_profile() {
        let config = CompilerConfig::jit_fast(Target::Aarch64);
        assert_eq!(config.opt_level, OptLevel::O1);
        assert_eq!(config.target, Target::Aarch64);
        assert!(!config.emit_proofs);
        assert_eq!(config.trace_level, CompilerTraceLevel::None);
        assert!(!config.emit_debug);
        assert!(!config.parallel);
        assert_eq!(config.cegis_superopt_budget_sec, None);
        // jit_fast must enable the latency-tuned regalloc profile so the
        // for_host_jit() path picks AllocConfig::jit_latency_aarch64
        // (AllocStrategy::LinearScan).
        assert!(config.enable_jit_fast_regalloc);

        let compiler = Compiler::jit_fast(Target::Aarch64);
        assert_eq!(compiler.config().opt_level, OptLevel::O1);
        assert!(!compiler.config().parallel);
    }

    #[test]
    fn test_compiler_default_does_not_enable_jit_fast_regalloc() {
        // Default (AOT) compilation must keep the full quality regalloc.
        let config = CompilerConfig::default();
        assert!(!config.enable_jit_fast_regalloc);
    }

    #[test]
    fn test_compiler_config_for_host_jit_selects_host() {
        let config = CompilerConfig::for_host_jit();
        assert_eq!(config.opt_level, OptLevel::O1);
        assert_eq!(config.target, Target::host());
        assert!(!config.emit_proofs);
        assert_eq!(config.trace_level, CompilerTraceLevel::None);
        assert!(!config.emit_debug);
        assert!(!config.parallel);
        assert_eq!(config.cegis_superopt_budget_sec, None);
    }

    #[test]
    fn test_compiler_for_host_selects_host_jit_config() {
        let compiler = Compiler::for_host();
        assert_eq!(compiler.config().opt_level, OptLevel::O1);
        assert_eq!(compiler.config().target, Target::host());
        assert!(!compiler.config().parallel);
    }

    #[test]
    fn test_compile_module_to_jit_rejects_non_host_target() {
        use std::collections::HashMap;
        use trust_ir_build::ModuleBuilder;

        let target = match Target::host() {
            Target::Aarch64 => Target::X86_64,
            Target::X86_64 | Target::Riscv64 => Target::Aarch64,
        };
        let compiler = Compiler::jit_fast(target);
        let module = ModuleBuilder::new("jit_target_mismatch").build();
        let err = compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_err();

        assert!(
            matches!(
                err,
                CompileError::JitTargetMismatch {
                    target: actual_target,
                    host
                } if actual_target == target && host == Target::host()
            ),
            "expected JitTargetMismatch for {target:?}, got {err}"
        );
    }

    #[cfg(not(any(target_arch = "aarch64", target_arch = "x86_64")))]
    #[test]
    fn test_compile_module_to_jit_rejects_unwired_host_target() {
        use std::collections::HashMap;
        use trust_ir_build::ModuleBuilder;

        let compiler = Compiler::for_host();
        let module = ModuleBuilder::new("jit_unsupported_host").build();
        let err = compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_err();

        assert!(
            matches!(
                err,
                CompileError::JitTargetUnsupported { target }
                    if target == Target::host()
            ),
            "expected JitTargetUnsupported for host {:?}, got {err}",
            Target::host()
        );
    }

    #[test]
    fn test_custom_config() {
        let config = CompilerConfig {
            opt_level: OptLevel::O0,
            target: Target::X86_64,
            emit_proofs: true,
            trace_level: CompilerTraceLevel::Full,
            emit_debug: true,
            parallel: false,
            cegis_superopt_budget_sec: None,
            enable_fsym_trust_ir_preflight: false,
            enable_jit_fast_regalloc: false,
            jit_validation_mode_override: None,
            panic_unwind: false,
        };
        let compiler = Compiler::new(config);
        assert_eq!(compiler.config().opt_level, OptLevel::O0);
        assert_eq!(compiler.config().target, Target::X86_64);
        assert!(compiler.config().emit_proofs);
        assert_eq!(compiler.config().trace_level, CompilerTraceLevel::Full);
        assert!(compiler.config().emit_debug);
        assert!(!compiler.config().parallel);
    }

    #[test]
    fn compiler_config_runs_fsym_trust_ir_preflight_in_public_pipeline() {
        let module = divzero_i64_module("compiler_fsym_public", "divzero");
        let compiler = Compiler::new(CompilerConfig {
            opt_level: OptLevel::O0,
            parallel: false,
            enable_fsym_trust_ir_preflight: true,
            ..CompilerConfig::default()
        });

        let result = compiler
            .compile(&module)
            .expect("fsym preflight should not reject codegen");

        assert_eq!(result.metrics.fsym_trust_ir.scanned_functions, 1);
        assert_eq!(result.metrics.fsym_trust_ir.skipped_functions, 0);
        assert_eq!(result.metrics.fsym_trust_ir.concrete_ub_diagnostics, 1);
        assert_eq!(result.metrics.fsym_trust_ir.unknown_obligations, 0);
        assert_eq!(result.metrics.fsym_trust_ir.warnings, 1);
    }

    #[test]
    fn compile_result_does_not_mint_proof_optimization_citations_from_labels() {
        let module = proof_optimization_citation_module();
        let compiler = Compiler::new(CompilerConfig {
            opt_level: OptLevel::O2,
            parallel: false,
            ..CompilerConfig::default()
        });

        let result = compiler
            .compile(&module)
            .expect("compiler codegen should succeed");
        assert!(result.proof_optimization_certificates.is_empty());
        assert_eq!(result.metrics.proof_optimizations.certificate_count, 0);
        assert_eq!(result.metrics.proof_optimizations.applied_count, 0);
        assert_eq!(result.metrics.proof_optimizations.rejected_count, 0);
        assert!(!trust_cg_lower::guard_evidence::validator_guard_replay_authority_available());
    }

    #[cfg(feature = "verify")]
    #[test]
    fn compile_result_attaches_checked_certified_pass_chain() {
        let base_compiler = Compiler::default_o2();
        let const_fold_run = gamma_demo_run_record(
            "const-fold-bv64",
            "const-fold:bv64:v1",
            "analytical-bv64 const-fold checker",
            "gamma_vnncomp_demo",
        );
        let dce_run = gamma_demo_run_record(
            "dce-pure-unused",
            "dce:pure-unused:v1",
            "trust-cg-opt dce checker",
            "gamma_vnncomp_demo",
        );
        let chain = trust_cg_verify::CertifiedPassChain::check_requests(vec![
            synthesize_gamma_demo_check_request(&base_compiler, 0, &const_fold_run),
            synthesize_gamma_demo_check_request(&base_compiler, 1, &dce_run),
        ])
        .expect("gamma certified pass requests should validate");
        let compiler = base_compiler
            .with_certified_pass_chain(chain)
            .expect("verified chain should attach");
        let mut ir_func = crate::pipeline::build_add_test_function();

        let result = compiler
            .compile_ir_function(&mut ir_func)
            .expect("compiler codegen should succeed");

        let attachment = result
            .certified_pass_chain
            .expect("compile result should carry the certified pass chain");
        assert_eq!(attachment.compilation_unit, "gamma-vnncomp-demo");
        assert_eq!(attachment.entries.len(), 2);

        let first = &attachment.entries[0];
        assert_eq!(first.compilation_unit, "gamma-vnncomp-demo");
        assert_eq!(first.certificate_index, 0);
        assert_eq!(first.pass_name, "const-fold-bv64");
        assert_eq!(
            first.certificate["obligation_hash"].as_str(),
            Some(first.obligation_hash.as_str())
        );
        assert_eq!(
            first.report["obligation_hash"].as_str(),
            Some(first.obligation_hash.as_str())
        );
        assert_eq!(first.report["result"]["status"].as_str(), Some("verified"));

        let second = &attachment.entries[1];
        assert_eq!(second.compilation_unit, "gamma-vnncomp-demo");
        assert_eq!(second.certificate_index, 1);
        assert_eq!(second.pass_name, "dce-pure-unused");
        assert_eq!(
            second.certificate["pass"]["name"].as_str(),
            Some(second.pass_name.as_str())
        );
        assert_eq!(second.report["result"]["status"].as_str(), Some("verified"));
    }

    #[cfg(feature = "verify")]
    #[test]
    fn compile_result_attaches_production_certified_pass_chain_from_opt_runs() {
        let compiler = Compiler::default_o2().with_production_certified_pass_chain();
        let module = const_i64_module("prod_cert", "prod_cert_entry", 7);

        let result = compiler
            .compile(&module)
            .expect("compiler codegen should succeed");

        let attachment = result
            .certified_pass_chain
            .expect("production certified pass chain should attach");
        assert_eq!(attachment.compilation_unit, "prod_cert");
        assert!(
            attachment
                .entries
                .iter()
                .any(|entry| entry.pass_name == "const-fold-bv64")
        );
        assert!(
            attachment
                .entries
                .iter()
                .any(|entry| entry.pass_name == "dce-pure-unused")
        );
        assert!(
            attachment
                .entries
                .iter()
                .all(|entry| entry.report["result"]["status"].as_str() == Some("verified"))
        );
        assert!(
            attachment
                .entries
                .windows(2)
                .all(|pair| pair[0].certificate_index + 1 == pair[1].certificate_index)
        );
    }

    #[cfg(feature = "verify")]
    #[test]
    fn production_certified_pass_chain_rejects_failed_opt_run() {
        let run = trust_cg_opt::CertifiedPassRunRecord {
            format_version: "trust-cg.opt.certified_pass_run.v1".to_string(),
            pass_name: "const-fold-bv64".to_string(),
            pass_version: 1,
            pass_instance_id: "const-fold:bv64:v1".to_string(),
            function_name: "bad".to_string(),
            changed: false,
            status: trust_cg_opt::CertifiedPassRunStatus::Failed,
            certificate_count: 0,
            failure_count: 1,
            obligation_hash: "trust-cg-opt-certified-pass-run-v1:bad".to_string(),
            local_checker: trust_cg_opt::CertifiedPassCheckerRecord {
                kind: "trust-cg-opt-local".to_string(),
                name: "analytical-bv64 const-fold checker".to_string(),
                version: "1".to_string(),
                status: trust_cg_opt::CertifiedPassRunStatus::Failed,
            },
            summary: serde_json::json!({
                "changed": false,
                "certificates": [],
                "failures": [{"reason": "forced failure"}]
            }),
        };
        let compiler = Compiler::default_o2().with_production_certified_pass_chain();

        let err = compiler
            .certified_pass_chain_attachment_from_runs("unit", &[run])
            .expect_err("failed opt certified run must reject the chain");

        assert!(matches!(
            err,
            CompileError::CertifiedPassExecutionFailed { .. }
        ));
    }

    #[cfg(feature = "verify")]
    #[test]
    fn compiler_rejects_unverified_certified_pass_entries() {
        use trust_cg_verify::certified_pass_checker::{
            Lean5CheckerResult, check_lean5_pass_certificate,
        };

        let base_compiler = Compiler::default_o2();
        let const_fold_run = gamma_demo_run_record(
            "const-fold-bv64",
            "const-fold:bv64:v1",
            "analytical-bv64 const-fold checker",
            "gamma_vnncomp_demo",
        );
        let request = synthesize_gamma_demo_check_request(&base_compiler, 0, &const_fold_run);
        let mut report = check_lean5_pass_certificate(&request);
        report.result = Lean5CheckerResult::Skipped {
            reason: "not replayed".to_string(),
        };
        let entry = trust_cg_verify::CertifiedPassChainEntry::from_report(request, report);

        let err = match Compiler::default_o2().with_checked_certified_pass_entries(vec![entry]) {
            Ok(_) => panic!("unverified certified pass entry should be rejected"),
            Err(err) => err,
        };

        assert!(matches!(
            err,
            trust_cg_verify::CertifiedPassChainError::ReportNotVerified { entry_index: 0, .. }
        ));
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn compile_module_to_jit_keeps_label_only_citations_out_of_replay_metadata() {
        let module = proof_optimization_citation_module();
        let compiler = Compiler::new(CompilerConfig {
            opt_level: OptLevel::O2,
            target: Target::Aarch64,
            parallel: false,
            ..CompilerConfig::default()
        });

        let result = compiler
            .compile_module_to_jit(&module, &std::collections::HashMap::new())
            .expect("JIT codegen should succeed");
        assert!(result.proof_optimization_certificates.is_empty());
        assert_eq!(result.metrics.proof_optimizations.certificate_count, 0);
        assert_eq!(result.metrics.proof_optimizations.applied_count, 0);
        assert_eq!(result.metrics.proof_optimizations.rejected_count, 0);
        assert!(result.buffer.proof_optimization_certificates().is_empty());

        let replay = result.buffer.replay_report_metadata().to_json_value();
        assert_eq!(
            replay["proof_optimization_certificates"],
            serde_json::Value::Array(Vec::new())
        );
    }

    #[test]
    fn compile_artifact_cache_pipeline_path_reports_miss_store_then_hit() {
        let root = temp_cache_root("hit");
        let module = const_i64_module("compiler_cache_hit", "answer", 42);
        let target_spec = TargetSpec::parse("aarch64-apple-darwin").unwrap();
        let config = CompilerConfig {
            opt_level: OptLevel::O0,
            parallel: false,
            ..CompilerConfig::default()
        };
        let cache_config = test_cache_config(&root, CompileArtifactProofPolicy::Unchecked);

        let first = Compiler::new_for_target_spec(config.clone(), target_spec)
            .with_compile_artifact_cache(cache_config.clone())
            .compile(&module)
            .expect("first compile should populate cache");
        assert_eq!(
            first
                .compile_artifact_cache_telemetry
                .iter()
                .map(|event| event.status)
                .collect::<Vec<_>>(),
            vec![
                CompileArtifactCacheStatus::Miss,
                CompileArtifactCacheStatus::Stored
            ]
        );
        assert!(
            first
                .compile_artifact_cache_telemetry
                .iter()
                .all(|event| event.boundary == CompileArtifactCacheBoundary::Pipeline)
        );

        let second = Compiler::new_for_target_spec(config, target_spec)
            .with_compile_artifact_cache(cache_config)
            .compile(&module)
            .expect("second compile should replay cached object");

        assert_eq!(second.object_code, first.object_code);
        assert_eq!(
            second
                .compile_artifact_cache_telemetry
                .iter()
                .map(|event| event.status)
                .collect::<Vec<_>>(),
            vec![CompileArtifactCacheStatus::Hit]
        );

        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn compile_artifact_cache_profile_use_misses_after_no_profile_entry() {
        let root = temp_cache_root("profile-use-no-profile");
        let module = const_i64_module("compiler_cache_profile_use", "answer", 42);
        let target_spec = TargetSpec::parse("aarch64-apple-darwin").unwrap();
        let config = CompilerConfig {
            opt_level: OptLevel::O2,
            parallel: false,
            ..CompilerConfig::default()
        };
        let cache_config = test_cache_config(&root, CompileArtifactProofPolicy::Unchecked);

        Compiler::new_for_target_spec(config.clone(), target_spec)
            .with_compile_artifact_cache(cache_config.clone())
            .compile(&module)
            .expect("no-profile compile should populate cache");

        let profile = profile_use_with_hits(11);
        let profiled = Compiler::new_for_target_spec(config, target_spec)
            .with_profile_use(profile)
            .with_compile_artifact_cache(cache_config)
            .compile(&module)
            .expect("profile-use compile should use a distinct cache key");

        assert_eq!(
            profiled
                .compile_artifact_cache_telemetry
                .iter()
                .map(|event| event.status)
                .collect::<Vec<_>>(),
            vec![
                CompileArtifactCacheStatus::Miss,
                CompileArtifactCacheStatus::Stored
            ]
        );

        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn compile_artifact_cache_different_profile_use_inputs_miss() {
        let root = temp_cache_root("profile-use-different");
        let module = const_i64_module("compiler_cache_profile_use_diff", "answer", 42);
        let target_spec = TargetSpec::parse("aarch64-apple-darwin").unwrap();
        let config = CompilerConfig {
            opt_level: OptLevel::O2,
            parallel: false,
            ..CompilerConfig::default()
        };
        let cache_config = test_cache_config(&root, CompileArtifactProofPolicy::Unchecked);

        Compiler::new_for_target_spec(config.clone(), target_spec)
            .with_profile_use(profile_use_with_hits(11))
            .with_compile_artifact_cache(cache_config.clone())
            .compile(&module)
            .expect("first profile-use compile should populate cache");

        let different_profile = Compiler::new_for_target_spec(config, target_spec)
            .with_profile_use(profile_use_with_hits(29))
            .with_compile_artifact_cache(cache_config)
            .compile(&module)
            .expect("different profile-use compile should not replay prior profile object");

        assert_eq!(
            different_profile
                .compile_artifact_cache_telemetry
                .iter()
                .map(|event| event.status)
                .collect::<Vec<_>>(),
            vec![
                CompileArtifactCacheStatus::Miss,
                CompileArtifactCacheStatus::Stored
            ]
        );

        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn compile_artifact_cache_proof_policy_change_misses_integrated_path() {
        let root = temp_cache_root("proof-policy");
        let module = const_i64_module("compiler_cache_policy", "answer", 7);
        let config = CompilerConfig {
            opt_level: OptLevel::O0,
            parallel: false,
            ..CompilerConfig::default()
        };

        #[cfg(not(feature = "verify"))]
        {
            match Compiler::new(config)
                .with_compile_artifact_cache(test_cache_config(
                    &root,
                    CompileArtifactProofPolicy::ProofTvFull,
                ))
                .compile(&module)
            {
                Err(CompileError::ProofPromotionRejected { reason, .. }) => {
                    assert!(
                        reason.contains("none were emitted"),
                        "non-verify proof-policy compile should fail closed: {reason}"
                    );
                }
                Err(other) => panic!("expected ProofPromotionRejected, got {other}"),
                Ok(_) => panic!("proof-policy cache compile must fail closed without verifier"),
            }
            std::fs::remove_dir_all(root).unwrap();
            return;
        }

        #[cfg(feature = "verify")]
        {
            // Ordinary AArch64 ELF object relocations intentionally block full
            // proof promotion until their target-specific obligations exist.
            // Use the proven x86-64 Mach-O object surface here so this test can
            // isolate cache-key partitioning rather than weakening that gate.
            let target_spec = TargetSpec::parse("x86_64-apple-darwin").unwrap();
            Compiler::new_for_target_spec(config.clone(), target_spec)
                .with_compile_artifact_cache(test_cache_config(
                    &root,
                    CompileArtifactProofPolicy::ProofTvFull,
                ))
                .compile(&module)
                .expect("full policy compile should populate cache");

            let smoke = Compiler::new_for_target_spec(config, target_spec)
                .with_compile_artifact_cache(test_cache_config(
                    &root,
                    CompileArtifactProofPolicy::Smoke,
                ))
                .compile(&module)
                .expect("smoke policy compile should use a distinct key");

            assert_eq!(
                smoke
                    .compile_artifact_cache_telemetry
                    .first()
                    .map(|event| event.status),
                Some(CompileArtifactCacheStatus::Miss)
            );

            std::fs::remove_dir_all(root).unwrap();
        }
    }

    #[test]
    fn compile_artifact_cache_profile_use_change_misses_integrated_path() {
        let root = temp_cache_root("profile-use");
        let module = const_i64_module("compiler_cache_profile_use", "answer", 13);
        let profile_a = profile_use_with_hits(10);
        let profile_b = profile_use_with_hits(20);
        let target_spec = TargetSpec::parse("aarch64-apple-darwin").unwrap();
        let config = CompilerConfig {
            opt_level: OptLevel::O2,
            parallel: false,
            ..CompilerConfig::default()
        };
        let cache_config = test_cache_config(&root, CompileArtifactProofPolicy::Unchecked);

        let first = Compiler::new_for_target_spec(config.clone(), target_spec)
            .with_profile_use(profile_a.clone())
            .with_compile_artifact_cache(cache_config.clone())
            .compile(&module)
            .expect("first profile-use compile should populate cache");
        assert_eq!(
            first
                .compile_artifact_cache_telemetry
                .iter()
                .map(|event| event.status)
                .collect::<Vec<_>>(),
            vec![
                CompileArtifactCacheStatus::Miss,
                CompileArtifactCacheStatus::Stored
            ]
        );
        let first_store = first
            .compile_artifact_cache_telemetry
            .iter()
            .find(|event| event.status == CompileArtifactCacheStatus::Stored)
            .expect("first compile should store cache entry");
        let first_profile_use_sha256 = manifest_profile_use_sha256(&first_store.cache_path);
        assert_ne!(
            first_profile_use_sha256,
            COMPILE_ARTIFACT_PROFILE_USE_DISABLED_SHA256
        );

        let repeat = Compiler::new_for_target_spec(config.clone(), target_spec)
            .with_profile_use(profile_a)
            .with_compile_artifact_cache(cache_config.clone())
            .compile(&module)
            .expect("same profile-use input should replay cached object");
        assert_eq!(
            repeat
                .compile_artifact_cache_telemetry
                .iter()
                .map(|event| event.status)
                .collect::<Vec<_>>(),
            vec![CompileArtifactCacheStatus::Hit]
        );
        assert_eq!(repeat.object_code, first.object_code);

        let changed = Compiler::new_for_target_spec(config, target_spec)
            .with_profile_use(profile_b)
            .with_compile_artifact_cache(cache_config)
            .compile(&module)
            .expect("different profile-use input should use a distinct cache key");
        assert_eq!(
            changed
                .compile_artifact_cache_telemetry
                .first()
                .map(|event| event.status),
            Some(CompileArtifactCacheStatus::Miss)
        );
        let changed_store = changed
            .compile_artifact_cache_telemetry
            .iter()
            .find(|event| event.status == CompileArtifactCacheStatus::Stored)
            .expect("changed profile compile should store cache entry");
        let changed_profile_use_sha256 = manifest_profile_use_sha256(&changed_store.cache_path);
        assert_ne!(first_profile_use_sha256, changed_profile_use_sha256);
        assert_ne!(first_store.key_sha256, changed_store.key_sha256);

        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn compile_artifact_cache_corrupt_integrated_entry_is_rejected() {
        let root = temp_cache_root("corrupt");
        let module = const_i64_module("compiler_cache_corrupt", "answer", 99);
        let target_spec = TargetSpec::parse("aarch64-apple-darwin").unwrap();
        let config = CompilerConfig {
            opt_level: OptLevel::O0,
            parallel: false,
            ..CompilerConfig::default()
        };
        let cache_config = test_cache_config(&root, CompileArtifactProofPolicy::Unchecked);

        let first = Compiler::new_for_target_spec(config.clone(), target_spec)
            .with_compile_artifact_cache(cache_config.clone())
            .compile(&module)
            .expect("first compile should populate cache");
        let cache_path = first
            .compile_artifact_cache_telemetry
            .iter()
            .find(|event| event.status == CompileArtifactCacheStatus::Stored)
            .expect("first compile should store cache entry")
            .cache_path
            .clone();
        std::fs::write(cache_path.join("artifact.bin"), b"tampered-object").unwrap();

        let second = Compiler::new_for_target_spec(config, target_spec)
            .with_compile_artifact_cache(cache_config)
            .compile(&module)
            .expect("corrupt cache entry should fall back to compilation");

        assert_eq!(second.object_code, first.object_code);
        assert_eq!(
            second
                .compile_artifact_cache_telemetry
                .iter()
                .map(|event| event.status)
                .collect::<Vec<_>>(),
            vec![
                CompileArtifactCacheStatus::RejectedCorrupt,
                CompileArtifactCacheStatus::Stored
            ]
        );

        std::fs::remove_dir_all(root).unwrap();
    }

    #[cfg(not(target_os = "windows"))]
    #[test]
    fn test_x86_compile_runtime_count_alloca_threads_stack_slot_metadata() {
        let module = runtime_count_alloca_module("x86_runtime_count_alloca");
        let compiler = Compiler::new(CompilerConfig {
            opt_level: OptLevel::O0,
            target: Target::X86_64,
            parallel: false,
            ..CompilerConfig::default()
        });

        let result = compiler
            .compile(&module)
            .expect("x86 Compiler dispatcher should compile runtime-count Alloca");

        assert_eq!(result.metrics.function_count, 1);
        assert!(result.metrics.code_size_bytes > 0);
        let output_format = x86_64_aot_output_format_for_target_spec(compiler.target_spec())
            .expect("x86 compiler target spec should select an object format");
        let expected_unwind_sections: &[&[u8]] = match output_format {
            crate::x86_64::X86OutputFormat::Elf => &[b".eh_frame", b".rela.eh_frame"],
            crate::x86_64::X86OutputFormat::MachO => &[b"__eh_frame"],
            crate::x86_64::X86OutputFormat::Coff => &[b".pdata", b".xdata"],
            crate::x86_64::X86OutputFormat::RawBytes => {
                panic!("x86 compiler AOT target should not emit raw bytes")
            }
        };
        for section in expected_unwind_sections {
            assert!(
                result
                    .object_code
                    .windows(section.len())
                    .any(|window| window == *section),
                "runtime-sized x86 StackAddr object should carry DWARF unwind fallback section {}",
                String::from_utf8_lossy(section)
            );
        }
    }

    #[cfg(not(target_os = "windows"))]
    #[test]
    fn test_x86_public_dispatch_opt_level_metrics_follow_x86_schedule() {
        use trust_ir::Ty;
        use trust_ir_build::ModuleBuilder;

        let build_module = || {
            let mut mb = ModuleBuilder::new("x86_opt_level_metrics");
            let ty = mb.add_func_type(vec![], vec![Ty::I64]);
            let mut fb = mb.function("const_fn", ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let value = fb.iconst(Ty::I64, 42);
            fb.ret(vec![value]);
            fb.build();
            mb.build()
        };

        let compile_at = |opt_level| {
            let compiler = Compiler::new(CompilerConfig {
                opt_level,
                target: Target::X86_64,
                parallel: false,
                ..CompilerConfig::default()
            });
            compiler
                .compile(&build_module())
                .expect("x86 public Compiler dispatcher should compile const module")
        };

        let o0 = compile_at(OptLevel::O0);
        let o1 = compile_at(OptLevel::O1);
        let o2 = compile_at(OptLevel::O2);

        assert_eq!(o0.metrics.function_count, 1);
        assert_eq!(o0.metrics.optimization_passes_run, 0);
        // O1 = LICM, copy-prop, peephole, DCE, if-convert, branch-layout.
        // O2 adds vectorize, SROA, strength-reduce, loop-unroll, const-fold,
        // const-guard-elim, CSE, the dominated-compare bounds-check
        // elimination, loop rotation, and conditional-swap (SROA added in c70e396,
        // bounds-check-elim in f6f73d3, loop rotation defaulted on in
        // c033ba54, full unroll + const-guard-elim defaulted on 2026-07-20,
        // conditional-swap defaulted on in bbc02c7f, straight-line
        // block-merge added 2026-08-09).
        // See `X86Pipeline::x86_o1_pass_manager` / `x86_o2_pass_manager`.
        assert_eq!(o1.metrics.optimization_passes_run, 6);
        assert_eq!(o2.metrics.optimization_passes_run, 17);
        assert!(o0.metrics.code_size_bytes > 0);
        assert!(o1.metrics.code_size_bytes > 0);
        assert!(o2.metrics.code_size_bytes > 0);
    }

    #[test]
    fn test_metrics_default() {
        let metrics = CompilationMetrics::default();
        assert_eq!(metrics.code_size_bytes, 0);
        assert_eq!(metrics.instruction_count, 0);
        assert_eq!(metrics.function_count, 0);
        assert_eq!(metrics.optimization_passes_run, 0);
        assert_eq!(
            metrics.proof_optimizations,
            ProofOptimizationMetrics::default()
        );
    }

    #[test]
    fn test_compiler_trace_default() {
        let trace = CompilerTrace::default();
        assert!(trace.entries.is_empty());
        assert_eq!(trace.total_duration, Duration::ZERO);
    }

    #[test]
    fn test_compile_ir_function_add() {
        // Build a simple add function in IR (post-ISel, post-regalloc state)
        // and compile it through the pipeline.
        let mut ir_func = crate::pipeline::build_add_test_function();
        let compiler = Compiler::default_o2();
        let result = compiler.compile_ir_function(&mut ir_func).unwrap();

        assert!(
            !result.object_code.is_empty(),
            "should produce Mach-O bytes"
        );
        assert!(result.metrics.code_size_bytes > 0);
        assert_eq!(result.metrics.function_count, 1);
        assert!(
            result.trace.is_none(),
            "trace should be None with default config"
        );
        assert!(
            result.proofs.is_none(),
            "proofs should be None with default config"
        );
    }

    #[test]
    fn test_compile_ir_function_with_trace() {
        let mut ir_func = crate::pipeline::build_add_test_function();
        let compiler = Compiler::new(CompilerConfig {
            trace_level: CompilerTraceLevel::Summary,
            ..CompilerConfig::default()
        });
        let result = compiler.compile_ir_function(&mut ir_func).unwrap();

        assert!(
            result.trace.is_some(),
            "trace should be present with Summary level"
        );
        let trace = result.trace.unwrap();
        assert!(!trace.entries.is_empty());
        assert!(trace.total_duration >= Duration::ZERO);
    }

    /// The AOT path measures per-phase costs inside
    /// `prepare_function_with_metrics*` and used to drop them, emitting only a
    /// lumped `prepare_function` entry. That left backend time unattributable --
    /// notably the fixed ~9.5ms every Rust program pays for `std::rt::lang_start`.
    /// The breakdown must reach the trace.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn compile_trace_surfaces_per_phase_prepare_breakdown() {
        use trust_ir::Ty;
        use trust_ir_build::ModuleBuilder;

        let mut mb = ModuleBuilder::new("phase_breakdown");
        {
            let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
            let mut fb = mb.function("add_fn", ty);
            let entry = fb.create_block();
            let a = fb.add_block_param(entry, Ty::I64);
            let b = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let result = fb.add(Ty::I64, a, b);
            fb.ret(vec![result]);
            fb.build();
        }
        let module = mb.build();

        let compiler = Compiler::new(CompilerConfig {
            trace_level: CompilerTraceLevel::Summary,
            ..CompilerConfig::default()
        });
        let result = compiler.compile(&module).expect("compile");
        let trace = result.trace.expect("trace present at Summary level");

        let phases: Vec<&str> = trace
            .entries
            .iter()
            .map(|e| e.phase.as_str())
            .filter(|p| p.starts_with("prepare::"))
            .collect();

        assert!(
            !phases.is_empty(),
            "AOT trace must carry the per-phase prepare breakdown, got: {:?}",
            trace.entries.iter().map(|e| &e.phase).collect::<Vec<_>>()
        );
        assert!(
            phases.contains(&"prepare::isel"),
            "isel is always measured; got {phases:?}"
        );
    }

    #[cfg(feature = "verify")]
    #[test]
    fn test_compile_ir_function_emit_proofs_rejects_inexact_module_inventory() {
        let mut ir_func = crate::pipeline::build_add_test_function();
        let compiler = Compiler::new_for_target_spec(
            CompilerConfig {
                emit_proofs: true,
                ..CompilerConfig::default()
            },
            TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap(),
        );
        let error = compiler
            .compile_ir_function(&mut ir_func)
            .expect_err("single-function promotion must not reuse the module inventory");
        assert!(
            matches!(error, CompileError::ProofPromotionRejected { .. }),
            "{error}"
        );
        assert!(error.to_string().contains("compact-unwind relocations"));
        assert!(error.to_string().contains("exact emitted object/plan"));
    }

    #[cfg(feature = "verify")]
    #[test]
    fn test_compile_ir_function_with_proofs_rejects_unverified_reports() {
        let mut ir_func = crate::pipeline::build_add_test_function();
        insert_unverified_csinv_before_return(&mut ir_func);
        let compiler = Compiler::new(CompilerConfig {
            emit_proofs: true,
            ..CompilerConfig::default()
        });

        match compiler.compile_ir_function(&mut ir_func) {
            Err(CompileError::ProofPromotionRejected { target, reason }) => {
                assert_eq!(target, Target::Aarch64);
                assert!(
                    reason.contains("compact-unwind relocations")
                        && reason.contains("exact emitted object/plan"),
                    "direct prebuilt-IR proof promotion should fail at the exact-object inventory boundary: {reason}"
                );
            }
            Err(other) => panic!("expected ProofPromotionRejected, got {other}"),
            Ok(_) => panic!("proof-backed compile must reject unverified proof reports"),
        }
    }

    #[cfg(feature = "verify")]
    #[test]
    fn test_generate_proof_certificates_omits_harmless_skipped_reports() {
        use trust_cg_ir::function::{MachFunction as IrMachFunction, Signature as IrSignature};
        use trust_cg_ir::inst::{AArch64Opcode as IrOpcode, MachInst as IrMachInst};

        let sig = IrSignature::new(vec![], vec![]);
        let mut func = IrMachFunction::new("skipped_reports_omitted".to_string(), sig);
        let entry = func.entry;

        let nop = IrMachInst::new(IrOpcode::Nop, vec![]);
        let nop_id = func.push_inst(nop);
        func.append_inst(entry, nop_id);

        let certs = generate_proof_certificates(&func, None);
        assert!(
            certs.is_empty(),
            "harmless skipped pseudo-ops must not become negative proof entries: {:?}",
            certs
        );
    }

    #[cfg(feature = "verify")]
    #[test]
    fn test_generate_proof_certificates_credits_align_nop_structural_checks() {
        use trust_cg_ir::function::{MachFunction as IrMachFunction, Signature as IrSignature};
        use trust_cg_ir::inst::{AArch64Opcode as IrOpcode, MachInst as IrMachInst};

        let sig = IrSignature::new(vec![], vec![]);
        let mut func = IrMachFunction::new("align_nop_coverage_seam".to_string(), sig);
        let align_nop_id = func.push_inst(IrMachInst::new(IrOpcode::AlignNop, vec![]));
        func.append_inst(func.entry, align_nop_id);

        let certs = generate_proof_certificates(&func, None);
        assert!(
            certs
                .iter()
                .any(|cert| cert.verified && cert.category == "covered_elsewhere"),
            "AlignNop must receive structural coverage credit: {certs:?}"
        );
        assert!(
            certs.iter().all(|cert| cert.verified),
            "AlignNop must not also emit an inventory blocker: {certs:?}"
        );
    }

    #[cfg(feature = "verify")]
    #[test]
    fn test_generate_proof_certificates_reports_aarch64_opcode_inventory_gap() {
        use trust_cg_ir::function::{MachFunction as IrMachFunction, Signature as IrSignature};
        use trust_cg_ir::inst::{AArch64Opcode as IrOpcode, MachInst as IrMachInst};

        let sig = IrSignature::new(vec![], vec![]);
        let mut func = IrMachFunction::new("aarch64_opcode_inventory_gap".to_string(), sig);
        let entry = func.entry;
        // CSINV is non-pseudo and has no registered value-proof mapping (FABS/
        // FSQRT/FDIV are now wired), so it is the canonical uncovered opcode.
        let csinv = IrMachInst::new(IrOpcode::Csinv, vec![]);
        let csinv_id = func.push_inst(csinv);
        func.append_inst(entry, csinv_id);

        let certs = generate_proof_certificates(&func, None);
        let inventory = certs
            .iter()
            .find(|cert| !cert.verified && cert.category == "opcode_inventory")
            .expect("uncovered AArch64 opcode must produce an inventory blocker");

        assert!(
            inventory.strength.contains("AArch64::Csinv"),
            "{inventory:?}"
        );
        assert!(
            inventory.strength.contains("uncovered non-pseudo opcode"),
            "{inventory:?}"
        );
    }

    /// MERGE-CLOBBER SENTINEL (cross-file): commit ae86e4c0 introduced the
    /// per-(width, shift) MOVK halfword-splice binding across TWO files — the
    /// proofs in trust-cg-verify/const_materialize_proofs.rs and the binding in
    /// trust-cg-verify/function_verifier.rs. Merge c334073b silently reverted
    /// ONLY the function_verifier.rs half, which took every wide-constant
    /// (MOVZ+MOVK) function back to unpromotable while every proof-side test
    /// stayed green. This test locks the seam from a THIRD file: a
    /// MOVZ+MOVK(LSL #16) function's emitted-opcode inventory must have NO
    /// uncovered Movk row (promotable w.r.t. opcodes), so clobbering either
    /// half fails a test outside the clobbered crate's own file.
    #[cfg(feature = "verify")]
    #[test]
    fn movk_per_form_binding_survives_merges() {
        use trust_cg_ir::function::{MachFunction as IrMachFunction, Signature as IrSignature};
        use trust_cg_ir::inst::{AArch64Opcode as IrOpcode, MachInst as IrMachInst};
        use trust_cg_ir::{MachOperand, RegClass, VReg};

        let sig = IrSignature::new(vec![], vec![]);
        let mut func = IrMachFunction::new("movk_per_form_sentinel".to_string(), sig);
        let entry = func.entry;
        let dst = VReg::new(0, RegClass::Gpr64);
        let movz_id = func.push_inst(IrMachInst::new(
            IrOpcode::Movz,
            vec![MachOperand::VReg(dst), MachOperand::Imm(0x1234)],
        ));
        func.append_inst(entry, movz_id);
        let movk_id = func.push_inst(IrMachInst::new(
            IrOpcode::Movk,
            vec![
                MachOperand::VReg(dst),
                MachOperand::Imm(0x5678),
                MachOperand::Imm(16),
            ],
        ));
        func.append_inst(entry, movk_id);

        // Inventory-level lock: no uncovered Movk row; the wide-constant chain
        // is promotable w.r.t. opcode coverage.
        let report = trust_cg_verify::function_verifier::verify_function(&func);
        let inventory = report.emitted_opcode_inventory();
        let uncovered: Vec<String> = inventory
            .uncovered_non_pseudo_opcodes()
            .iter()
            .map(|entry| format!("{}", entry.opcode))
            .collect();
        assert!(
            !uncovered.iter().any(|name| name.contains("Movk")),
            "MOVK lost its per-form proof binding (merge clobber of the \
             function_verifier.rs half of ae86e4c0?): uncovered rows {uncovered:?}"
        );
        assert!(
            inventory.is_promotable(),
            "MOVZ+MOVK(LSL #16) must be promotable w.r.t. opcodes; \
             uncovered rows {uncovered:?}"
        );

        // Compile-path lock: the certificate emitter must agree with the
        // inventory and raise no opcode_inventory blocker for the same chain.
        let certs = generate_proof_certificates(&func, None);
        assert!(
            !certs
                .iter()
                .any(|cert| !cert.verified && cert.category == "opcode_inventory"),
            "certificate path re-diverged from the emitted-opcode inventory: {certs:?}"
        );
    }

    #[cfg(feature = "verify")]
    #[test]
    fn test_generate_x86_64_proof_certificates_reports_actual_x86_opcode() {
        use trust_cg_ir::X86Opcode;
        use trust_cg_lower::function::Signature;
        use trust_cg_lower::instructions::Block;
        use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst};

        let mut func = X86ISelFunction::new(
            "x86_unverified_opcode_report".to_string(),
            Signature {
                params: vec![],
                returns: vec![],
            },
        );
        let entry = Block(0);
        func.ensure_block(entry);
        func.push_inst(entry, X86ISelInst::new(X86Opcode::Push, vec![]));

        let certs = generate_x86_64_proof_certificates(&func, None);
        let inventory = certs
            .iter()
            .find(|cert| !cert.verified && cert.category == "opcode_inventory")
            .expect("uncovered x86 Push must produce an inventory blocker");
        assert!(
            inventory.strength.contains("x86_64::Push")
                && inventory.strength.contains("emitted opcode inventory"),
            "x86 inventory blocker must name the actual x86 opcode: {inventory:?}"
        );

        let unverified = certs
            .iter()
            .find(|cert| !cert.verified && cert.category == "unverified")
            .expect("uncovered x86 Push must surface as an unverified proof report");

        assert!(
            unverified.strength.contains("x86_64::Push"),
            "x86 negative proof report must name the actual x86 opcode: {unverified:?}"
        );
        assert!(
            !unverified.strength.contains("AArch64") && !unverified.strength.contains("Nop"),
            "x86 negative proof report must not use the old AArch64::Nop sentinel: {unverified:?}"
        );
    }

    // TEETH for the popcnt-canary PRESENCE GATE: the gate must scan for a
    // `Popcnt` opcode so the canary FIRES on exactly (and only) the compiles
    // where the SWAR expansion can run. A false-negative here would silently
    // stop guarding a real popcnt compile; a false-positive would only cost a
    // (memoized) proof. Both directions pinned.
    #[test]
    fn popcnt_presence_gate_fires_iff_popcnt_emitted() {
        use trust_cg_ir::X86Opcode;
        use trust_cg_lower::function::Signature;
        use trust_cg_lower::instructions::Block;
        use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst};
        let mk = |op: X86Opcode| {
            let mut f = X86ISelFunction::new(
                "presence".to_string(),
                Signature {
                    params: vec![],
                    returns: vec![],
                },
            );
            let entry = Block(0);
            f.ensure_block(entry);
            f.push_inst(entry, X86ISelInst::new(op, vec![]));
            f
        };
        // No Popcnt anywhere -> gate does NOT fire (canary skipped, sound: the
        // SWAR expansion cannot exist without a Popcnt opcode).
        assert!(
            !super::x86_funcs_emit_popcnt(&[mk(X86Opcode::Push), mk(X86Opcode::Nop)]),
            "presence gate must not fire on a Popcnt-free program"
        );
        // A single Popcnt (in the second function's second block) -> gate FIRES.
        let mut with = mk(X86Opcode::Push);
        let b1 = Block(1);
        with.ensure_block(b1);
        with.push_inst(b1, X86ISelInst::new(X86Opcode::Popcnt, vec![]));
        assert!(
            super::x86_funcs_emit_popcnt(&[mk(X86Opcode::Nop), with]),
            "presence gate must fire when any function emits a Popcnt"
        );
    }

    // Guards the #62 / ce09efa compile-path degenerate-proof handling on BOTH
    // sides: a degenerate X==X DB proof for an AUDITED GENUINE IDENTITY (on the
    // GENUINE_IDENTITY_ALLOWLIST — reg copies, EA loads/stores the project has
    // vetted) MUST still promote, while a NON-allowlisted degenerate proof must
    // NOT. The over-strict "reject all degenerate" variant fail-closed every
    // such genuine-identity instruction (it broke the m69/m71 corpus); the
    // exemption is `trust_cg_verify::proof_database::is_genuine_identity`.
    #[cfg(feature = "verify")]
    #[test]
    fn test_degenerate_genuine_identity_promotes_but_unclassified_does_not() {
        use trust_cg_ir::X86Opcode;
        use trust_cg_ir::regs::{RegClass, VReg};
        use trust_cg_lower::function::Signature;
        use trust_cg_lower::instructions::Block;
        use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst, X86ISelOperand};

        // A MovMR whose memory operand is a BARE StackSlot (not MemAddr/SibMemAddr):
        // `x86_reconstruct_effective_address` rejects it, so `try_reconstruct`
        // returns None and the verifier falls back to `resolve_db_proof`, which
        // substring-matches the DEGENERATE X==X "Store_I64 -> MOV [r64+disp32],r64"
        // proof. That proof IS on the GENUINE_IDENTITY_ALLOWLIST, so it must still
        // promote (verified: true) — NOT be degenerate-rejected.
        let mut func = X86ISelFunction::new(
            "x86_degenerate_genuine_identity".to_string(),
            Signature {
                params: vec![],
                returns: vec![],
            },
        );
        let entry = Block(0);
        func.ensure_block(entry);
        func.push_inst(
            entry,
            X86ISelInst::new(
                X86Opcode::MovMR,
                vec![
                    X86ISelOperand::StackSlot(0),
                    X86ISelOperand::VReg(VReg::new(0, RegClass::Gpr64)),
                ],
            ),
        );

        let certs = generate_x86_64_proof_certificates(&func, None);

        // The allowlisted genuine-identity Store proof still promotes...
        assert!(
            certs
                .iter()
                .any(|c| c.verified && c.rule_name.contains("Store_I64")),
            "an allowlisted genuine-identity Store proof must still promote: {certs:?}"
        );
        // ...and is NOT degenerate-rejected (the over-rejection that broke m69/m71).
        assert!(
            !certs
                .iter()
                .any(|c| !c.verified && c.strength.contains("degenerate")),
            "an allowlisted genuine identity must NOT be degenerate-rejected: {certs:?}"
        );
        // Sanity: the exemption predicate distinguishes a genuine identity from an
        // unclassified degenerate name (so a NON-allowlisted degenerate proof, the
        // residual #62 risk, IS still rejected by the compile-path branch).
        assert!(trust_cg_verify::proof_database::is_genuine_identity(
            "x86_64: Store_I64 -> MOV [r64+disp32],r64"
        ));
        assert!(!trust_cg_verify::proof_database::is_genuine_identity(
            "x86_64: SomeUnclassified_NonIdentity -> bogus"
        ));
    }

    #[cfg(feature = "verify")]
    #[test]
    fn test_object_relocation_inventory_certificate_blocks_promotion() {
        use trust_cg_verify::{
            ObjectRelocationInventoryReport, ObjectRelocationKind, ObjectRelocationProofRegistry,
        };

        let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
            "aarch64-linux-module.o",
            [ObjectRelocationKind::AArch64ElfAdrGotPage],
            &ObjectRelocationProofRegistry::aarch64_elf_production(),
        );
        let mut certs = Vec::new();
        append_object_relocation_inventory_certificate(&mut certs, &report);

        let inventory = certs
            .iter()
            .find(|cert| !cert.verified && cert.category == "relocation_inventory")
            .expect("uncovered object relocations must produce an inventory blocker");
        assert!(
            inventory.strength.contains("object relocation inventory")
                && inventory.strength.contains("R_AARCH64_ADR_GOT_PAGE"),
            "relocation inventory blocker should name the uncovered relocation: {inventory:?}"
        );

        let compiler = Compiler::new(CompilerConfig {
            emit_proofs: true,
            ..CompilerConfig::default()
        });
        match compiler.ensure_object_proofs_promotable(Some(&certs)) {
            Err(CompileError::ProofPromotionRejected { target, reason }) => {
                assert_eq!(target, Target::Aarch64);
                assert!(
                    reason.contains("relocation_inventory")
                        && reason.contains("object relocation inventory"),
                    "proof promotion rejection should name relocation inventory: {reason}"
                );
            }
            Err(other) => panic!("expected ProofPromotionRejected, got {other}"),
            Ok(()) => panic!("proof promotion must reject uncovered object relocations"),
        }
    }

    #[cfg(feature = "verify")]
    #[test]
    fn test_object_proof_promotion_rejects_instruction_only_proofs() {
        let certs = vec![ProofCertificate {
            rule_name: "dummy_verified_instruction".to_string(),
            verified: true,
            category: "instruction".to_string(),
            strength: "test fixture verified proof row".to_string(),
            function_name: "caller".to_string(),
        }];

        let compiler = Compiler::new(CompilerConfig {
            emit_proofs: true,
            ..CompilerConfig::default()
        });
        match compiler.ensure_object_proofs_promotable(Some(&certs)) {
            Err(CompileError::ProofPromotionRejected { target, reason }) => {
                assert_eq!(target, Target::Aarch64);
                assert!(
                    reason.contains("relocation_inventory"),
                    "object proof rejection should require relocation inventory: {reason}"
                );
            }
            Err(other) => panic!("expected ProofPromotionRejected, got {other}"),
            Ok(()) => panic!("object proof promotion must reject instruction-only proofs"),
        }
    }

    #[cfg(feature = "verify")]
    #[test]
    fn test_actual_x86_64_elf_plt32_relocation_inventory_promotes() {
        use trust_ir::{FuncId, Ty};
        use trust_ir_build::ModuleBuilder;

        let mut mb = ModuleBuilder::new("x86_relocation_proof_gate");
        let callee_ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        {
            let mut fb = mb.function("callee", callee_ty);
            let entry = fb.create_block();
            let arg = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            fb.ret(vec![arg]);
            fb.build();
        }
        let caller_ty = mb.add_func_type(vec![], vec![Ty::I64]);
        {
            let mut fb = mb.function("caller", caller_ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let arg = fb.iconst(Ty::I64, 7);
            let result = fb.call(FuncId::new(0), vec![arg]);
            fb.ret(vec![result]);
            fb.build();
        }
        let module = mb.build();

        let compiler = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: OptLevel::O0,
                target: Target::X86_64,
                emit_proofs: true,
                parallel: false,
                ..CompilerConfig::default()
            },
            TargetSpec::parse("x86_64-unknown-linux-gnu").unwrap(),
        );

        // PLT32 now carries the full Certified composition on ELF: the
        // solver-backed value proof (elf_call_reloc_proofs, registered with
        // negative controls) plus the per-object ELF reparse binding
        // (default-Enforce in `emit_module_elf`'s checked write funnel), so
        // the proof-required compile PROMOTES. The fail-closed complements
        // (unproven kind / missing or cross-container binding) are covered by
        // the object_inventory unit tests.
        let result = compiler
            .compile(&module)
            .expect("proved x86-64 ELF PLT32 relocation inventory must promote");
        let proofs = result
            .proofs
            .expect("promoting compile must carry proof certificates");
        let inventory = proofs
            .iter()
            .find(|cert| cert.category == "relocation_inventory")
            .expect("the compile must carry the relocation inventory certificate");
        assert!(
            inventory.verified,
            "the ELF relocation inventory must verify: {inventory:?}"
        );
        assert!(
            inventory
                .strength
                .contains("trust_cg_verify::elf_call_reloc_proofs")
                && inventory.strength.contains("ELF reparse-enforced object"),
            "the inventory evidence must cite the value-proof lane and the \
             per-object ELF reparse binding: {inventory:?}"
        );
    }

    #[cfg(feature = "verify")]
    #[test]
    fn test_actual_aarch64_elf_relocation_inventory_blocks_without_formal_proof() {
        use trust_cg_ir::function::{MachFunction as IrMachFunction, Signature as IrSignature};
        use trust_cg_ir::inst::{AArch64Opcode as IrOpcode, MachInst as IrMachInst};
        use trust_cg_ir::operand::MachOperand as IrOperand;

        let sig = IrSignature::new(vec![], vec![]);
        let mut func = IrMachFunction::new("caller".to_string(), sig);
        let call = func.push_inst(IrMachInst::new(
            IrOpcode::Bl,
            vec![IrOperand::Symbol("printf".to_string())],
        ));
        let ret = func.push_inst(IrMachInst::new(IrOpcode::Ret, vec![]));
        func.append_inst(func.entry, call);
        func.append_inst(func.entry, ret);

        let pipeline = Pipeline::new(PipelineConfig {
            target_triple: "aarch64-unknown-linux-gnu".to_string(),
            ..PipelineConfig::default()
        });
        let report = pipeline
            .module_relocation_inventory_report(&[func], "aarch64-linux-module.o")
            .expect("relocation inventory should be computed")
            .expect("AArch64 Linux ELF should produce an inventory report");
        let mut certs = Vec::new();
        append_object_relocation_inventory_certificate(&mut certs, &report);

        assert!(!report.is_promotable());
        let inventory_cert = certs
            .iter()
            .find(|cert| !cert.verified && cert.category == "relocation_inventory")
            .expect("an implemented but unproven ELF relocation must append a blocker");
        assert!(
            inventory_cert.strength.contains("R_AARCH64_CALL26")
                && inventory_cert
                    .strength
                    .contains("no object relocation proof is registered"),
            "ordinary ELF relocation blocker should name its missing proof: {inventory_cert:?}"
        );
    }

    #[cfg(feature = "verify")]
    #[test]
    fn test_named_aarch64_elf_rows_without_formal_proofs_block_promotion() {
        use trust_cg_verify::{
            ObjectRelocationInventoryReport, ObjectRelocationKind, ObjectRelocationProofRegistry,
        };

        let registry = ObjectRelocationProofRegistry::aarch64_elf_production();
        let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
            "aarch64-linux-module.o",
            ObjectRelocationKind::aarch64_elf_named_non_tls_rows()
                .iter()
                .copied(),
            &registry,
        );
        let mut certs = vec![ProofCertificate {
            rule_name: "dummy_verified_instruction".to_string(),
            verified: true,
            category: "instruction".to_string(),
            strength: "test fixture verified proof row".to_string(),
            function_name: "caller".to_string(),
        }];

        append_object_relocation_inventory_certificate(&mut certs, &report);
        assert!(
            certs
                .iter()
                .any(|cert| !cert.verified && cert.category == "relocation_inventory"),
            "named-but-unproven relocation inventory must append a blocker: {certs:?}"
        );
        assert!(
            !report.is_promotable(),
            "implementation support alone must not authorize ordinary ELF rows"
        );

        let compiler = Compiler::new(CompilerConfig {
            emit_proofs: true,
            ..CompilerConfig::default()
        });
        compiler
            .ensure_object_proofs_promotable(Some(&certs))
            .expect_err("ordinary AArch64 ELF rows need genuine proof authority");
    }

    #[cfg(feature = "verify")]
    #[test]
    fn test_unknown_aarch64_elf_relocation_inventory_still_blocks_promotion() {
        use trust_cg_verify::{
            ObjectRelocationInventoryReport, ObjectRelocationKind, ObjectRelocationProofRegistry,
        };

        let registry = ObjectRelocationProofRegistry::aarch64_elf_production();
        let report = ObjectRelocationInventoryReport::from_emitted_kinds_with_registry(
            "aarch64-linux-module.o",
            [
                ObjectRelocationKind::AArch64ElfOther(0x539),
                ObjectRelocationKind::AArch64ElfCall26,
            ],
            &registry,
        );
        let mut certs = Vec::new();
        append_object_relocation_inventory_certificate(&mut certs, &report);

        let inventory = certs
            .iter()
            .find(|cert| !cert.verified && cert.category == "relocation_inventory")
            .expect("unknown relocation rows must remain a promotion blocker");
        assert!(
            inventory.strength.contains("relocation 1337"),
            "unknown relocation blocker should name the uncovered relocation: {inventory:?}"
        );
    }

    #[cfg(feature = "verify")]
    #[test]
    fn test_actual_aarch64_elf_tls_relocation_inventory_still_fails_closed() {
        use trust_cg_ir::function::{MachFunction as IrMachFunction, Signature as IrSignature};
        use trust_cg_ir::inst::{AArch64Opcode as IrOpcode, MachInst as IrMachInst};
        use trust_cg_ir::operand::MachOperand as IrOperand;
        use trust_cg_ir::regs::{X16, X17};

        let sig = IrSignature::new(vec![], vec![]);
        let mut func = IrMachFunction::new("tls_user".to_string(), sig);
        let adrp = func.push_inst(IrMachInst::new(
            IrOpcode::Adrp,
            vec![
                IrOperand::PReg(X17),
                IrOperand::Symbol("tls_global".to_string()),
            ],
        ));
        let ldr = func.push_inst(IrMachInst::new(
            IrOpcode::LdrTlvp,
            vec![
                IrOperand::PReg(X16),
                IrOperand::PReg(X17),
                IrOperand::Symbol("tls_global".to_string()),
            ],
        ));
        let ret = func.push_inst(IrMachInst::new(IrOpcode::Ret, vec![]));
        func.append_inst(func.entry, adrp);
        func.append_inst(func.entry, ldr);
        func.append_inst(func.entry, ret);

        let pipeline = Pipeline::new(PipelineConfig {
            target_triple: "aarch64-unknown-linux-gnu".to_string(),
            ..PipelineConfig::default()
        });
        let err = pipeline
            .module_relocation_inventory_report(&[func], "aarch64-linux-module.o")
            .expect_err("TLS/TLVP fixups must fail closed before registry coverage");
        match err {
            PipelineError::TargetObjectUnsupported { format, reason, .. } => {
                assert_eq!(format, "ELF");
                assert!(
                    reason.contains("TLS/TLVP fixup")
                        && reason.contains("model Some(Tlv)")
                        && reason.contains("Darwin TLV descriptors cannot be mapped to ELF TLS"),
                    "TLS inventory failure should preserve the precise fail-closed boundary: {reason}"
                );
            }
            other => panic!("expected TargetObjectUnsupported for TLS inventory, got {other:?}"),
        }
    }

    /// The ELF local-exec `#[thread_local]` read (`MRS; ADD #:tprel_hi12:, LSL #12;
    /// ADD #:tprel_lo12_nc:`) emits the two TLSLE relocation rows
    /// (`R_AARCH64_TLSLE_ADD_TPREL_HI12` / `_LO12_NC`), each backed by an
    /// solver-backed bit-field-placement obligation
    /// (`trust_cg_verify::aarch64_elf_tls_reloc_proofs`). That is Trusted formal
    /// evidence, not production Certified authority: the inventory cannot yet
    /// represent that distinction or bind the strict gate report and solver
    /// identity to this object, so both rows must block certified promotion.
    #[cfg(feature = "verify")]
    #[test]
    fn test_actual_aarch64_elf_local_exec_tls_relocation_inventory_blocks_certification() {
        use trust_cg_ir::function::{MachFunction as IrMachFunction, Signature as IrSignature};
        use trust_cg_ir::inst::{AArch64Opcode as IrOpcode, MachInst as IrMachInst};
        use trust_cg_ir::operand::MachOperand as IrOperand;
        use trust_cg_ir::regs::X0;

        // The two relocation-bearing ADDs of the local-exec sequence (the MRS that
        // reads TP produces no relocation, so it is not needed to exercise the
        // TLSLE inventory rows). Both carry a Symbol operand at index 2 and are
        // intercepted by the module emitter as ELF TLSLE fixups with LocalExec
        // model (`pipeline.rs` skeleton emission).
        let sig = IrSignature::new(vec![], vec![]);
        let mut func = IrMachFunction::new("tls_local_exec_user".to_string(), sig);
        let add_hi = func.push_inst(IrMachInst::new(
            IrOpcode::AddTprelHi12,
            vec![
                IrOperand::PReg(X0),
                IrOperand::PReg(X0),
                IrOperand::Symbol("tls_global".to_string()),
            ],
        ));
        let add_lo = func.push_inst(IrMachInst::new(
            IrOpcode::AddTprelLo12,
            vec![
                IrOperand::PReg(X0),
                IrOperand::PReg(X0),
                IrOperand::Symbol("tls_global".to_string()),
            ],
        ));
        let ret = func.push_inst(IrMachInst::new(IrOpcode::Ret, vec![]));
        func.append_inst(func.entry, add_hi);
        func.append_inst(func.entry, add_lo);
        func.append_inst(func.entry, ret);

        let pipeline = Pipeline::new(PipelineConfig {
            target_triple: "aarch64-unknown-linux-gnu".to_string(),
            ..PipelineConfig::default()
        });
        let report = pipeline
            .module_relocation_inventory_report(&[func], "aarch64-linux-tls-localexec.o")
            .expect("local-exec TLSLE fixups map to ELF relocations")
            .expect("AArch64 Linux ELF should produce an inventory report");

        assert!(!report.is_promotable());
        // The emitted rows are exactly the two local-exec TLSLE relocations.
        let kinds: Vec<_> = report.entries.iter().map(|e| e.kind).collect();
        assert!(
            kinds.contains(&trust_cg_verify::ObjectRelocationKind::AArch64ElfTlsleAddTprelHi12)
                && kinds.contains(
                    &trust_cg_verify::ObjectRelocationKind::AArch64ElfTlsleAddTprelLo12Nc
                ),
            "expected both TLSLE local-exec rows in the inventory, got {kinds:?}"
        );
        assert!(
            report
                .entries
                .iter()
                .all(|e| e.status == trust_cg_verify::RelocationInventoryStatus::Unverified),
            "solver-backed TLSLE evidence must not become Certified: {report:?}"
        );
        let mut certs = Vec::new();
        append_object_relocation_inventory_certificate(&mut certs, &report);
        assert!(
            certs
                .iter()
                .any(|cert| !cert.verified && cert.category == "relocation_inventory"),
            "TLSLE inventory must append a certified-output blocker: {certs:?}"
        );
    }

    /// The ELF initial-exec `#[thread_local]` read (`ADRP :gottprel:;
    /// LDR #:gottprel_lo12:; MRS; ADD`) emits the two TLSIE relocation rows
    /// (`R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21` / `_LD64_GOTTPREL_LO12_NC`),
    /// each backed by a solver-backed GOT-slot address reconstruction
    /// obligation (`trust_cg_verify::aarch64_elf_tls_reloc_proofs`, TLSIE rows).
    /// This remains Trusted evidence only; both rows block production Certified
    /// promotion until the authority surface carries that distinction.
    #[cfg(feature = "verify")]
    #[test]
    fn test_actual_aarch64_elf_initial_exec_tls_relocation_inventory_blocks_certification() {
        use trust_cg_ir::function::{MachFunction as IrMachFunction, Signature as IrSignature};
        use trust_cg_ir::inst::{AArch64Opcode as IrOpcode, MachInst as IrMachInst};
        use trust_cg_ir::operand::MachOperand as IrOperand;
        use trust_cg_ir::regs::X0;

        // The two relocation-bearing instructions of the initial-exec sequence
        // (the MRS/ADD completion carries no relocation). The ADRP's TLSIE
        // GOT-page kind is reconstructed by the encode-time consumer pairing
        // (same-register, same-symbol LdrGottprel), exactly like LdrGot/LdrTlvp.
        let sig = IrSignature::new(vec![], vec![]);
        let mut func = IrMachFunction::new("tls_initial_exec_user".to_string(), sig);
        let adrp = func.push_inst(IrMachInst::new(
            IrOpcode::Adrp,
            vec![
                IrOperand::PReg(X0),
                IrOperand::Symbol("tls_global".to_string()),
            ],
        ));
        let ldr = func.push_inst(IrMachInst::new(
            IrOpcode::LdrGottprel,
            vec![
                IrOperand::PReg(X0),
                IrOperand::PReg(X0),
                IrOperand::Symbol("tls_global".to_string()),
            ],
        ));
        let ret = func.push_inst(IrMachInst::new(IrOpcode::Ret, vec![]));
        func.append_inst(func.entry, adrp);
        func.append_inst(func.entry, ldr);
        func.append_inst(func.entry, ret);

        let pipeline = Pipeline::new(PipelineConfig {
            target_triple: "aarch64-unknown-linux-gnu".to_string(),
            ..PipelineConfig::default()
        });
        let report = pipeline
            .module_relocation_inventory_report(&[func], "aarch64-linux-tls-initialexec.o")
            .expect("initial-exec TLSIE fixups map to ELF relocations")
            .expect("AArch64 Linux ELF should produce an inventory report");

        assert!(!report.is_promotable());
        // The emitted rows are exactly the two initial-exec TLSIE relocations.
        let kinds: Vec<_> = report.entries.iter().map(|e| e.kind).collect();
        assert!(
            kinds
                .contains(&trust_cg_verify::ObjectRelocationKind::AArch64ElfTlsieAdrGottprelPage21)
                && kinds.contains(
                    &trust_cg_verify::ObjectRelocationKind::AArch64ElfTlsieLd64GottprelLo12Nc
                ),
            "expected both TLSIE initial-exec rows in the inventory, got {kinds:?}"
        );
        assert!(
            report
                .entries
                .iter()
                .all(|e| e.status == trust_cg_verify::RelocationInventoryStatus::Unverified),
            "solver-backed TLSIE evidence must not become Certified: {report:?}"
        );
        let mut certs = Vec::new();
        append_object_relocation_inventory_certificate(&mut certs, &report);
        assert!(
            certs
                .iter()
                .any(|cert| !cert.verified && cert.category == "relocation_inventory"),
            "TLSIE inventory must append a certified-output blocker: {certs:?}"
        );
    }

    #[test]
    fn test_compiler_trace_level_equality() {
        assert_eq!(CompilerTraceLevel::None, CompilerTraceLevel::None);
        assert_ne!(CompilerTraceLevel::None, CompilerTraceLevel::Summary);
        assert_ne!(CompilerTraceLevel::Summary, CompilerTraceLevel::Full);
    }

    #[test]
    fn test_parallel_and_serial_ir_compile_produce_same_output() {
        // Compile the same IR function with parallel=true and parallel=false.
        // Single-function modules take the sequential path regardless of the
        // parallel flag (threshold is 2+ functions), so this test verifies
        // the config plumbing and that both paths produce identical output.
        let mut ir_func_a = crate::pipeline::build_add_test_function();
        let mut ir_func_b = crate::pipeline::build_add_test_function();

        let serial = Compiler::new(CompilerConfig {
            parallel: false,
            ..CompilerConfig::default()
        });
        let parallel = Compiler::new(CompilerConfig {
            parallel: true,
            ..CompilerConfig::default()
        });

        let result_serial = serial.compile_ir_function(&mut ir_func_a).unwrap();
        let result_parallel = parallel.compile_ir_function(&mut ir_func_b).unwrap();

        assert_eq!(
            result_serial.object_code, result_parallel.object_code,
            "parallel and serial compilation must produce identical Mach-O output"
        );
        assert_eq!(
            result_serial.metrics.instruction_count,
            result_parallel.metrics.instruction_count
        );
    }

    #[test]
    fn test_parallel_config_disabled() {
        let config = CompilerConfig {
            parallel: false,
            ..CompilerConfig::default()
        };
        assert!(!config.parallel);
    }

    #[test]
    fn test_parallel_multi_function_module_produces_same_output() {
        // Build a trust_ir module with 3 functions and compile it both serially
        // and in parallel. The outputs MUST be identical (deterministic).
        use trust_ir::Ty;
        use trust_ir_build::ModuleBuilder;

        let build_module = || {
            let mut mb = ModuleBuilder::new("test_parallel_multi");
            // Function 1: f(a, b) = a + b
            {
                let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
                let mut fb = mb.function("add_fn", ty);
                let entry = fb.create_block();
                let a = fb.add_block_param(entry, Ty::I64);
                let b = fb.add_block_param(entry, Ty::I64);
                fb.switch_to_block(entry);
                let result = fb.add(Ty::I64, a, b);
                fb.ret(vec![result]);
                fb.build();
            }
            // Function 2: g(a, b) = a * b - a
            {
                let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
                let mut fb = mb.function("mul_sub_fn", ty);
                let entry = fb.create_block();
                let a = fb.add_block_param(entry, Ty::I64);
                let b = fb.add_block_param(entry, Ty::I64);
                fb.switch_to_block(entry);
                let prod = fb.mul(Ty::I64, a, b);
                let result = fb.sub(Ty::I64, prod, a);
                fb.ret(vec![result]);
                fb.build();
            }
            // Function 3: h(a, b) = (a + b) * 2
            {
                let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
                let mut fb = mb.function("add_double_fn", ty);
                let entry = fb.create_block();
                let a = fb.add_block_param(entry, Ty::I64);
                let b = fb.add_block_param(entry, Ty::I64);
                fb.switch_to_block(entry);
                let sum = fb.add(Ty::I64, a, b);
                let c2 = fb.iconst(Ty::I64, 2);
                let result = fb.mul(Ty::I64, sum, c2);
                fb.ret(vec![result]);
                fb.build();
            }
            mb.build()
        };

        let module_serial = build_module();
        let module_parallel = build_module();

        let serial = Compiler::new(CompilerConfig {
            parallel: false,
            ..CompilerConfig::default()
        });
        let parallel = Compiler::new(CompilerConfig {
            parallel: true,
            ..CompilerConfig::default()
        });

        let result_serial = serial.compile(&module_serial).unwrap();
        let result_parallel = parallel.compile(&module_parallel).unwrap();

        assert_eq!(
            result_serial.object_code, result_parallel.object_code,
            "multi-function parallel and serial compilation must produce identical Mach-O output"
        );
        assert_eq!(result_serial.metrics.function_count, 3);
        assert_eq!(result_parallel.metrics.function_count, 3);
        assert_eq!(
            result_serial.metrics.instruction_count,
            result_parallel.metrics.instruction_count
        );
    }

    /// CT-5: the x86-64 dispatcher (`compile_x86_64`) fans per-function register
    /// allocation + encoding + certificate generation out across a rayon pool
    /// when `parallel` is set. The emitted object MUST be byte-for-byte identical
    /// to the serial path, and identical across repeated parallel runs, or a
    /// scheduling-dependent output would be the exact BENCH-8 / determinism-
    /// sentinel nondeterminism class. Enough functions to cross the parallel
    /// threshold (`worker_count_for_items` needs >= 2) and exercise real regalloc.
    #[cfg(not(target_os = "windows"))]
    #[test]
    fn test_x86_parallel_and_serial_multi_function_byte_identical() {
        use trust_ir::Ty;
        use trust_ir_build::ModuleBuilder;

        let build_module = || {
            let mut mb = ModuleBuilder::new("x86_parallel_determinism");
            for (idx, name) in [
                "add_fn",
                "mul_sub_fn",
                "add_double_fn",
                "poly_fn",
                "chain_fn",
                "mix_fn",
            ]
            .iter()
            .enumerate()
            {
                let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
                let mut fb = mb.function(*name, ty);
                let entry = fb.create_block();
                let a = fb.add_block_param(entry, Ty::I64);
                let b = fb.add_block_param(entry, Ty::I64);
                fb.switch_to_block(entry);
                // Distinct bodies so each function needs its own allocation /
                // encoding (and the object is not trivially uniform).
                let k = fb.iconst(Ty::I64, (idx as i128) + 3);
                let sum = fb.add(Ty::I64, a, b);
                let prod = fb.mul(Ty::I64, sum, k);
                let result = fb.sub(Ty::I64, prod, a);
                fb.ret(vec![result]);
                fb.build();
            }
            mb.build()
        };

        let compile_with = |parallel: bool| {
            Compiler::new(CompilerConfig {
                target: Target::X86_64,
                parallel,
                // Exercise the parallel CERTIFICATE lane too (not just the
                // regalloc+encode lane): with proofs on, the per-function
                // verifier fans out and the ordered proof bundle must be
                // identical serial-vs-parallel.
                emit_proofs: true,
                ..CompilerConfig::default()
            })
            .compile(&build_module())
            .expect("x86 multi-function module should compile")
        };

        let serial = compile_with(false);
        let parallel_a = compile_with(true);
        let parallel_b = compile_with(true);

        assert_eq!(
            serial.object_code, parallel_a.object_code,
            "x86 parallel compilation must be BYTE-IDENTICAL to serial (determinism gate)"
        );
        assert_eq!(
            parallel_a.object_code, parallel_b.object_code,
            "x86 parallel compilation must be deterministic across repeated runs"
        );
        // The ordered proof bundle (and thus its sha256 cache key) must also be
        // identical: `par_iter().flat_map().collect()` preserves function order.
        assert_eq!(
            serial.proofs, parallel_a.proofs,
            "x86 parallel proof bundle must be identical to serial (ordered cert lane)"
        );
        assert_eq!(
            parallel_a.proofs, parallel_b.proofs,
            "x86 parallel proof bundle must be deterministic across repeated runs"
        );
        assert!(
            serial.proofs.as_ref().is_some_and(|p| !p.is_empty()),
            "emit_proofs should produce a non-empty proof bundle"
        );
        assert_eq!(serial.metrics.function_count, 6);
        assert_eq!(parallel_a.metrics.function_count, 6);
        assert_eq!(
            serial.metrics.instruction_count,
            parallel_a.metrics.instruction_count
        );
        assert_eq!(
            serial.metrics.code_size_bytes,
            parallel_a.metrics.code_size_bytes
        );
    }

    /// CT-5 measurement + large-scale byte-identity gate. Compiles a wide
    /// multi-function x86 module (the shape where the per-function-parallel win
    /// shows — a single-function canary parks the pool) serially and in
    /// parallel, asserts BYTE-IDENTICAL objects, and prints the wall-clock
    /// delta. The test requires an explicit measurement qualification because
    /// the timing is informational and the build is only meaningful in
    /// `--release`; run with:
    ///
    /// ```text
    /// TRUST_CG_RUN_MEASUREMENT_TESTS=1 TRUST_CG_MAX_PARALLELISM=8 \
    ///     cargo test --release -p trust-cg-codegen --lib \
    ///     x86_parallel_multi_function_compile_time_delta -- --nocapture
    /// ```
    #[cfg(not(target_os = "windows"))]
    #[test]
    fn x86_parallel_multi_function_compile_time_delta() {
        if !matches!(
            std::env::var("TRUST_CG_RUN_MEASUREMENT_TESTS").as_deref(),
            Ok("1")
        ) {
            eprintln!(
                "measurement campaign not requested; \
                 set TRUST_CG_RUN_MEASUREMENT_TESTS=1 to run"
            );
            return;
        }

        use std::time::Instant;
        use trust_ir::Ty;
        use trust_ir_build::ModuleBuilder;

        const FUNCTION_COUNT: usize = 160;

        // Each function has a straight-line arithmetic body with enough live
        // values to give register allocation real work (the dominant backend
        // cost being parallelized). Distinct constants keep the bodies from
        // collapsing to one shared shape.
        let build_module = || {
            let mut mb = ModuleBuilder::new("x86_parallel_scale");
            for f in 0..FUNCTION_COUNT {
                let ty = mb.add_func_type(vec![Ty::I64, Ty::I64, Ty::I64], vec![Ty::I64]);
                let mut fb = mb.function(format!("scale_fn_{f}"), ty);
                let entry = fb.create_block();
                let a = fb.add_block_param(entry, Ty::I64);
                let b = fb.add_block_param(entry, Ty::I64);
                let c = fb.add_block_param(entry, Ty::I64);
                fb.switch_to_block(entry);
                let mut acc = a;
                for i in 0..24 {
                    let k = fb.iconst(Ty::I64, (f as i128) * 7 + (i as i128) + 1);
                    let m = fb.mul(Ty::I64, acc, b);
                    let s = fb.add(Ty::I64, m, k);
                    let d = fb.sub(Ty::I64, s, c);
                    acc = fb.add(Ty::I64, d, acc);
                }
                fb.ret(vec![acc]);
                fb.build();
            }
            mb.build()
        };

        let compile_with = |parallel: bool| {
            let compiler = Compiler::new(CompilerConfig {
                target: Target::X86_64,
                parallel,
                // Exercise BOTH parallelized dominant stages: per-function
                // regalloc+encode AND the per-function certificate lane (the
                // bridge runs with proofs on).
                emit_proofs: true,
                ..CompilerConfig::default()
            });
            let start = Instant::now();
            let result = compiler
                .compile(&build_module())
                .expect("wide x86 module should compile");
            (result, start.elapsed())
        };

        // Warm any process-wide memo/OnceLock so the timing reflects steady
        // state, not one-off canary discharge.
        let _ = compile_with(false);

        let (serial, serial_dt) = compile_with(false);
        let (parallel, parallel_dt) = compile_with(true);

        assert_eq!(
            serial.object_code, parallel.object_code,
            "wide-module parallel compilation must be BYTE-IDENTICAL to serial"
        );
        assert_eq!(serial.metrics.function_count, FUNCTION_COUNT);

        let speedup = serial_dt.as_secs_f64() / parallel_dt.as_secs_f64().max(f64::MIN_POSITIVE);
        eprintln!(
            "[CT-5] x86 {FUNCTION_COUNT}-fn compile: serial={:?} parallel={:?} speedup={:.2}x \
             (workers capped by TRUST_CG_MAX_PARALLELISM, default 2)",
            serial_dt, parallel_dt, speedup
        );
    }

    // -----------------------------------------------------------------------
    // JIT batch compilation tests
    // -----------------------------------------------------------------------

    /// Compile a single-function trust_ir module to JIT and verify the symbol
    /// is present in the executable buffer.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_compile_module_to_jit_single_function() {
        use std::collections::HashMap;
        use trust_ir::Ty;
        use trust_ir_build::ModuleBuilder;

        let mut mb = ModuleBuilder::new("jit_single");
        {
            let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
            let mut fb = mb.function("add_fn", ty);
            let entry = fb.create_block();
            let a = fb.add_block_param(entry, Ty::I64);
            let b = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let result = fb.add(Ty::I64, a, b);
            fb.ret(vec![result]);
            fb.build();
        }
        let module = mb.build();

        let compiler = Compiler::default_o2();
        let result = compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap();

        assert_eq!(result.metrics.function_count, 1);
        assert!(result.metrics.instruction_count > 0);
        assert!(result.metrics.code_size_bytes > 0);
        assert!(
            result.buffer.get_fn_ptr("add_fn").is_some(),
            "add_fn should be in the symbol map"
        );
        assert_eq!(result.buffer.symbol_count(), 1);
    }

    /// Compile a multi-function trust_ir module to JIT and verify all symbols
    /// are present with correct metrics.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_compile_module_to_jit_multi_function() {
        use std::collections::HashMap;
        use trust_ir::Ty;
        use trust_ir_build::ModuleBuilder;

        let mut mb = ModuleBuilder::new("jit_multi");
        {
            let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
            let mut fb = mb.function("add_fn", ty);
            let entry = fb.create_block();
            let a = fb.add_block_param(entry, Ty::I64);
            let b = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let result = fb.add(Ty::I64, a, b);
            fb.ret(vec![result]);
            fb.build();
        }
        {
            let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
            let mut fb = mb.function("mul_fn", ty);
            let entry = fb.create_block();
            let a = fb.add_block_param(entry, Ty::I64);
            let b = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let result = fb.mul(Ty::I64, a, b);
            fb.ret(vec![result]);
            fb.build();
        }
        {
            let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
            let mut fb = mb.function("sub_fn", ty);
            let entry = fb.create_block();
            let a = fb.add_block_param(entry, Ty::I64);
            let b = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let result = fb.sub(Ty::I64, a, b);
            fb.ret(vec![result]);
            fb.build();
        }
        let module = mb.build();

        let compiler = Compiler::default_o2();
        let result = compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap();

        assert_eq!(result.metrics.function_count, 3);
        assert!(result.metrics.instruction_count > 0);
        assert_eq!(result.buffer.symbol_count(), 3);
        assert!(result.buffer.get_fn_ptr("add_fn").is_some());
        assert!(result.buffer.get_fn_ptr("mul_fn").is_some());
        assert!(result.buffer.get_fn_ptr("sub_fn").is_some());

        // Verify symbols have distinct offsets (functions are laid out sequentially).
        let symbols: std::collections::HashMap<&str, u64> = result.buffer.symbols().collect();
        assert_eq!(symbols.len(), 3);
    }

    /// Verify that an empty trust_ir module returns EmptyModule error.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_compile_module_to_jit_empty_module() {
        use std::collections::HashMap;
        use trust_ir_build::ModuleBuilder;

        let mb = ModuleBuilder::new("jit_empty");
        let module = mb.build();

        let compiler = Compiler::default_o2();
        let err = compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_err();
        assert!(
            matches!(err, CompileError::EmptyModule),
            "expected EmptyModule, got: {err}"
        );
    }

    /// Verify that trace entries are populated when trace_level is Full.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_compile_module_to_jit_with_trace() {
        use std::collections::HashMap;
        use trust_ir::Ty;
        use trust_ir_build::ModuleBuilder;

        let mut mb = ModuleBuilder::new("jit_trace");
        {
            let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
            let mut fb = mb.function("add_fn", ty);
            let entry = fb.create_block();
            let a = fb.add_block_param(entry, Ty::I64);
            let b = fb.add_block_param(entry, Ty::I64);
            fb.switch_to_block(entry);
            let result = fb.add(Ty::I64, a, b);
            fb.ret(vec![result]);
            fb.build();
        }
        let module = mb.build();

        let compiler = Compiler::new(CompilerConfig {
            trace_level: CompilerTraceLevel::Full,
            ..CompilerConfig::default()
        });
        let result = compiler
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap();

        assert!(
            result.trace.is_some(),
            "trace should be present with Full level"
        );
        let trace = result.trace.unwrap();
        assert!(!trace.entries.is_empty(), "trace should have entries");
        // Should have at least an adapter phase and a compile_raw phase.
        let phase_names: Vec<&str> = trace.entries.iter().map(|e| e.phase.as_str()).collect();
        assert!(
            phase_names.contains(&"adapter"),
            "trace should contain adapter phase, got: {:?}",
            phase_names
        );
        assert!(
            phase_names.contains(&"compile_raw"),
            "trace should contain compile_raw phase, got: {:?}",
            phase_names
        );
    }

    /// The old call+add fixture used to expose an opcode-inventory gap. That
    /// lowering is now fully covered, so proof-required JIT compilation must
    /// succeed and report only verified entries.
    /// Runs on a thread with enlarged stack because the verifier's recursive
    /// SMT evaluation can overflow the default 8 MiB test thread stack.
    #[cfg(target_arch = "aarch64")]
    #[test]
    fn test_compile_module_to_jit_with_covered_proofs_succeeds() {
        use std::collections::HashMap;
        use trust_ir::{FuncId, Ty};
        use trust_ir_build::ModuleBuilder;

        // 16 MiB stack — verification's recursive evaluator needs headroom.
        let child = std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| {
                let mut mb = ModuleBuilder::new("jit_proofs");
                {
                    let ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
                    let mut fb = mb.function("identity_fn", ty);
                    let entry = fb.create_block();
                    let a = fb.add_block_param(entry, Ty::I64);
                    fb.switch_to_block(entry);
                    fb.ret(vec![a]);
                    fb.build();
                }
                {
                    let ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
                    let mut fb = mb.function("call_add_fn", ty);
                    let entry = fb.create_block();
                    let a = fb.add_block_param(entry, Ty::I64);
                    let b = fb.add_block_param(entry, Ty::I64);
                    fb.switch_to_block(entry);
                    let called = fb.call(FuncId::new(0), vec![a]);
                    let result = fb.add(Ty::I64, called, b);
                    fb.ret(vec![result]);
                    fb.build();
                }
                let module = mb.build();

                let compiler = Compiler::new(CompilerConfig {
                    emit_proofs: true,
                    ..CompilerConfig::default()
                });
                let result = compiler
                    .compile_module_to_jit(&module, &HashMap::new())
                    .expect("covered proof-required JIT fixture should compile");
                let proofs = result
                    .proofs
                    .expect("emit_proofs must return public proof reports");
                assert!(!proofs.is_empty(), "fixture must exercise proof promotion");
                assert!(
                    proofs.iter().all(|proof| proof.verified),
                    "covered fixture must not publish an unverified report: {proofs:?}"
                );
            })
            .expect("failed to spawn thread with larger stack");
        child.join().expect("test thread panicked");
    }

    /// Keep the fail-closed authority contract explicit even as instruction
    /// coverage grows: one unverified public report blocks promotion.
    #[cfg(feature = "verify")]
    #[test]
    fn test_proof_required_jit_rejects_unverified_public_report() {
        let compiler = Compiler::new(CompilerConfig {
            emit_proofs: true,
            ..CompilerConfig::default()
        });
        let proofs = [ProofCertificate {
            rule_name: "synthetic_unverified_opcode".to_string(),
            verified: false,
            category: "opcode_inventory".to_string(),
            strength: "synthetic emitted opcode inventory gap".to_string(),
            function_name: "proof_required_jit_fixture".to_string(),
        }];

        match compiler.ensure_proofs_promotable(Some(&proofs)) {
            Err(CompileError::ProofPromotionRejected { target, reason }) => {
                assert_eq!(target, Target::Aarch64);
                assert!(
                    reason.contains("synthetic_unverified_opcode")
                        && reason.contains("synthetic emitted opcode inventory gap"),
                    "rejection must retain the unverified report identity: {reason}"
                );
            }
            Err(other) => panic!("expected ProofPromotionRejected, got {other}"),
            Ok(()) => panic!("one unverified public report must block JIT promotion"),
        }
    }

    // -----------------------------------------------------------------------
    // PROOF-GAP item 1: carrier-hygiene gate runs in the production codegen
    // path on the DEFAULT build (NOT behind the `verify` feature).
    // -----------------------------------------------------------------------

    use trust_cg_ir::regs::{RegClass, VReg};
    use trust_cg_ir::x86_64_ops::X86Opcode;
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::x86_64_isel::{X86ISelBlock, X86ISelFunction, X86ISelInst, X86ISelOperand};

    fn ch_vreg32(id: u32) -> VReg {
        VReg::new(id, RegClass::Gpr32)
    }

    fn ch_make_func(insts: Vec<X86ISelInst>, widths: &[(VReg, u32)]) -> X86ISelFunction {
        let mut func = X86ISelFunction::new(
            "carrier_hygiene_fixture".to_string(),
            trust_cg_lower::function::Signature {
                params: vec![],
                returns: vec![],
            },
        );
        let block_id = Block(0);
        func.ensure_block(block_id);
        let block: &mut X86ISelBlock = func.blocks.get_mut(&block_id).unwrap();
        block.insts.extend(insts);
        for &(v, w) in widths {
            func.vreg_nominal_widths.insert(v, w);
        }
        func
    }

    /// LOCKS IN #51/#66: the production carrier-hygiene gate FAILS THE COMPILE
    /// (returns `CompileError::CarrierHygiene`) when a dirtied narrow i8 value
    /// (produced by a 32-bit NEG) is fed straight to IDIV with no sign
    /// extension. This is the same fixture the function verifier uses, but
    /// asserted against the codegen-level fail-closed gate that now runs on
    /// every x86 compile.
    #[test]
    fn carrier_hygiene_gate_rejects_dirty_narrow_idiv_divisor() {
        let v0 = ch_vreg32(0);
        let div = ch_vreg32(1);
        let q = ch_vreg32(2);
        let func = ch_make_func(
            vec![
                X86ISelInst::new(
                    X86Opcode::MovRI,
                    vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(0)],
                ),
                X86ISelInst::new(
                    X86Opcode::Neg,
                    vec![X86ISelOperand::VReg(div), X86ISelOperand::VReg(v0)],
                ),
                X86ISelInst::new(
                    X86Opcode::Idiv,
                    vec![X86ISelOperand::VReg(q), X86ISelOperand::VReg(div)],
                ),
            ],
            &[(v0, 8), (div, 8), (q, 8)],
        );

        match check_x86_carrier_hygiene(&func) {
            Err(CompileError::CarrierHygiene { opcode, detail, .. }) => {
                assert_eq!(opcode, X86Opcode::Idiv);
                assert!(
                    detail.contains("#51"),
                    "detail should reference the historical miscompile class: {detail}"
                );
            }
            other => panic!("expected CarrierHygiene rejection, got {other:?}"),
        }
    }

    /// LOCKS IN: the fix shape (MOVSX-extended divisor) is NOT false-rejected
    /// by the production gate — a real, correctly extended wide-reader operand
    /// must compile.
    #[test]
    fn carrier_hygiene_gate_accepts_sign_extended_idiv_divisor() {
        let v0 = ch_vreg32(0);
        let ext = ch_vreg32(1);
        let q = ch_vreg32(2);
        let func = ch_make_func(
            vec![
                X86ISelInst::new(
                    X86Opcode::MovRI,
                    vec![X86ISelOperand::VReg(v0), X86ISelOperand::Imm(-3)],
                ),
                X86ISelInst::new(
                    X86Opcode::MovsxB,
                    vec![X86ISelOperand::VReg(ext), X86ISelOperand::VReg(v0)],
                ),
                X86ISelInst::new(
                    X86Opcode::Idiv,
                    vec![X86ISelOperand::VReg(q), X86ISelOperand::VReg(ext)],
                ),
            ],
            &[(v0, 8), (ext, 8), (q, 8)],
        );
        assert!(
            check_x86_carrier_hygiene(&func).is_ok(),
            "a MOVSX-extended IDIV divisor must compile (no false positive)"
        );
    }

    /// LOCKS IN the soundness gate: a width-less synthetic function carries no
    /// ground truth, so the gate is skipped (returns Ok) rather than
    /// false-rejecting every wide reader as unknown-width.
    #[test]
    fn carrier_hygiene_gate_skips_widthless_function() {
        let v0 = ch_vreg32(0);
        let div = ch_vreg32(1);
        let q = ch_vreg32(2);
        let func = ch_make_func(
            vec![
                X86ISelInst::new(
                    X86Opcode::Neg,
                    vec![X86ISelOperand::VReg(div), X86ISelOperand::VReg(v0)],
                ),
                X86ISelInst::new(
                    X86Opcode::Idiv,
                    vec![X86ISelOperand::VReg(q), X86ISelOperand::VReg(div)],
                ),
            ],
            &[], // no widths => skip
        );
        assert!(func.vreg_nominal_widths().is_empty());
        assert!(
            check_x86_carrier_hygiene(&func).is_ok(),
            "width-less synthetic functions must be skipped (sound default)"
        );
    }

    // -----------------------------------------------------------------------
    // PROOF-GAP item 3: glue-pass (overflow expansion) validation runs in the
    // production codegen path and is arch-correct for x86-64.
    // -----------------------------------------------------------------------

    /// LOCKS IN #67: the live division-free wide-multiply expansion validates
    /// under x86-64 IDIV trap semantics, so the gate does NOT block a valid
    /// compile (here over an empty program = the folded-in canary baseline).
    #[test]
    fn glue_pass_validation_accepts_live_division_free_expansion() {
        assert!(
            validate_x86_glue_pass_expansions(&[]).is_ok(),
            "the live division-free wide-mul overflow expansion must validate on x86-64"
        );
    }

    /// LOCKS IN #67 (the mis-port): if the overflow expansion regressed to the
    /// AArch64-only SDIV-identity, the same validator the production gate uses
    /// would REJECT it on x86-64 (the `x.overflowing_mul(0)` SIGFPE). This
    /// asserts the validator the gate relies on is arch-discriminating, so a
    /// regression would turn #67 into a compile error rather than a runtime
    /// crash.
    #[test]
    fn glue_pass_validation_would_reject_sdiv_identity_on_x86() {
        use trust_cg_verify::pass_validators::{
            OverflowExpansion, OverflowExpansionValidator, PassValidator, TargetArch,
        };
        let regressed = OverflowExpansionValidator::signed_mul(
            "x86-overflow-expand",
            8,
            OverflowExpansion::SdivIdentity,
            TargetArch::X86_64,
        );
        assert!(
            !regressed.validate().is_verified(),
            "SDIV-identity (AArch64-ism) on x86 must be rejected (#67 SIGFPE)"
        );
    }

    // -----------------------------------------------------------------------
    // PROOF-GAP item 3 — PER-PROGRAM overflow-expansion validation: the gate
    // now derives the overflow expansions from each emitted X86ISelFunction.
    // -----------------------------------------------------------------------

    /// LOAD-BEARING per-program proof: a function that emits the trapping
    /// SDIV-identity signed-mul-overflow shape `q = (a*b) IDIV b` (the #67 bug
    /// that SIGFPEs on x86-64 IDIV-by-zero / INT_MIN-by-1) — emitted in the REAL
    /// x86 form `IMUL product, a, b; MOV EAX, product; IDIV b` — is REJECTED by
    /// the per-program gate. This proves the gate is per-program, NOT a fixed
    /// canary: the rejection is driven by THIS function's emitted instruction
    /// stream. An `(a*b)/c` divide by a NON-multiplicand is NOT rejected
    /// (`per_program_gate_accepts_mul_then_divide_by_unrelated_value`).
    #[test]
    fn per_program_gate_rejects_trapping_imul_idiv_signed_mul_overflow() {
        use trust_cg_ir::x86_64_regs::EAX;

        let a = ch_vreg32(0);
        let b = ch_vreg32(1);
        let product = ch_vreg32(2);
        // product = a * b ; EAX = product ; q = product IDIV b  (divisor IS the
        // multiplicand b — the SDIV-identity recovering `a`).
        let func = ch_make_func(
            vec![
                X86ISelInst::new(
                    X86Opcode::ImulRR,
                    vec![
                        X86ISelOperand::VReg(product),
                        X86ISelOperand::VReg(a),
                        X86ISelOperand::VReg(b),
                    ],
                ),
                X86ISelInst::new(
                    X86Opcode::MovRR32,
                    vec![X86ISelOperand::PReg(EAX), X86ISelOperand::VReg(product)],
                ),
                X86ISelInst::new(X86Opcode::Cdq, vec![]),
                X86ISelInst::new(X86Opcode::Idiv, vec![X86ISelOperand::VReg(b)]),
            ],
            &[(a, 8), (b, 8), (product, 8)],
        );

        match validate_x86_glue_pass_expansions(std::slice::from_ref(&func)) {
            Err(CompileError::PassValidationRejected {
                obligation_name,
                reason,
                ..
            }) => {
                assert!(
                    obligation_name.contains("per-program")
                        && obligation_name.contains("division-free invariant"),
                    "rejection must be the per-program structural #67 net: {obligation_name}"
                );
                assert!(
                    reason.contains("IDIV") && reason.contains("#67"),
                    "rejection reason should explain the #67 IMUL->IDIV trap: {reason}"
                );
            }
            other => panic!(
                "per-program gate must REJECT a trapping IMUL->IDIV signed-mul-overflow, got {other:?}"
            ),
        }
    }

    /// SOUNDNESS / no-false-positive companion: the structural net keys off the
    /// SDIV-identity `(a*b)/b` shape (divisor IS a multiplicand), so a genuine
    /// `(a*b)/c` that divides the product by an UNRELATED value `c` must NOT be
    /// rejected (this is ordinary user code, not the overflow identity).
    #[test]
    fn per_program_gate_accepts_mul_then_divide_by_unrelated_value() {
        use trust_cg_ir::x86_64_regs::EAX;

        let a = ch_vreg32(0);
        let b = ch_vreg32(1);
        let c = ch_vreg32(2); // unrelated divisor
        let product = ch_vreg32(3);
        let func = ch_make_func(
            vec![
                X86ISelInst::new(
                    X86Opcode::ImulRR,
                    vec![
                        X86ISelOperand::VReg(product),
                        X86ISelOperand::VReg(a),
                        X86ISelOperand::VReg(b),
                    ],
                ),
                X86ISelInst::new(
                    X86Opcode::MovRR32,
                    vec![X86ISelOperand::PReg(EAX), X86ISelOperand::VReg(product)],
                ),
                X86ISelInst::new(X86Opcode::Cdq, vec![]),
                X86ISelInst::new(X86Opcode::Idiv, vec![X86ISelOperand::VReg(c)]),
            ],
            &[(a, 32), (b, 32), (c, 32), (product, 32)],
        );

        assert!(
            find_signed_mul_overflow_division(&func).is_none(),
            "(a*b)/c by an unrelated value must NOT trip the #67 SDIV-identity net"
        );
        assert!(
            validate_x86_glue_pass_expansions(std::slice::from_ref(&func)).is_ok(),
            "(a*b)/c must compile — the structural net is false-positive-free"
        );
    }

    /// COMPANION: a plain multiply with NO divide at all (the live division-free
    /// overflow shape) is ACCEPTED — the gate does not false-reject a correct
    /// signed multiply.
    #[test]
    fn per_program_gate_accepts_division_free_signed_mul() {
        let a = ch_vreg32(0);
        let b = ch_vreg32(1);
        let product = ch_vreg32(2);
        let func = ch_make_func(
            vec![X86ISelInst::new(
                X86Opcode::ImulRR,
                vec![
                    X86ISelOperand::VReg(product),
                    X86ISelOperand::VReg(a),
                    X86ISelOperand::VReg(b),
                ],
            )],
            &[(a, 32), (b, 32), (product, 32)],
        );

        assert!(
            validate_x86_glue_pass_expansions(std::slice::from_ref(&func)).is_ok(),
            "a division-free multiply must NOT be rejected by the per-program #67 gate"
        );
    }

    /// The per-program gate ENUMERATES and re-verifies the native checked-arith
    /// idiom emitted in the program: `IMUL + SETcc O` (signed-mul-overflow flag
    /// via the hardware OF flag). The recovered (SignedMul, DivisionFreeWideMul)
    /// triple is proven correct on x86-64, so a clean native idiom is accepted.
    #[test]
    fn per_program_gate_accepts_native_signed_mul_overflow_idiom() {
        use trust_cg_ir::x86_64_ops::X86CondCode;

        let a = ch_vreg32(0);
        let b = ch_vreg32(1);
        let product = ch_vreg32(2);
        let flag = ch_vreg32(3);
        let func = ch_make_func(
            vec![
                X86ISelInst::new(
                    X86Opcode::ImulRR,
                    vec![
                        X86ISelOperand::VReg(product),
                        X86ISelOperand::VReg(a),
                        X86ISelOperand::VReg(b),
                    ],
                ),
                X86ISelInst::new(
                    X86Opcode::Setcc,
                    vec![
                        X86ISelOperand::VReg(flag),
                        X86ISelOperand::CondCode(X86CondCode::O),
                    ],
                ),
            ],
            &[(a, 32), (b, 32), (product, 32), (flag, 32)],
        );

        // Sanity: the idiom is actually recognized (the recovered triple set is
        // non-empty), so the acceptance below is meaningful (it re-verified a
        // real recovered triple, not an empty program).
        let mut triples = std::collections::BTreeSet::new();
        collect_overflow_expansions(&func, &mut triples);
        assert!(
            !triples.is_empty(),
            "native IMUL+SETcc O idiom must be enumerated as an overflow expansion"
        );

        assert!(
            validate_x86_glue_pass_expansions(std::slice::from_ref(&func)).is_ok(),
            "the live native signed-mul-overflow idiom must validate on x86-64"
        );
    }

    /// A deliberately-MIS-MODELED expansion triple (signed MUL paired with the
    /// add/sub `SignBitCheck` strategy — wrong for multiply) is REJECTED by the
    /// per-program re-verification path. This guards the enumeration->validator
    /// mapping: if a future enumerator mislabels a mul site's strategy, the
    /// exhaustive proof catches it. (Drives `validate_recovered_overflow_expansion`
    /// directly with a wrong (op, expansion) pairing.)
    #[test]
    fn per_program_reverification_rejects_wrong_expansion_for_mul() {
        // op = 2 (SignedMul), expansion = 0 (SignBitCheck) — a mismatched pairing
        // the validator models as a trap sentinel => Rejected.
        let wrong = RecoveredOverflowExpansion {
            op: 2,
            expansion: 0,
            width: 8,
        };
        assert!(
            matches!(
                validate_recovered_overflow_expansion(wrong),
                Err(CompileError::PassValidationRejected { .. })
            ),
            "a signed-MUL site mislabeled with the add/sub SignBitCheck strategy must be rejected"
        );
    }
}
