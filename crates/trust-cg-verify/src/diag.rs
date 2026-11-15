// trust-cg-verify/diag.rs - Stable diagnostic codes for fail-closed gates
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Stable, machine-readable diagnostic codes for every fail-closed gate in the
//! Trust Codegen pipeline (the **AI-usability** diagnostics layer).
//!
//! # What this is
//!
//! Each soundness/correctness gate that can *fail the compile closed* (rather
//! than ship possibly-wrong object code) is assigned a **stable diagnostic
//! code** here — a single, version-stable string such as `TCG-SSA-071` that a
//! compiler engineer or an AI tool can pin a runbook, a suppression, or a
//! repair heuristic to. This module is the *single source of truth* for that
//! code namespace: the bridge ([`rustc_codegen_trust_cg`]) and the codegen
//! crate consult [`DiagCode`] to prefix every fail-closed human message with
//! `[CODE]` and, under the `TCG_DIAG_JSON=1` env gate, to emit one structured
//! JSON object per fail-closed event.
//!
//! # What this is NOT
//!
//! This layer is **purely additive**. It changes **no** compile decision: the
//! gate predicates, the bytes of every emitted object, and which programs
//! compile vs. fail closed are *identical* with and without it. Only the error
//! *text* (now carrying a `[CODE]` prefix) and the *optional* JSON metadata are
//! new. Nothing here is ever consulted on a success path.
//!
//! # The codes
//!
//! A code is `TCG-<CATEGORY>-<NNN>`. The numeric suffix references the historical
//! issue / miscompile class the gate was built to catch (so e.g. the #71
//! loop-threading class is `…-071`), which keeps the code stable even as the
//! surrounding code is refactored. See [`DiagCode`] for the full table.

use std::fmt;

/// A stable diagnostic code for one fail-closed gate / violation category.
///
/// The string form (`DiagCode::as_str`) is the **stable identity** — it is what
/// appears in the `[CODE]` message prefix and the JSON `code` field, and it must
/// not change for a given failure category once shipped. Add new variants for
/// new gates rather than renumbering existing ones.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DiagCode {
    /// SSA / loop-completeness gate (`ssa_loop_complete`): a back-edge dropped or
    /// misthreaded a loop-carried value (the #71 class), an undefined/undominated
    /// value, or a malformed CFG. Source: [`crate::ssa_loop_complete::SsaViolation`].
    Ssa,
    /// Definite-initialization gate (`definite_init`): a stack cell is loaded
    /// through a pointer that definitely derives only from it, yet is never
    /// stored and never escapes — an uninitialized stack read (the #99 class).
    /// Source: [`crate::definite_init::InitViolation`].
    Init,
    /// Carrier-hygiene gate (`carrier_hygiene`): a wide-reading x86-64 consumer
    /// (`SAR`/`IDIV`, `SHR`/`DIV`) read its source across the full carrier
    /// without a proven sign/zero extension (the #51 / #66 class). Source:
    /// [`crate::carrier_hygiene::CarrierHygieneViolation`].
    Carrier,
    /// Per-pass translation validator (`pass_validators`): a glue-pass expansion
    /// the x86-64 pipeline relies on failed re-proof of equivalence (the #67
    /// overflow / checked-arith class). Source:
    /// `CompileError::PassValidationRejected`.
    PassValidator,
    /// P3c scalar-rvalue MIR→trust-ir refinement (`mir_semantics`): the trust-ir
    /// op the bridge chose for a scalar rvalue can disagree with the Rust-defined
    /// meaning (the #68 fneg-as-sub / wrong-cast class), Refuted or Inconclusive.
    Refine,
    /// Loop-carried block-arg threading VC (`trust_ir_interp` /
    /// `loop_backedge_symexec`): the emitted back-edge threading can disagree
    /// with the MIR loop dataflow (the #71 / euclid class), Refuted/Inconclusive.
    LoopThreading,
    /// Opcode coverage / proof-database gate (`coverage_gate`): an emittable
    /// backend opcode has no discharged proof covering it (the #68 class). Source:
    /// [`crate::coverage_gate::CoverageFinding`]. (Build/audit-time gate.)
    Coverage,
    /// Machine-code pipeline (the #63 class): instruction selection, frame
    /// lowering, the machine-IR optimizer, register allocation, encoding and
    /// relaxation, target-ISA admission, and the translation validators that
    /// check those steps (TV-3 dataflow integrity, post-regalloc re-checks, the
    /// ENC-5 decode check). Source: the ISel / frame / optimizer / regalloc /
    /// encoding variants of `PipelineError`, `LowerError` and
    /// `X86PipelineError`.
    ///
    /// It is NOT a catch-all and NOT the trust-ir lowering layer: the
    /// trust-ir→LIR adapter, dialect pipeline and inliner carry
    /// [`Self::IrLowering`]; object, exception-handling, debug-info, JIT,
    /// compute-dispatch and driver refusals carry their own codes below; proof
    /// gates carry [`Self::Proof`].
    Regalloc,
    /// Per-compile proof-certificate gate (#465): proofs were requested but are
    /// unsupported for the target/build, an emitted instruction had no verified
    /// certificate, proof promotion was rejected, a kernel-authorized guard
    /// elimination failed its independent re-check, or the certificate lane
    /// lost the whole-module LIR it must cover. Source: the `Proofs*` /
    /// `CertifiedPass*` / `ProofLaneLirIncomplete` `CompileError` variants, the
    /// verifier-backed `PipelineError` variants (`VerificationFailed`,
    /// `FsymCoverageGap`, `GuardKernelRecheckRejected` (AArch64) and
    /// `IsaGuardKernelRecheckRejected` (x86-64, RISC-V),
    /// `SampledVerifyUnavailable`), and the bridge cert re-check.
    Proof,
    /// Generic "unsupported MIR / failing closed" skip: a required function used a
    /// MIR shape the bridge cannot lower, so the compile fails closed rather than
    /// miscompiling (or emitting a wrong/missing symbol).
    ///
    /// Also the code of the bridge's `[TCG-LINK-UNDEF]` refusal (an emitted
    /// object references a symbol only this crate could define, and it did not).
    /// Both causes that refusal names are MIR→trust-ir bridge decisions: the
    /// bridge's drop verdict for a function whose body failed (the same
    /// condition the deferred verdict already files here as a failed required
    /// root), or the bridge's call lowering declaring a callee rustc never
    /// collected. The references come from the bridge's own trust-ir, before
    /// the object writer runs, so the object layer is not the producer.
    MirUnsupported,
    /// Object / link layer: the object writer (text, data and TLS sections,
    /// global data images, the symbol table and local symbol binding,
    /// relocations, fixups and their inventory, object-format support and
    /// field representability).
    ///
    /// Why a code of its own (trust-core architecture AD-8 names it): none of
    /// the codes above covers the object lane. Before AD-8 its refusals read as
    /// [`Self::Regalloc`] (the classifier's default arm) although no register
    /// allocator is involved. Like `MirUnsupported` it carries no historical
    /// issue number.
    Object,
    /// Exception-handling / unwind layer: EH structure validation, the EH
    /// sidecar (LSDA, personality, landing pads, call-site tables), unwind
    /// tables (`__eh_frame` CIE/FDE, compact unwind, Windows `.pdata`/`.xdata`)
    /// and EH in the in-process JIT.
    ///
    /// Why a code of its own (AD-8 names it): 80 of the 97 `TCG-REGALLOC-063`
    /// rows in the first valid Checkpoint A were EH-sidecar refusals filed by
    /// the default arm; no existing code describes this layer.
    Unwind,
    /// trust-ir lowering layer, above machine IR: the dialect pipeline, the
    /// trust-ir inliner's structural self-check, and the trust-ir→LIR adapter
    /// (for example an ambiguous lowered symbol name, or an entry-block
    /// parameter whose type disagrees with the signature). Source:
    /// `CompileError::{DialectPipeline, IrInline, Adapter}` and
    /// `PipelineError::IrLowering` (an adapter refusal raised in the pipeline).
    ///
    /// Why a code of its own: these were documented under
    /// [`Self::Regalloc`], but no instruction selector, register allocator or
    /// encoder runs before them, and [`Self::MirUnsupported`] names the
    /// MIR→trust-ir bridge, a different producer.
    IrLowering,
    /// In-process JIT layer: executable-memory publication, in-memory symbol
    /// resolution / fixups / veneers, block-profile instrumentation, the
    /// host target / feature-profile binding of executable bytes, and the JIT
    /// validation-mode opt-in. Source: `JitError` (except the variants that
    /// forward another layer) and `CompileError::{Jit*, HostJit*,
    /// Aarch64MachineCodeEvidence*, JitIdentityEncoding,
    /// JitUncertifiedBytesRequireOptIn}`.
    ///
    /// Why a code of its own: the JIT produces executable memory, not an
    /// object file, so [`Self::Object`] would misdescribe it, and none of the
    /// other codes names a publication layer. The rustc bridge never reaches
    /// it (AOT only); the code exists so the classifier has no default arm.
    Jit,
    /// Heterogeneous compute-dispatch layer: dispatch-plan property
    /// verification (CPU fallback, transfers, synchronization, ordering,
    /// profitability) and CoreML / Metal kernel emission. Source:
    /// `PipelineError::{DispatchVerificationFailed, CoreMLEmit, MetalEmit}`.
    ///
    /// Why a code of its own: a dispatch plan and an accelerator kernel are
    /// neither machine code for [`Self::Regalloc`] nor an object for
    /// [`Self::Object`], and dispatch verification issues no proof certificate
    /// ([`Self::Proof`]). Not reached from the rustc bridge.
    ComputeDispatch,
    /// Debug-information layer: source-variable location provenance and DWARF
    /// section construction. Source: `PipelineError::{DebugProvenance,
    /// DebugInfoInput, DwarfEmit}`.
    ///
    /// Why a code of its own: a variable-location range conflict is raised
    /// while a function is compiled, before any object is written, so neither
    /// [`Self::Object`] nor [`Self::Regalloc`] (which it was filed under)
    /// describes the producer.
    DebugInfo,
    /// Compile driver layer: the request refused before any code-producing
    /// layer ran (empty module, an API/target combination the entry point does
    /// not accept, PGO profile-generate on a target without instrumentation, an
    /// invalid execution resource budget, a worker pool that could not be
    /// built, trust-ir module file I/O and decoding) and the compile artifact
    /// cache (I/O, identity). Source: `CompileError::{EmptyModule,
    /// PrebuiltIrTargetUnsupported, ProfileGenerateTargetUnsupported,
    /// ResourceBudget, CompileArtifactCache, ProfileUseCacheIdentity,
    /// CompileArtifactCacheIdentityJson, RelocationModelUnsupported,
    /// Aarch64IsaProfileUnsupported}`, the `ResourceBudget` / `WorkerPool` /
    /// `ModuleIo` variants of `PipelineError`, `JitError` and
    /// `X86PipelineError`, and `PipelineError::{NoTmbcWireImage,
    /// TargetAbiUnresolved, AmbientLateLayoutControl}` (the module encoding,
    /// and the request's target and ambient-control policy).
    ///
    /// Why a code of its own, and only one: none of the codes above describes a
    /// refusal where no code-producing layer ran. The request checks and the
    /// artifact cache are both the driver around codegen, not producers of
    /// code, objects or proofs, so separate codes for them would not meet the
    /// bar of "a producing layer with no other honest code"; they share this one.
    Driver,
}

impl DiagCode {
    /// The stable string identity of this code (`TCG-SSA-071`, …).
    ///
    /// This is the value embedded in the `[CODE]` message prefix and the JSON
    /// `code` field. It is part of the stable public contract.
    pub const fn as_str(self) -> &'static str {
        match self {
            DiagCode::Ssa => "TCG-SSA-071",
            DiagCode::Init => "TCG-INIT-099",
            DiagCode::Carrier => "TCG-CARRIER-051",
            DiagCode::PassValidator => "TCG-PASSVAL-067",
            DiagCode::Refine => "TCG-REFINE-068",
            DiagCode::LoopThreading => "TCG-REFINE-071",
            DiagCode::Coverage => "TCG-COVERAGE-068",
            DiagCode::Regalloc => "TCG-REGALLOC-063",
            DiagCode::Proof => "TCG-PROOF-465",
            DiagCode::MirUnsupported => "TCG-MIR-UNSUPPORTED",
            DiagCode::Object => "TCG-OBJECT-EMIT",
            DiagCode::Unwind => "TCG-EH-UNWIND",
            DiagCode::IrLowering => "TCG-IR-LOWER",
            DiagCode::Jit => "TCG-JIT-EXEC",
            DiagCode::ComputeDispatch => "TCG-COMPUTE-DISPATCH",
            DiagCode::DebugInfo => "TCG-DEBUG-INFO",
            DiagCode::Driver => "TCG-COMPILE-DRIVER",
        }
    }

    /// The short gate identity (the `gate` field in the JSON object): the name of
    /// the checker / subsystem that produced the failure.
    pub const fn gate(self) -> &'static str {
        match self {
            DiagCode::Ssa => "ssa_loop_complete",
            DiagCode::Init => "definite_init",
            DiagCode::Carrier => "carrier_hygiene",
            DiagCode::PassValidator => "pass_validators",
            DiagCode::Refine => "mir_semantics::check_rvalue_lowering",
            DiagCode::LoopThreading => "trust_ir_interp::loop_threading_vc",
            DiagCode::Coverage => "coverage_gate",
            DiagCode::Regalloc => "codegen_pipeline",
            DiagCode::Proof => "proof_certificates",
            DiagCode::MirUnsupported => "mir_lowering",
            DiagCode::Object => "object_emission",
            DiagCode::Unwind => "eh_unwind",
            DiagCode::IrLowering => "trust_ir_lowering",
            DiagCode::Jit => "jit_executable",
            DiagCode::ComputeDispatch => "compute_dispatch",
            DiagCode::DebugInfo => "debug_info",
            DiagCode::Driver => "compile_driver",
        }
    }

    /// A one-line description of what this gate checks (the `what` JSON field).
    pub const fn what(self) -> &'static str {
        match self {
            DiagCode::Ssa => {
                "trust-ir SSA / loop-completeness invariant violated \
                 (a loop-carried value was dropped or misthreaded across a back-edge)"
            }
            DiagCode::Init => {
                "trust-ir definite-initialization invariant violated \
                 (a stack cell is read before it is ever written)"
            }
            DiagCode::Carrier => {
                "x86-64 carrier-hygiene invariant violated \
                 (a wide-reading consumer read a narrow value's dirty high carrier bits)"
            }
            DiagCode::PassValidator => {
                "a per-pass translation validator rejected an x86-64 glue-pass expansion"
            }
            DiagCode::Refine => {
                "a MIR→trust-ir scalar-rvalue refinement obligation did not refine \
                 (the chosen trust-ir op can disagree with the Rust-defined meaning)"
            }
            DiagCode::LoopThreading => {
                "a loop-carried block-argument threading verification condition did not refine \
                 (the emitted back-edge threading can disagree with the MIR loop dataflow)"
            }
            DiagCode::Coverage => {
                "an emittable backend opcode is not covered by a discharged lowering proof"
            }
            DiagCode::Regalloc => {
                "the machine-code pipeline (ISel / frame lowering / register allocation / \
                 encoding, or a validator of those steps) could not produce verified code \
                 for a function"
            }
            DiagCode::Proof => {
                "a per-compile proof-certificate requirement was not met \
                 (unsupported target, missing/unverified certificate, or rejected promotion)"
            }
            DiagCode::MirUnsupported => {
                "a required function uses a MIR shape this backend cannot lower"
            }
            DiagCode::Object => {
                "the object / link layer (object writer, sections, symbols and binding, \
                 relocations/fixups, object format, or link integrity of the emitted \
                 objects) could not produce a linkable object"
            }
            DiagCode::Unwind => {
                "the exception-handling / unwind layer (EH structure, LSDA / personality \
                 sidecar, or unwind tables) could not be emitted with its metadata intact"
            }
            DiagCode::IrLowering => {
                "trust-ir lowering (dialect pipeline, inliner self-check, or the \
                 trust-ir to LIR adapter) refused the module before machine code"
            }
            DiagCode::Jit => {
                "the in-process JIT layer could not publish or bind executable code \
                 for the host"
            }
            DiagCode::ComputeDispatch => {
                "the heterogeneous compute-dispatch layer (dispatch-plan verification or \
                 CoreML / Metal kernel emission) refused"
            }
            DiagCode::DebugInfo => {
                "the debug-information layer (variable-location provenance or DWARF \
                 sections) could not be built"
            }
            DiagCode::Driver => {
                "the compile driver refused the request (input, configuration, execution \
                 resources) or the compile artifact cache failed; no code was produced"
            }
        }
    }

    /// Render the `[CODE]` prefix (with a trailing space) for a human message.
    ///
    /// Callers prepend this to the *existing* fail-closed message; the only
    /// change to default (env-unset) output is this prefix.
    pub fn prefix(self) -> String {
        format!("[{}] ", self.as_str())
    }
}

impl fmt::Display for DiagCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Embedder-installed setting for structured-JSON diagnostic emission.
///
/// `None` until an embedding installs one. The rustc bridge installs it during
/// `CodegenBackend::init` from the TRACKED `-Ztrust-ir-cg-args=diag-json` knob,
/// because `TCG_DIAG_JSON` is an untracked codegen control that trustc refuses
/// outright.
static JSON_SETTING: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the structured-JSON setting for this process.
///
/// Returns true for a first or identical installation and false for a conflict.
/// A conflict never changes the installed value. Embedders must check this
/// result before claiming the requested policy was installed.
pub fn set_json_enabled(enabled: bool) -> bool {
    match JSON_SETTING.set(enabled) {
        Ok(()) => true,
        Err(requested) => JSON_SETTING.get() == Some(&requested),
    }
}

static SOLVE_TRACE_SETTING: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the solver-trace setting from a TRACKED compiler option, once.
///
/// Same contract as [`set_json_enabled`]: the embedder's value wins because it
/// is the one that arrived through a channel the artifact's identity records.
pub fn set_solve_trace_enabled(enabled: bool) -> bool {
    match SOLVE_TRACE_SETTING.set(enabled) {
        Ok(()) => true,
        Err(requested) => SOLVE_TRACE_SETTING.get() == Some(&requested),
    }
}

/// Is per-query solver tracing enabled?
///
/// Before this existed, every read was a bare `TCG_SOLVE_TRACE` environment
/// probe — and under trustc that variable is REFUSED before the backend loads
/// (`UNTRACKED_TRUST_CODEGEN_ENV_PREFIXES`), with a message telling the operator
/// to "use the corresponding tracked compiler option". There was none: the
/// instrument was unreachable from the compiler, and the refusal pointed at a
/// fix that did not exist. `-Ztrust-ir-cg-args=solve-trace` is that option.
///
/// The environment read stays as the fallback for standalone, non-rustc use of
/// this crate, exactly as [`json_enabled`] keeps its own. This gates output
/// only; it never affects a verdict.
pub fn solve_trace_enabled() -> bool {
    if let Some(enabled) = SOLVE_TRACE_SETTING.get() {
        return *enabled;
    }
    std::env::var_os("TCG_SOLVE_TRACE").is_some()
}

static BACKEDGE_TRACE_SETTING: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the back-edge-VC trace setting from a TRACKED compiler option, once.
pub fn set_backedge_trace_enabled(enabled: bool) -> bool {
    BACKEDGE_TRACE_SETTING.set(enabled).is_ok()
}

/// Is per-obligation back-edge threading tracing enabled?
///
/// Same defect, same fix as [`solve_trace_enabled`]: the read was a bare
/// `TCG_BACKEDGE_TRACE` probe, and under trustc that variable is REFUSED before
/// the backend loads, with a message telling the operator to use "the
/// corresponding tracked compiler option" — which did not exist. So the ONE
/// instrument that prints both sides of a failing edge-equality obligation was
/// unreachable from the compiler, and a `[TCG-SSA-071]` refusal could not be
/// diagnosed without editing the source. `-Ztrust-ir-cg-args=backedge-trace` is
/// that option.
///
/// This matters more than an ordinary trace: `edge_equality_holds_structurally`
/// is an EXACT tree comparison, so when it declines the only actionable question
/// is *which subterm differs* — and that is precisely what this prints.
///
/// The environment read stays as the fallback for standalone, non-rustc use of
/// this crate. Gates output only; never affects a verdict.
pub fn backedge_trace_enabled() -> bool {
    if let Some(enabled) = BACKEDGE_TRACE_SETTING.get() {
        return *enabled;
    }
    std::env::var_os("TCG_BACKEDGE_TRACE").is_some()
}

static X86_BODY_TRACE_SETTING: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the x86-64 body-lane trace setting from a TRACKED compiler option,
/// once. Same contract as [`set_json_enabled`].
pub fn set_x86_body_trace_enabled(enabled: bool) -> bool {
    match X86_BODY_TRACE_SETTING.set(enabled) {
        Ok(()) => true,
        Err(requested) => X86_BODY_TRACE_SETTING.get() == Some(&requested),
    }
}

/// Does the x86-64 source-bound body lane print one line per classified
/// function (the owner's refusal reason, or its bound rows and replay
/// verdict)? `-Ztrust-ir-cg-args=x86-body-trace` under the rustc bridge;
/// `TCG_X86_BODY_TRACE` as the standalone fallback, like
/// [`solve_trace_enabled`]. This gates output only; it never affects a
/// verdict.
pub fn x86_body_trace_enabled() -> bool {
    if let Some(enabled) = X86_BODY_TRACE_SETTING.get() {
        return *enabled;
    }
    std::env::var_os("TCG_X86_BODY_TRACE").is_some()
}

/// Does the AArch64 source-bound whole-body lane print one line per
/// classified function (the owner's refusal, or its covered rows and replay
/// verdict)? `TCG_A64_BODY_TRACE`. This gates output only; it never affects
/// a verdict.
pub fn a64_body_trace_enabled() -> bool {
    std::env::var_os("TCG_A64_BODY_TRACE").is_some()
}

static X86_BODY_DUMP_SETTING: std::sync::OnceLock<Option<std::path::PathBuf>> =
    std::sync::OnceLock::new();

/// Install the x86-64 body-lane query dump directory from a TRACKED compiler
/// option, once. Same contract as [`set_json_enabled`].
pub fn set_x86_body_dump_dir(dir: Option<std::path::PathBuf>) -> bool {
    match X86_BODY_DUMP_SETTING.set(dir) {
        Ok(()) => true,
        Err(requested) => X86_BODY_DUMP_SETTING.get() == Some(&requested),
    }
}

/// The directory the x86-64 source-bound body lane writes the replayed SMT2
/// query of every body theorem that does not replay Valid into, so a gap can
/// be reproduced outside the compiler (`-Ztrust-ir-cg-args=x86-body-dump=DIR`
/// under the rustc bridge; `TCG_X86_BODY_DUMP` as the standalone fallback).
/// An empty directory (the bare knob, or an empty variable) is no dump, never
/// the compiler's current directory. Diagnostic only: it never affects a
/// verdict.
pub fn x86_body_dump_dir() -> Option<std::path::PathBuf> {
    resolve_x86_body_dump_dir(
        X86_BODY_DUMP_SETTING.get(),
        trust_cg_process_env::var_os("TCG_X86_BODY_DUMP"),
    )
}

/// [`x86_body_dump_dir`] from an installed setting (authoritative when
/// present) and the environment fallback.
fn resolve_x86_body_dump_dir(
    setting: Option<&Option<std::path::PathBuf>>,
    env: Option<std::ffi::OsString>,
) -> Option<std::path::PathBuf> {
    let dir = match setting {
        Some(dir) => dir.clone(),
        None => env.map(std::path::PathBuf::from),
    };
    dir.filter(|dir| !dir.as_os_str().is_empty())
}

static SOURCE_BOUND_NO_NEGATIVE_MEMO_SETTING: std::sync::OnceLock<bool> =
    std::sync::OnceLock::new();

/// Install the source-bound negative-memo bypass from a TRACKED compiler
/// option, once. Same contract as [`set_json_enabled`].
pub fn set_source_bound_negative_memo_disabled(disabled: bool) -> bool {
    match SOURCE_BOUND_NO_NEGATIVE_MEMO_SETTING.set(disabled) {
        Ok(()) => true,
        Err(requested) => SOURCE_BOUND_NO_NEGATIVE_MEMO_SETTING.get() == Some(&requested),
    }
}

/// Is the source-bound negative memo (`crate::source_bound_negative_memo`)
/// bypassed, so every source-bound theorem AY did not certify is solved
/// again at every occurrence and nothing is read from or written to the
/// memo? `-Ztrust-ir-cg-args=source-bound-no-negative-memo` under the rustc
/// bridge (trustc refuses `TCG_*` variables); `TCG_SOURCE_BOUND_NO_NEGATIVE_MEMO`
/// (any value but `0`) as the standalone fallback. It never grants credit:
/// the memo only withholds it, so bypassing it can only cost time or let a
/// retry certify.
pub fn source_bound_negative_memo_disabled() -> bool {
    if let Some(disabled) = SOURCE_BOUND_NO_NEGATIVE_MEMO_SETTING.get() {
        return *disabled;
    }
    trust_cg_process_env::var_os("TCG_SOURCE_BOUND_NO_NEGATIVE_MEMO")
        .is_some_and(|value| value != std::ffi::OsStr::new("0"))
}

static MEMORY_EFFECT_REPLAY_SETTING: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the memory-effect replay diagnostic from a TRACKED compiler option,
/// once. Same contract as [`set_json_enabled`].
pub fn set_memory_effect_replay_enabled(enabled: bool) -> bool {
    match MEMORY_EFFECT_REPLAY_SETTING.set(enabled) {
        Ok(()) => true,
        Err(requested) => MEMORY_EFFECT_REPLAY_SETTING.get() == Some(&requested),
    }
}

/// Does the function verifier replay the parts of each uncredited AArch64
/// memory row's word-bound memory-effect decomposition live (AY, then Clean)
/// under a replaying policy (`crate::aarch64_memory_effect`)?
/// `-Ztrust-ir-cg-args=memory-effect-replay` under the rustc bridge;
/// `TCG_MEMORY_EFFECT_REPLAY` (any value but `0`) as the standalone fallback.
/// Default off: the decomposition is never proof credit, so the replay only
/// RECORDS how many parts have a Clean-checked certificate, and it costs a
/// solve per distinct word and process. It changes an uncredited row's reason
/// text; only a solver counterexample (a refutation) changes a verdict, to
/// `Failed`.
pub fn memory_effect_replay_enabled() -> bool {
    if let Some(enabled) = MEMORY_EFFECT_REPLAY_SETTING.get() {
        return *enabled;
    }
    crate::env_lock::var_os("TCG_MEMORY_EFFECT_REPLAY")
        .is_some_and(|value| value != std::ffi::OsStr::new("0"))
}

static OPCODE_INVENTORY_TRACE_SETTING: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the opcode-inventory census trace setting from a TRACKED compiler
/// option, once. Same contract as [`set_json_enabled`].
pub fn set_opcode_inventory_trace_enabled(enabled: bool) -> bool {
    match OPCODE_INVENTORY_TRACE_SETTING.set(enabled) {
        Ok(()) => true,
        Err(requested) => OPCODE_INVENTORY_TRACE_SETTING.get() == Some(&requested),
    }
}

/// Does the certificate builder print every function's opcode-inventory census
/// lines
/// ([`crate::function_verifier::EmittedOpcodeInventoryReport::census_lines`])?
/// `-Ztrust-ir-cg-args=opcode-inventory-trace` under the rustc bridge;
/// `TCG_TRACE_OPCODE_INVENTORY` as the standalone fallback, like
/// [`solve_trace_enabled`]. This gates output only; it never affects a
/// verdict.
pub fn opcode_inventory_trace_enabled() -> bool {
    if let Some(enabled) = OPCODE_INVENTORY_TRACE_SETTING.get() {
        return *enabled;
    }
    std::env::var_os("TCG_TRACE_OPCODE_INVENTORY")
        .is_some_and(|value| value != std::ffi::OsStr::new("0"))
}

static EH_OBLIGATION_TRACE_SETTING: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the exception-table obligation trace setting from a TRACKED
/// compiler option, once. Same contract as [`set_json_enabled`].
pub fn set_eh_obligation_trace_enabled(enabled: bool) -> bool {
    match EH_OBLIGATION_TRACE_SETTING.set(enabled) {
        Ok(()) => true,
        Err(requested) => EH_OBLIGATION_TRACE_SETTING.get() == Some(&requested),
    }
}

/// Does the AArch64 Darwin emission gate print the exception-table
/// obligation report ([`crate::eh_obligations::EhObligationReport::summary`])
/// of every object or JIT image it decides? `-Ztrust-ir-cg-args=
/// eh-obligation-trace` under the rustc bridge; `TCG_TRACE_EH_OBLIGATIONS` as
/// the standalone fallback, like [`opcode_inventory_trace_enabled`]. This
/// gates output only; it never affects a decision.
pub fn eh_obligation_trace_enabled() -> bool {
    if let Some(enabled) = EH_OBLIGATION_TRACE_SETTING.get() {
        return *enabled;
    }
    std::env::var_os("TCG_TRACE_EH_OBLIGATIONS")
        .is_some_and(|value| value != std::ffi::OsStr::new("0"))
}

/// Is structured-JSON diagnostic emission enabled?
///
/// An embedder-installed setting (see [`set_json_enabled`]) is authoritative:
/// it is the one that arrived through a tracked channel. The `TCG_DIAG_JSON=1`
/// environment read remains ONLY as the fallback for a standalone, non-rustc
/// use of this crate, where there is no compiler option to carry it and no
/// artifact whose identity the variable could falsify.
///
/// When this returns `false` (the default), the diagnostics layer emits only the
/// `[CODE]`-prefixed human message exactly as before. When `true`, the bridge
/// additionally writes one [`emit_json`]-formatted object to stderr per
/// fail-closed event. This predicate gates *only* extra output; it never affects
/// any compile decision.
pub fn json_enabled() -> bool {
    if let Some(enabled) = JSON_SETTING.get() {
        return *enabled;
    }
    matches!(std::env::var("TCG_DIAG_JSON").as_deref(), Ok("1"))
}

/// Build the structured diagnostic JSON object for a fail-closed event.
///
/// The object is `{code, gate, function, what, why, fields}` where:
/// * `code` / `gate` / `what` come from [`DiagCode`],
/// * `function` is the symbol whose compile failed closed,
/// * `why` is the gate's own descriptive reason (the human message body),
/// * `fields` is the typed violation data as JSON (already-serialized by the
///   caller via `serde`; pass [`serde_json::Value::Null`] when a gate carries no
///   structured fields).
///
/// Returns the compact single-line JSON string. The caller decides whether to
/// emit it (see [`json_enabled`]). This function performs no I/O and has no
/// effect on codegen.
pub fn render_json(code: DiagCode, function: &str, why: &str, fields: serde_json::Value) -> String {
    let obj = serde_json::json!({
        "code": code.as_str(),
        "gate": code.gate(),
        "function": function,
        "what": code.what(),
        "why": why,
        "fields": fields,
    });
    // `to_string` on a serde_json::Value cannot fail; it is infallible for any
    // Value we construct here.
    obj.to_string()
}

thread_local! {
    /// How many [`mute_json`] guards are alive on THIS thread.
    static JSON_MUTE_DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// A live [`mute_json`] scope. Emission resumes on its thread when the last
/// guard drops — also when it is dropped by unwinding. Not `Send`: it must drop
/// on the thread whose emission it muted.
#[must_use = "structured-JSON emission is muted only while the guard is alive"]
pub struct JsonMuteGuard {
    _not_send: std::marker::PhantomData<*const ()>,
}

impl Drop for JsonMuteGuard {
    fn drop(&mut self) {
        JSON_MUTE_DEPTH.with(|depth| depth.set(depth.get() - 1));
    }
}

/// Mute structured-JSON emission on the CURRENT thread until the returned guard
/// drops (guards nest).
///
/// For an embedder that runs a gate SPECULATIVELY: the rustc bridge's SSA-071
/// cell retry re-lowers a refused body and re-runs every gate on the new
/// trust-ir. An attempt it does not admit is discarded, and the refusal it
/// reports is the FIRST attempt's, emitted once; a discarded attempt's own
/// fail-closed events must not reach the JSON stream, or one refused function
/// would report several events, for failures that are not the reported one.
/// This gates output only — never a verdict, never the returned message — and
/// only on this thread.
pub fn mute_json() -> JsonMuteGuard {
    JSON_MUTE_DEPTH.with(|depth| depth.set(depth.get() + 1));
    JsonMuteGuard {
        _not_send: std::marker::PhantomData,
    }
}

/// Is structured-JSON emission muted on this thread (a [`mute_json`] guard is
/// alive)?
pub fn json_muted() -> bool {
    JSON_MUTE_DEPTH.with(|depth| depth.get() > 0)
}

/// Emit the structured diagnostic JSON object to stderr, *iff* `TCG_DIAG_JSON=1`
/// and no [`mute_json`] guard is alive on this thread.
///
/// This is the one place the JSON side-channel is written. It is a no-op when the
/// env gate is unset, so default behavior is unchanged. It never affects codegen.
pub fn emit_json(code: DiagCode, function: &str, why: &str, fields: serde_json::Value) {
    if json_enabled() && !json_muted() {
        eprintln!("{}", render_json(code, function, why, fields));
    }
}

// ---------------------------------------------------------------------------
// Typed gate helpers
// ---------------------------------------------------------------------------
//
// One helper per per-compile fail-closed gate. Each helper:
//   1. (when `TCG_DIAG_JSON=1`) emits one structured JSON object to stderr whose
//      `fields` are the gate's *typed* violation data, via `serde`; and
//   2. returns the `[CODE]`-prefixed human message (the only change to default
//      output).
//
// They are the single integration surface the bridge calls — the bridge never
// touches `serde_json` itself, so the diagnostic schema stays defined here.
// `serde_json::to_value` on these `Serialize` types is infallible for the value
// shapes they produce; `unwrap_or(Null)` is a belt-and-braces fallback that can
// never fire and keeps the helpers panic-free on a fail-closed path.

/// SSA / loop-completeness gate (`DiagCode::Ssa`).
///
/// `why` is the existing fail-closed message body (e.g. the first violation's
/// `.message()`); `violations` are the typed findings emitted as JSON `fields`.
pub fn ssa_message(
    function: &str,
    why: &str,
    violations: &[crate::ssa_loop_complete::SsaViolation],
) -> String {
    let fields = serde_json::json!({ "violations": violations });
    emit_json(DiagCode::Ssa, function, why, fields);
    format!("{}{why}", DiagCode::Ssa.prefix())
}

/// Definite-initialization gate (`DiagCode::Init`).
pub fn init_message(
    function: &str,
    why: &str,
    violations: &[crate::definite_init::InitViolation],
) -> String {
    let fields = serde_json::json!({ "violations": violations });
    emit_json(DiagCode::Init, function, why, fields);
    format!("{}{why}", DiagCode::Init.prefix())
}

/// MIR→trust-ir scalar-rvalue refinement gate (`DiagCode::Refine`).
///
/// `obligation` is the obligation name; `verdict` is `"REFUTED"` /
/// `"INCONCLUSIVE"`; `detail` is the counterexample / reason.
pub fn refine_message(
    function: &str,
    why: &str,
    obligation: &str,
    verdict: &str,
    detail: &str,
) -> String {
    let fields = serde_json::json!({
        "obligation": obligation,
        "verdict": verdict,
        "detail": detail,
    });
    emit_json(DiagCode::Refine, function, why, fields);
    format!("{}{why}", DiagCode::Refine.prefix())
}

/// Loop-carried block-arg threading VC gate (`DiagCode::LoopThreading`).
pub fn loop_threading_message(function: &str, why: &str, detail: &str) -> String {
    let fields = serde_json::json!({ "detail": detail });
    emit_json(DiagCode::LoopThreading, function, why, fields);
    format!("{}{why}", DiagCode::LoopThreading.prefix())
}

/// Generic gate helper: emit JSON with caller-supplied `fields` and return the
/// `[CODE]`-prefixed message. Used by the bridge for the codegen `CompileError`
/// categories (carrier-hygiene, pass-validator, regalloc/pipeline, proofs) and
/// the unsupported-MIR site, where `fields` is built from the typed error.
pub fn gate_message(
    code: DiagCode,
    function: &str,
    why: &str,
    fields: serde_json::Value,
) -> String {
    emit_json(code, function, why, fields);
    format!("{}{why}", code.prefix())
}

/// Generic gate helper accepting string-keyed typed `fields` as `(key, value)`
/// pairs, so a caller without a `serde_json` dependency (the bridge) can still
/// emit a structured `fields` object built from a typed error's components.
/// Emits JSON under `TCG_DIAG_JSON=1` and returns the `[CODE]`-prefixed message.
pub fn gate_message_kv(
    code: DiagCode,
    function: &str,
    why: &str,
    fields: &[(&str, &str)],
) -> String {
    let mut map = serde_json::Map::with_capacity(fields.len());
    for (k, v) in fields {
        map.insert((*k).to_owned(), serde_json::Value::String((*v).to_owned()));
    }
    emit_json(code, function, why, serde_json::Value::Object(map));
    format!("{}{why}", code.prefix())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn opcode_inventory_policy_isolated() {
        const CHILD: &str = "CG_OPCODE_INVENTORY_POLICY";
        let Ok(case) = std::env::var(CHILD) else {
            let mut failures = Vec::new();
            for case in [
                "default",
                "zero",
                "one",
                "empty",
                "installed_on",
                "installed_off",
            ] {
                let mut cmd = std::process::Command::new(std::env::current_exe().unwrap());
                cmd.args([
                    "--exact",
                    "diag::tests::opcode_inventory_policy_isolated",
                    "--nocapture",
                    "--test-threads=1",
                ]);
                cmd.env(CHILD, case)
                    .env_remove("TCG_TRACE_OPCODE_INVENTORY");
                if case != "default" {
                    cmd.env(
                        "TCG_TRACE_OPCODE_INVENTORY",
                        if matches!(case, "zero" | "installed_on") {
                            "0"
                        } else if case == "empty" {
                            ""
                        } else {
                            "1"
                        },
                    );
                }
                let output = cmd.output().unwrap();
                let stdout = String::from_utf8_lossy(&output.stdout);
                println!(
                    "case {case}:\n{stdout}{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                if !output.status.success() || !stdout.contains("running 1 test") {
                    failures.push(case);
                }
            }
            assert!(failures.is_empty(), "failed cases: {failures:?}");
            return;
        };
        if case.starts_with("installed_") {
            let enabled = case == "installed_on";
            assert!(set_opcode_inventory_trace_enabled(enabled));
            assert!(set_opcode_inventory_trace_enabled(enabled));
            assert!(!set_opcode_inventory_trace_enabled(!enabled));
        }
        assert_eq!(
            opcode_inventory_trace_enabled(),
            matches!(case.as_str(), "one" | "empty" | "installed_on")
        );
    }

    #[test]
    fn codes_are_stable_and_unique() {
        let all = [
            DiagCode::Ssa,
            DiagCode::Init,
            DiagCode::Carrier,
            DiagCode::PassValidator,
            DiagCode::Refine,
            DiagCode::LoopThreading,
            DiagCode::Coverage,
            DiagCode::Regalloc,
            DiagCode::Proof,
            DiagCode::MirUnsupported,
            DiagCode::Object,
            DiagCode::Unwind,
            DiagCode::IrLowering,
            DiagCode::Jit,
            DiagCode::ComputeDispatch,
            DiagCode::DebugInfo,
            DiagCode::Driver,
        ];
        // Completeness: a new `DiagCode` variant must be added to `all` above.
        // This match has no wildcard, so the variant fails to compile here
        // until someone lists it (and then the length check below holds).
        let listed = |code: DiagCode| -> usize {
            match code {
                DiagCode::Ssa
                | DiagCode::Init
                | DiagCode::Carrier
                | DiagCode::PassValidator
                | DiagCode::Refine
                | DiagCode::LoopThreading
                | DiagCode::Coverage
                | DiagCode::Regalloc
                | DiagCode::Proof
                | DiagCode::MirUnsupported
                | DiagCode::Object
                | DiagCode::Unwind
                | DiagCode::IrLowering
                | DiagCode::Jit
                | DiagCode::ComputeDispatch
                | DiagCode::DebugInfo
                | DiagCode::Driver => 17,
            }
        };
        assert_eq!(all.len(), listed(DiagCode::Ssa));
        // Stable, exact strings (pinning the public contract).
        assert_eq!(DiagCode::Ssa.as_str(), "TCG-SSA-071");
        assert_eq!(DiagCode::Init.as_str(), "TCG-INIT-099");
        assert_eq!(DiagCode::Carrier.as_str(), "TCG-CARRIER-051");
        assert_eq!(DiagCode::PassValidator.as_str(), "TCG-PASSVAL-067");
        assert_eq!(DiagCode::Refine.as_str(), "TCG-REFINE-068");
        assert_eq!(DiagCode::LoopThreading.as_str(), "TCG-REFINE-071");
        assert_eq!(DiagCode::Coverage.as_str(), "TCG-COVERAGE-068");
        assert_eq!(DiagCode::Regalloc.as_str(), "TCG-REGALLOC-063");
        assert_eq!(DiagCode::Proof.as_str(), "TCG-PROOF-465");
        assert_eq!(DiagCode::MirUnsupported.as_str(), "TCG-MIR-UNSUPPORTED");
        assert_eq!(DiagCode::Object.as_str(), "TCG-OBJECT-EMIT");
        assert_eq!(DiagCode::Unwind.as_str(), "TCG-EH-UNWIND");
        assert_eq!(DiagCode::IrLowering.as_str(), "TCG-IR-LOWER");
        assert_eq!(DiagCode::Jit.as_str(), "TCG-JIT-EXEC");
        assert_eq!(DiagCode::ComputeDispatch.as_str(), "TCG-COMPUTE-DISPATCH");
        assert_eq!(DiagCode::DebugInfo.as_str(), "TCG-DEBUG-INFO");
        assert_eq!(DiagCode::Driver.as_str(), "TCG-COMPILE-DRIVER");
        // Every code string and gate string is unique.
        let mut codes: Vec<&str> = all.iter().map(|c| c.as_str()).collect();
        codes.sort_unstable();
        codes.dedup();
        assert_eq!(codes.len(), all.len(), "diagnostic codes must be unique");
        // A gate names the layer that produced the failure, so two codes never
        // share one: a shared gate would be a default arm by another name.
        let mut gates: Vec<&str> = all.iter().map(|c| c.gate()).collect();
        gates.sort_unstable();
        gates.dedup();
        assert_eq!(gates.len(), all.len(), "diagnostic gates must be unique");
        // Each code starts with the TCG- namespace.
        for c in all {
            assert!(c.as_str().starts_with("TCG-"));
            assert!(!c.gate().is_empty());
            assert!(!c.what().is_empty());
        }
    }

    #[test]
    fn prefix_wraps_code() {
        assert_eq!(DiagCode::Ssa.prefix(), "[TCG-SSA-071] ");
    }

    #[test]
    fn render_json_has_all_keys() {
        let s = render_json(
            DiagCode::Init,
            "_ZN4main",
            "uninitialized stack cell read",
            serde_json::json!({ "cell": "v3", "load_ptr": "v7" }),
        );
        let v: serde_json::Value = serde_json::from_str(&s).unwrap();
        assert_eq!(v["code"], "TCG-INIT-099");
        assert_eq!(v["gate"], "definite_init");
        assert_eq!(v["function"], "_ZN4main");
        assert_eq!(v["why"], "uninitialized stack cell read");
        assert!(
            v["what"]
                .as_str()
                .unwrap()
                .contains("definite-initialization")
        );
        assert_eq!(v["fields"]["cell"], "v3");
    }

    #[test]
    fn json_mute_is_scoped_nested_per_thread_and_unwind_safe() {
        assert!(!json_muted());
        {
            let _outer = mute_json();
            assert!(json_muted());
            {
                let _inner = mute_json();
                assert!(json_muted());
            }
            assert!(json_muted(), "an inner guard must not unmute");
            let elsewhere = std::thread::spawn(json_muted).join().unwrap();
            assert!(!elsewhere, "muting is per thread");
        }
        assert!(!json_muted());
        let unwound = std::panic::catch_unwind(|| {
            let _guard = mute_json();
            panic!("unwinding through a live mute guard");
        });
        assert!(unwound.is_err());
        assert!(!json_muted(), "a guard dropped by unwinding must unmute");
    }

    /// The bare `x86-body-dump` knob (stored as "") and an empty
    /// `TCG_X86_BODY_DUMP` are no dump: an empty path would write every
    /// query into the compiler's current directory.
    #[test]
    fn an_empty_x86_body_dump_directory_is_no_dump() {
        use std::path::PathBuf;
        let empty = Some(PathBuf::new());
        let dir = Some(PathBuf::from("/tmp/dump"));
        assert_eq!(resolve_x86_body_dump_dir(Some(&empty), None), None);
        assert_eq!(resolve_x86_body_dump_dir(None, Some("".into())), None);
        // An installed setting stays authoritative over the environment.
        assert_eq!(
            resolve_x86_body_dump_dir(Some(&empty), Some("/x".into())),
            None
        );
        assert_eq!(
            resolve_x86_body_dump_dir(Some(&None), Some("/x".into())),
            None
        );
        assert_eq!(resolve_x86_body_dump_dir(Some(&dir), None), dir);
        assert_eq!(
            resolve_x86_body_dump_dir(None, Some("/tmp/dump".into())),
            Some(PathBuf::from("/tmp/dump"))
        );
    }
}
