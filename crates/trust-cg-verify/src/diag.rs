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
    /// Register-allocation / lowering pipeline validator: the codegen pipeline
    /// (ISel, regalloc, encoding) rejected a function (the #63 class). Source:
    /// `CompileError::Pipeline` / `CompileError::Adapter` /
    /// `CompileError::DialectPipeline`.
    Regalloc,
    /// Per-compile proof-certificate gate (#465): proofs were requested but are
    /// unsupported for the target/build, an emitted instruction had no verified
    /// certificate, or proof promotion was rejected. Source: the `Proofs*` /
    /// `CertifiedPass*` `CompileError` variants and the bridge cert re-check.
    Proof,
    /// Generic "unsupported MIR / failing closed" skip: a required function used a
    /// MIR shape the bridge cannot lower, so the compile fails closed rather than
    /// miscompiling (or emitting a wrong/missing symbol).
    MirUnsupported,
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
                "the codegen pipeline (ISel / register allocation / encoding) could not \
                 produce verified object code for a function"
            }
            DiagCode::Proof => {
                "a per-compile proof-certificate requirement was not met \
                 (unsupported target, missing/unverified certificate, or rejected promotion)"
            }
            DiagCode::MirUnsupported => {
                "a required function uses a MIR shape this backend cannot lower"
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

/// Is structured-JSON diagnostic emission enabled (env `TCG_DIAG_JSON=1`)?
///
/// When this returns `false` (the default), the diagnostics layer emits only the
/// `[CODE]`-prefixed human message exactly as before. When `true`, the bridge
/// additionally writes one [`emit_json`]-formatted object to stderr per
/// fail-closed event. This predicate gates *only* extra output; it never affects
/// any compile decision.
pub fn json_enabled() -> bool {
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

/// Emit the structured diagnostic JSON object to stderr, *iff* `TCG_DIAG_JSON=1`.
///
/// This is the one place the JSON side-channel is written. It is a no-op when the
/// env gate is unset, so default behavior is unchanged. It never affects codegen.
pub fn emit_json(code: DiagCode, function: &str, why: &str, fields: serde_json::Value) {
    if json_enabled() {
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
        ];
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
        // Every code string and gate string is unique.
        let mut codes: Vec<&str> = all.iter().map(|c| c.as_str()).collect();
        codes.sort_unstable();
        codes.dedup();
        assert_eq!(codes.len(), all.len(), "diagnostic codes must be unique");
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
}
