// trust-cg-verify/coverage_gate.rs — P1.1 emittable-opcode evidence inventory
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// CONTEXT: a session found ~17 miscompiles, all OUTSIDE the SMT-verified
// per-instruction lowering core. One concrete failure mode (#68-fneg) was an
// opcode the lowerer could EMIT (`select_fneg` -> a sign-flip sequence) for
// which there was NO proof obligation at all: the per-instruction verifier
// walked the function, found no proof mapping, recorded `Unverified`, and the
// build still passed. Coverage was measured per-function on whatever code the
// fuzzer happened to generate; an opcode never exercised by a test was never
// even noticed as a gap.
//
// This module turns that around: it enumerates the ENTIRE emittable opcode set
// of each backend (driven from the real `AArch64Opcode` / `X86Opcode` enums via
// an exhaustiveness-forced classifier `match`), and cross-references each
// emittable opcode against the `ProofDatabase` through the SAME evidence-query
// mappings the function verifiers use (`FunctionVerifier::opcode_to_proof_query`
// for AArch64, `X86FunctionVerifier::opcode_to_proof_query` for x86-64). An
// emittable value/effect opcode that has no matching, accepted obligation stays
// RED in the inventory. Only encoder-rejected / never-selected opcodes and
// non-value structural/control forms covered by a different gate may be excluded
// through the explicit, logged exception list.
//
// The exhaustiveness property is load-bearing: `classify_aarch64` /
// `classify_x86` are total `match` expressions with NO wildcard arm. Adding a
// new opcode variant to either enum will not compile until it is classified
// here — which forces a human to decide "is this emittable-and-needs-a-proof,
// or fail-closed?" exactly when the opcode is introduced, not after it ships an
// unproven lowering. That is the structural fix for the #68-fneg class of bug.
//
// Reference: crates/trust-cg-verify/src/function_verifier.rs
//            crates/trust-cg-verify/src/x86_64_function_verifier.rs
//            crates/trust-cg-verify/src/proof_database.rs
//            crates/trust-cg-ir/src/inst.rs       (AArch64Opcode, is_pseudo)
//            crates/trust-cg-ir/src/x86_64_ops.rs (X86Opcode, is_pseudo)

//! Emittable-opcode obligation/evidence inventory.
//!
//! [`CoverageGate`] inventories one question for a whole backend: *which emitted
//! value/effect opcodes have accepted, explicitly characterized evidence
//! obligations, and which remain named RED debt?* It is the build-time,
//! opcode-complete complement to the per-function
//! [`crate::function_verifier`] walk, which only ever sees the opcodes a given
//! test happens to produce.
//!
//! A green row is evidence that the configured obligation was accepted. It is
//! not, by itself, an end-to-end compiler-correctness proof. In particular, the
//! default `Statistical(N)` strength is deterministic regression sampling, not a
//! formal proof. Formal/solver-backed strength is reported separately.
//!
//! # Example
//!
//! ```rust,no_run
//! use trust_cg_verify::coverage_gate::{CoverageGate, GateArch};
//!
//! let report = CoverageGate::new().audit(GateArch::AArch64);
//! println!("{}", report.audit_log());
//! ```

use trust_cg_ir::{AArch64Opcode, RiscVOpcode, WasmOpcode, X86Opcode};

use crate::function_verifier::{FunctionVerifier, reconstruction_discharges_valid};
use crate::lowering_proof::{VerificationConfig, verify_by_evaluation_with_config};
use crate::proof_database::{ProofCategory, ProofDatabase};
use crate::riscv_function_verifier::{
    RiscVFunctionVerifier, reconstruction_discharges_valid as riscv_reconstruction_discharges_valid,
};
use crate::verify::{VerificationResult, VerificationStrength};
use crate::wasm_function_verifier::reconstruction_discharges_valid as wasm_reconstruction_discharges_valid;
use crate::x86_64_function_verifier::{
    X86FunctionVerifier, reconstruction_discharges_valid as x86_reconstruction_discharges_valid,
};

// ---------------------------------------------------------------------------
// Opcode classification
// ---------------------------------------------------------------------------

/// How an opcode relates to the obligation/evidence inventory.
///
/// Every opcode of every backend enum is mapped to exactly one of these by an
/// exhaustive (wildcard-free) `match`, so the classification can never silently
/// fall through for a newly added opcode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpcodeClass {
    /// The lowerer can emit this value/effect opcode and it MUST have an
    /// accepted evidence obligation. A missing/failed obligation is a RED row.
    EmittableNeedsProof,

    /// Pseudo-instruction with no hardware semantics (Phi, Nop, Copy, …) or a
    /// trap pseudo. These have no per-instruction equivalence proof obligation;
    /// they are skipped by the function verifiers and skipped here too.
    PseudoOrTrap,

    /// Explicitly excluded from this value/effect denominator. This bucket is
    /// limited to either (a) an opcode rejected by the encoder / never selected
    /// by lowering, or (b) a non-value structural, control-flow, ABI, or
    /// relocation form whose obligation belongs to another named gate. Despite
    /// the historical variant name, case (b) is not "fail-closed"; the reason
    /// must say `covered elsewhere` and name that evidence boundary.
    ///
    /// Emitted value/effect proof debt must never use this variant: it belongs
    /// in [`OpcodeClass::EmittableNeedsProof`] as an explicit RED finding.
    FailClosedAllowlisted {
        /// Why this opcode is allowed to ship without a proof. Logged in the
        /// report so the gate's exceptions are auditable.
        reason: &'static str,
    },
}

/// Case-matching convention for proof-name lookup, chosen to mirror exactly
/// what each backend's function verifier does (AArch64: case-insensitive;
/// x86-64: case-sensitive).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MatchCase {
    /// `name.contains(query)` — used for the x86-64 verifier parity.
    Sensitive,
    /// `name.to_lowercase().contains(query.to_lowercase())` — AArch64 parity.
    Insensitive,
}

/// Which backend to audit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GateArch {
    /// AArch64 backend (`AArch64Opcode`).
    AArch64,
    /// x86-64 backend (`X86Opcode`).
    X86_64,
    /// RISC-V (RV64) backend (`RiscVOpcode`).
    RiscV,
    /// WebAssembly backend (`WasmOpcode`) — the 4th backend, a STACK MACHINE.
    Wasm,
}

impl std::fmt::Display for GateArch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GateArch::AArch64 => f.write_str("aarch64"),
            GateArch::X86_64 => f.write_str("x86_64"),
            GateArch::RiscV => f.write_str("riscv"),
            GateArch::Wasm => f.write_str("wasm"),
        }
    }
}

// ---------------------------------------------------------------------------
// Per-opcode coverage finding
// ---------------------------------------------------------------------------

/// Why a given emittable opcode does not satisfy the gate.
///
/// `Serialize` is derived purely for the AI-usability diagnostics layer
/// (`crate::diag`): it lets a fail-closed event emit its typed fields as JSON.
/// The derive is additive — it changes no field and no gate decision.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub enum CoverageFinding {
    /// `EmittableNeedsProof`, but no proof query maps the opcode at all.
    /// This is the #68-fneg class: an opcode that can be emitted with no proof.
    NoProofMapping,
    /// A proof query maps the opcode, but no proof in the database matches it
    /// (a stale/typo'd query, or a registry that was never wired).
    NoMatchingProof {
        /// The query that found nothing.
        query: String,
    },
    /// A matching proof exists but its discharge did NOT come back `Valid`.
    ProofNotDischarged {
        /// Name of the proof that was matched.
        proof_name: String,
        /// Why discharge failed (`Invalid` counterexample or `Unknown` reason).
        detail: String,
    },
    /// A matching proof exists and evaluates `Valid`, but it is STRUCTURALLY
    /// DEGENERATE (`trust_ir_expr == aarch64_expr`, i.e. an `X == X`
    /// self-equality). Such a proof evaluates `Valid` trivially and proves
    /// NOTHING about the lowering, so it does NOT constitute coverage. This is
    /// the STRICT honesty fix (task #61): a degenerate proof NEVER counts as a
    /// discharged proof — purely structural, with NO allowlist exemption.
    /// Whether the proof is on the `KNOWN_DEGENERATE_PENDING_FIX` debt ledger, on
    /// the (former) `GENUINE_IDENTITY_ALLOWLIST`, or a brand-new unclassified
    /// one, it surfaces here. (Fail-closed: ANY degenerate match surfaces, period.)
    DegenerateProof {
        /// Name of the degenerate proof that was matched.
        proof_name: String,
    },
    /// An emitted value/effect opcode that belongs in the denominator but is
    /// HONESTLY DEFERRED and left RED because the current gate has no faithful,
    /// complete obligation for its semantics. The missing evidence may be an
    /// evaluator limitation, absent operand/immediate decoding, incomplete
    /// value/effect facets, or an unmodeled optimization/ordering boundary.
    /// Crediting it would be dishonest; excluding it would inflate the headline.
    /// This is expected, explicitly named publication debt, distinct from an
    /// unexpected [`CoverageFinding::NoProofMapping`] wiring regression.
    DeferredUnfaithfulModel {
        /// Why the op is deferred (the honest, auditable reason).
        reason: &'static str,
    },
}

impl std::fmt::Display for CoverageFinding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CoverageFinding::NoProofMapping => {
                f.write_str("emittable opcode has NO proof mapping (the #68-fneg class)")
            }
            CoverageFinding::NoMatchingProof { query } => {
                write!(f, "proof query {query:?} matched no proof in the database")
            }
            CoverageFinding::ProofNotDischarged { proof_name, detail } => {
                write!(f, "proof {proof_name:?} did not discharge: {detail}")
            }
            CoverageFinding::DegenerateProof { proof_name } => {
                write!(
                    f,
                    "proof {proof_name:?} is DEGENERATE (trust_ir_expr == aarch64_expr, an X==X \
                     self-equality) — it evaluates Valid trivially and proves NOTHING (it is a \
                     model-consistency check, not a lowering-correctness proof); it does NOT \
                     count as coverage under STRICT (no allowlist exemption). Give the opcode a \
                     faithful independent-encoder proof, or fail-closed-allowlist it with a true \
                     reason."
                )
            }
            CoverageFinding::DeferredUnfaithfulModel { reason } => {
                write!(
                    f,
                    "emitted value/effect opcode HONESTLY DEFERRED (left RED in the denominator, \
                     NOT allowlisted-out and NOT credited): {reason}. The current gate has no \
                     faithful, complete obligation that could refute the relevant wrong lowering \
                     or effect; crediting it would be dishonest and excluding it would inflate \
                     the headline."
                )
            }
        }
    }
}

/// One audited opcode row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpcodeAuditRow {
    /// The opcode under audit, rendered with its enum path (`AArch64::FnegRR`).
    pub opcode_display: String,
    /// How it was classified.
    pub class: OpcodeClass,
    /// `None` when the row is covered (or allowed); `Some` when it fails.
    pub finding: Option<CoverageFinding>,
    /// For covered emittable rows: the proof name + strength that covers it.
    /// For allowlisted rows: the allowlist reason. For pseudo: a short note.
    pub note: String,
}

impl OpcodeAuditRow {
    /// Returns true when this row blocks the gate.
    pub fn is_failure(&self) -> bool {
        self.finding.is_some()
    }
}

/// Full coverage report for one backend.
#[derive(Debug, Clone)]
pub struct CoverageReport {
    /// Which backend was audited.
    pub arch: GateArch,
    /// Every opcode of the backend enum, classified and (if emittable) checked.
    pub rows: Vec<OpcodeAuditRow>,
}

impl CoverageReport {
    /// Total opcodes audited.
    pub fn total(&self) -> usize {
        self.rows.len()
    }

    /// Number of emitted value/effect opcodes that need an accepted evidence
    /// obligation (the inventory denominator; not an end-to-end correctness
    /// denominator).
    pub fn emittable_count(&self) -> usize {
        self.rows
            .iter()
            .filter(|r| r.class == OpcodeClass::EmittableNeedsProof)
            .count()
    }

    /// Number of emitted value/effect opcodes with an accepted, matching
    /// obligation at its separately reported evidence strength.
    pub fn covered_count(&self) -> usize {
        self.rows
            .iter()
            .filter(|r| r.class == OpcodeClass::EmittableNeedsProof && r.finding.is_none())
            .count()
    }

    /// Number of opcodes explicitly excluded because they are fail-closed /
    /// never selected or are non-value forms covered by another named gate.
    pub fn allowlisted_count(&self) -> usize {
        self.rows
            .iter()
            .filter(|r| matches!(r.class, OpcodeClass::FailClosedAllowlisted { .. }))
            .count()
    }

    /// Rows that fail the gate.
    pub fn failures(&self) -> Vec<&OpcodeAuditRow> {
        self.rows.iter().filter(|r| r.is_failure()).collect()
    }

    /// True when no inventoried opcode is missing an accepted obligation.
    /// This does not mean the backend or compiler is formally proved correct.
    pub fn is_clean(&self) -> bool {
        self.failures().is_empty()
    }

    /// Accepted-obligation coverage of the emitted value/effect inventory
    /// (`covered / emittable`), in percent. This is not a correctness-proof
    /// percentage. Returns 100.0 for an empty (therefore vacuous) denominator.
    pub fn coverage_percent(&self) -> f64 {
        let denom = self.emittable_count();
        if denom == 0 {
            100.0
        } else {
            (self.covered_count() as f64 / denom as f64) * 100.0
        }
    }

    /// A multi-line human-readable description of every failing row, suitable
    /// for an assertion message in the gate test.
    pub fn failure_summary(&self) -> String {
        use std::fmt::Write as _;
        let failures = self.failures();
        if failures.is_empty() {
            return format!(
                "{}: no RED rows — {}/{} emitted value/effect opcodes have accepted obligations, \
                 {} explicitly excluded; this is evidence coverage, not an end-to-end proof",
                self.arch,
                self.covered_count(),
                self.emittable_count(),
                self.allowlisted_count()
            );
        }
        let mut out = format!(
            "{}: evidence inventory has {} RED emitted value/effect opcode(s):\n",
            self.arch,
            failures.len()
        );
        for row in failures {
            let finding = row
                .finding
                .as_ref()
                .expect("failure row has a finding by construction");
            let _ = writeln!(out, "  {} — {}", row.opcode_display, finding);
        }
        let _ = writeln!(
            out,
            "Only encoder-rejected / never-selected opcodes or non-value structural/control \
             forms covered by another named gate may be excluded. Emitted value/effect debt \
             must remain EmittableNeedsProof and RED."
        );
        out
    }

    /// A full audit log (every row), for `--nocapture` diagnostics and for
    /// keeping the allowlist visible/auditable in CI output.
    pub fn audit_log(&self) -> String {
        use std::fmt::Write as _;
        let mut out = format!(
            "Evidence audit: {} ({} opcodes; {}/{} emitted value/effect obligations accepted = \
             {:.1}%; {} explicitly excluded; ratio is NOT a correctness-proof percentage)\n",
            self.arch,
            self.total(),
            self.covered_count(),
            self.emittable_count(),
            self.coverage_percent(),
            self.allowlisted_count(),
        );
        for row in &self.rows {
            let tag = match (&row.class, &row.finding) {
                (OpcodeClass::EmittableNeedsProof, None) => "accepted",
                (OpcodeClass::EmittableNeedsProof, Some(_)) => "RED     ",
                (OpcodeClass::PseudoOrTrap, _) => "skip    ",
                (OpcodeClass::FailClosedAllowlisted { .. }, _) => "exclude ",
            };
            let _ = writeln!(out, "  [{tag}] {:32} {}", row.opcode_display, row.note);
        }
        out
    }
}

// ---------------------------------------------------------------------------
// The gate
// ---------------------------------------------------------------------------

/// Audits an entire backend's emittable opcode set against the proof database.
pub struct CoverageGate {
    db: ProofDatabase,
    config: VerificationConfig,
}

impl CoverageGate {
    /// Construct a gate with the default proof database and verification config.
    pub fn new() -> Self {
        Self {
            db: ProofDatabase::new(),
            config: VerificationConfig::default(),
        }
    }

    /// Construct a gate with a custom verification config (e.g. to require a
    /// larger sample count or, once P0 lands, to force the formal lane).
    pub fn with_config(config: VerificationConfig) -> Self {
        Self {
            db: ProofDatabase::new(),
            config,
        }
    }

    /// Audit a backend. Returns one [`OpcodeAuditRow`] per opcode in the
    /// backend's enum.
    pub fn audit(&self, arch: GateArch) -> CoverageReport {
        let rows = match arch {
            GateArch::AArch64 => ALL_AARCH64_OPCODES
                .iter()
                .map(|&op| self.audit_aarch64(op))
                .collect(),
            GateArch::X86_64 => ALL_X86_OPCODES
                .iter()
                .map(|&op| self.audit_x86(op))
                .collect(),
            GateArch::RiscV => ALL_RISCV_OPCODES
                .iter()
                .map(|&op| self.audit_riscv(op))
                .collect(),
            GateArch::Wasm => ALL_WASM_OPCODES
                .iter()
                .map(|&op| self.audit_wasm(op))
                .collect(),
        };
        CoverageReport { arch, rows }
    }

    // -- AArch64 ----------------------------------------------------------

    fn audit_aarch64(&self, opcode: AArch64Opcode) -> OpcodeAuditRow {
        let display = format!("AArch64::{opcode:?}");
        match classify_aarch64(opcode) {
            OpcodeClass::PseudoOrTrap => OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::PseudoOrTrap,
                finding: None,
                note: "pseudo/trap — no equivalence proof obligation".to_string(),
            },
            OpcodeClass::FailClosedAllowlisted { reason } => OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::FailClosedAllowlisted { reason },
                finding: None,
                note: format!("fail-closed allowlist: {reason}"),
            },
            OpcodeClass::EmittableNeedsProof => {
                // PHASE-2 OPERAND RECONSTRUCTION CREDIT (task #63 Step 4).
                //
                // If the opcode is RECONSTRUCTABLE (in `opcode_to_source_op`) and a
                // representative reconstructed obligation discharges `Valid`, credit
                // it COVERED here — the machine side was rebuilt from the REAL
                // opcode+operands, so this is GENUINE coverage (a wrong isel choice
                // would have refuted), not the degenerate X==X the static-DB path
                // would have matched. This routes BEFORE the DB-substring path so
                // the headline reflects reconstruction; an opcode that is NOT
                // reconstructable, or whose reconstruction does not discharge Valid,
                // falls through to the existing DB path unchanged (so nothing is
                // fake-covered). Mirrors `FunctionVerifier::try_reconstruct`'s
                // dual `is_reconstructed() && Valid` credit rule exactly.
                if reconstruction_discharges_valid(opcode, &self.config) {
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: None,
                        note: format!(
                            "RECONSTRUCTED from real {opcode:?} operands — \
                             representative obligation evaluates Valid [reconstruction] (default \
                             evaluator acceptance is regression evidence, NOT a formal proof)"
                        ),
                    };
                }
                // SOUNDNESS: width-polymorphic AArch64 opcodes (FABS/FSQRT/FDIV)
                // are emitted at BOTH F32 and F64 under one opcode. The gate has
                // only the opcode, so it requires BOTH widths be proven; both the
                // F32 and F64 value proofs live under FloatingPoint. The AArch64
                // verifier matches case-insensitively, so mirror that here.
                if let Some(queries) = aarch64_width_polymorphic_proofs(opcode) {
                    return self.check_all_queries(display, queries, MatchCase::Insensitive);
                }
                // Known emitted value/effect opcodes whose present model cannot
                // provide faithful opcode-level evidence remain explicit RED
                // rows. This runs before the legacy DB-substring path because
                // several old mappings resolve only to a degenerate X==X model
                // (notably scalar/vector memory and DUP/MOVI). A legacy mapping
                // must never turn known unfaithful debt green. Faithful
                // reconstruction and width-complete mappings still get first
                // chance above; removing a row from this table is therefore an
                // explicit, reviewable promotion.
                if let Some(reason) = aarch64_deferred_value_op_reason(opcode) {
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: Some(CoverageFinding::DeferredUnfaithfulModel { reason }),
                        note: format!("HONESTLY DEFERRED (RED in denominator): {reason}"),
                    };
                }
                // Reuse the SAME mapping the function verifier uses, so the gate
                // measures exactly the coverage the per-instruction walk would.
                let Some((query, category)) = FunctionVerifier::opcode_to_proof_query(opcode)
                else {
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: Some(CoverageFinding::NoProofMapping),
                        note: "no opcode_to_proof_query mapping".to_string(),
                    };
                };
                // The AArch64 verifier matches case-insensitively
                // (`name.to_lowercase().contains(query)`), so mirror that.
                self.check_query(display, query, category, MatchCase::Insensitive)
            }
        }
    }

    // -- x86-64 -----------------------------------------------------------

    fn audit_x86(&self, opcode: X86Opcode) -> OpcodeAuditRow {
        let display = format!("x86_64::{opcode:?}");
        match classify_x86(opcode) {
            OpcodeClass::PseudoOrTrap => OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::PseudoOrTrap,
                finding: None,
                note: "pseudo/trap — no equivalence proof obligation".to_string(),
            },
            OpcodeClass::FailClosedAllowlisted { reason } => OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::FailClosedAllowlisted { reason },
                finding: None,
                note: format!("fail-closed allowlist: {reason}"),
            },
            OpcodeClass::EmittableNeedsProof => {
                // Known emitted value/effect opcodes whose current gate binding
                // is incomplete stay explicit RED rows. This check deliberately
                // precedes reconstruction: in particular, a volatile access is
                // not covered merely because its byte-identical plain load/store
                // value model reconstructs. Promotion requires evidence for both
                // the memory value/effect and the volatile observation/ordering
                // boundary, followed by explicit removal from this debt table.
                if let Some(reason) = x86_deferred_value_op_reason(opcode) {
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: Some(CoverageFinding::DeferredUnfaithfulModel { reason }),
                        note: format!("HONESTLY DEFERRED (RED in denominator): {reason}"),
                    };
                }
                // PHASE-2 OPERAND RECONSTRUCTION CREDIT (task #66) — mirrors
                // `audit_aarch64` / `audit_riscv` exactly.
                //
                // If the opcode is RECONSTRUCTABLE (in the x86
                // `x86_opcode_to_source_op`) and a representative reconstructed
                // obligation discharges `Valid`, credit it COVERED here — the
                // machine side was rebuilt from the REAL opcode+operands, so this
                // is GENUINE coverage (a wrong isel choice would have refuted), not
                // the degenerate X==X the static-DB "x86_64: …" proof would have
                // matched. Routes BEFORE the width-polymorphic / DB-substring path
                // so the headline reflects reconstruction; an opcode that is NOT
                // reconstructable, or whose reconstruction does not discharge Valid,
                // falls through to the existing paths unchanged (nothing is
                // fake-covered). Same dual `is_reconstructed() && Valid` credit rule
                // as the function verifier's `try_reconstruct`. NOTE: the byte/word
                // MOVSX/MOVZX extends are reconstructable and credited HERE; the
                // 3-operand ImulRRI is NOT in the reconstructable set, so it still
                // falls through to its both-widths width-polymorphic gate below.
                if x86_reconstruction_discharges_valid(opcode, &self.config) {
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: None,
                        note: format!(
                            "RECONSTRUCTED from real {opcode:?} operands — \
                             representative obligation evaluates Valid [reconstruction] (default \
                             evaluator acceptance is regression evidence, NOT a formal proof)"
                        ),
                    };
                }
                // SOUNDNESS: width-polymorphic opcodes (3-operand IMUL, BT, MUL,
                // ROUNDSS/SD) are emitted at MULTIPLE widths/bits/modes under one
                // opcode. The gate has only the opcode, so it requires EVERY width
                // be proven; the byte/word MOVSX/MOVZX extends were already credited
                // via reconstruction above, so this path now backs the remaining
                // genuinely width/bit/mode-polymorphic opcodes.
                if let Some(queries) = x86_width_polymorphic_proofs(opcode) {
                    return self.check_all_queries(display, queries, MatchCase::Sensitive);
                }
                let Some(query) = X86FunctionVerifier::opcode_to_proof_query(opcode) else {
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: Some(CoverageFinding::NoProofMapping),
                        note: "no opcode_to_proof_query mapping".to_string(),
                    };
                };
                // All x86-64 lowering proofs live under a single category. The
                // x86 verifier matches case-sensitively
                // (`name.contains(query)`), so mirror that exactly.
                self.check_query(
                    display,
                    query,
                    ProofCategory::X8664Lowering,
                    MatchCase::Sensitive,
                )
            }
        }
    }

    // -- RISC-V -----------------------------------------------------------

    fn audit_riscv(&self, opcode: RiscVOpcode) -> OpcodeAuditRow {
        let display = format!("riscv::{opcode:?}");
        match classify_riscv(opcode) {
            OpcodeClass::PseudoOrTrap => OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::PseudoOrTrap,
                finding: None,
                note: "pseudo/trap — no equivalence proof obligation".to_string(),
            },
            OpcodeClass::FailClosedAllowlisted { reason } => OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::FailClosedAllowlisted { reason },
                finding: None,
                note: format!("fail-closed allowlist: {reason}"),
            },
            OpcodeClass::EmittableNeedsProof => {
                // PHASE-2 OPERAND RECONSTRUCTION CREDIT (task #63, RISC-V) —
                // mirrors `audit_aarch64` exactly.
                //
                // If the opcode is RECONSTRUCTABLE (in the RISC-V
                // `opcode_to_source_op`) and a representative reconstructed
                // obligation discharges `Valid`, credit it COVERED here — the
                // machine side was rebuilt from the REAL opcode+operands, so this
                // is GENUINE coverage (a wrong isel choice would have refuted), not
                // the degenerate X==X the static-DB "riscv: …" proof would have
                // matched. Routes BEFORE the DB-substring path so the headline
                // reflects reconstruction; an opcode that is NOT reconstructable,
                // or whose reconstruction does not discharge Valid, falls through
                // to the existing DB path unchanged (nothing is fake-covered).
                // Same dual `is_reconstructed() && Valid` credit rule as the
                // function verifier's `try_reconstruct`.
                if riscv_reconstruction_discharges_valid(opcode, &self.config) {
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: None,
                        note: format!(
                            "RECONSTRUCTED from real {opcode:?} operands — \
                             representative obligation evaluates Valid [reconstruction] (default \
                             evaluator acceptance is regression evidence, NOT a formal proof)"
                        ),
                    };
                }
                // Emitted constant/comparison-idiom components that are not
                // individually reconstructed must remain named denominator debt.
                // A whole-sequence proof does not bind the standalone opcode row
                // in the current function verifier.
                if let Some(reason) = riscv_deferred_value_op_reason(opcode) {
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: Some(CoverageFinding::DeferredUnfaithfulModel { reason }),
                        note: format!("HONESTLY DEFERRED (RED in denominator): {reason}"),
                    };
                }
                // Reuse the SAME mapping the function verifier uses, so the gate
                // measures exactly the coverage the per-instruction walk would.
                // RISC-V proof binding is purely opcode-level (no width/scale
                // polymorphism), so there is no width-polymorphic table here.
                let Some(query) = RiscVFunctionVerifier::opcode_to_proof_query(opcode) else {
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: Some(CoverageFinding::NoProofMapping),
                        note: "no opcode_to_proof_query mapping".to_string(),
                    };
                };
                // All RISC-V lowering proofs live under a single category. The
                // RISC-V verifier matches case-sensitively (`name.contains`), so
                // mirror that exactly.
                self.check_query(
                    display,
                    query,
                    ProofCategory::RiscVLowering,
                    MatchCase::Sensitive,
                )
            }
        }
    }

    // -- WebAssembly ------------------------------------------------------

    fn audit_wasm(&self, opcode: WasmOpcode) -> OpcodeAuditRow {
        let display = format!("wasm::{opcode:?}");
        match classify_wasm(opcode) {
            OpcodeClass::PseudoOrTrap => OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::PseudoOrTrap,
                finding: None,
                note: "pseudo/trap — no equivalence proof obligation".to_string(),
            },
            OpcodeClass::FailClosedAllowlisted { reason } => OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::FailClosedAllowlisted { reason },
                finding: None,
                note: format!("fail-closed allowlist: {reason}"),
            },
            OpcodeClass::EmittableNeedsProof => {
                // STACK-MACHINE OPERAND RECONSTRUCTION CREDIT (task #71) —
                // mirrors `audit_riscv` / `audit_aarch64` / `audit_x86` exactly.
                //
                // wasm has no register operands: the reconstructor models the
                // value-stack operands as fresh symbolic vars and rebuilds the
                // machine side by DECODING the REAL emitted opcode BYTE
                // (wasm_function_verifier::reconstruct_alu_obligation). A wrong
                // opcode byte (`i32.sub` for an intended add) decodes to a
                // different op ⇒ REFUTE; a swapped non-commutative wiring (sub /
                // shift / comparison) ⇒ REFUTE. So crediting COVERED here is
                // GENUINE, not the vacuous X==X the deleted static "X -> wasm X"
                // proofs would have matched. There is NO DB-substring fallback for
                // wasm scalar value ops — reconstruction is the SOLE credit path;
                // an opcode whose representative reconstruction does not discharge
                // Valid is reported MISSING (nothing is fake-covered).
                if wasm_reconstruction_discharges_valid(opcode, &self.config) {
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: None,
                        note: format!(
                            "RECONSTRUCTED from real {opcode:?} opcode byte over symbolic \
                             value-stack operands — representative obligation evaluates Valid \
                             [reconstruction] (default evaluator acceptance is regression evidence, \
                             NOT a formal proof)"
                        ),
                    };
                }
                // Reconstruction did NOT credit this op. If it is a known value-
                // bearing op we are HONESTLY DEFERRING (the native evaluator cannot
                // faithfully model it), surface it as a `DeferredUnfaithfulModel`
                // RED row IN the denominator with a true reason — NOT a fake green,
                // NOT allowlisted-out. This is the wasm analogue of the x86
                // DegenerateProof deferral; the gate test treats it as an
                // ACCEPTABLE RED (distinct from a `NoProofMapping` wiring gap).
                if let Some(reason) = wasm_deferred_value_op_reason(opcode) {
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: Some(CoverageFinding::DeferredUnfaithfulModel { reason }),
                        note: format!("HONESTLY DEFERRED (RED in denominator): {reason}"),
                    };
                }
                OpcodeAuditRow {
                    opcode_display: display,
                    class: OpcodeClass::EmittableNeedsProof,
                    finding: Some(CoverageFinding::NoProofMapping),
                    note: "wasm scalar value op did not reconstruct-discharge Valid — no \
                           static DB fallback exists (reconstruction is the sole credit path)"
                        .to_string(),
                }
            }
        }
    }

    // -- shared proof lookup + discharge ----------------------------------

    /// Find the proof matching `query` in `category` and discharge it. Mirrors
    /// the lookup in `FunctionVerifier::verify` / `X86FunctionVerifier::verify`,
    /// including each verifier's case-matching convention.
    fn check_query(
        &self,
        display: String,
        query: &str,
        category: ProofCategory,
        case: MatchCase,
    ) -> OpcodeAuditRow {
        match self.discharge_one(query, category, case) {
            Ok(note) => OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::EmittableNeedsProof,
                finding: None,
                note,
            },
            Err((finding, note)) => OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::EmittableNeedsProof,
                finding: Some(finding),
                note,
            },
        }
    }

    /// Require that EVERY listed `(category, query)` proof exists and discharges.
    ///
    /// SOUNDNESS: used for width-polymorphic opcodes — x86 byte/word MOVSX/MOVZX
    /// and 3-operand IMUL (emitted at BOTH i32 and i64 destination widths under
    /// one opcode), and AArch64 FABS/FSQRT/FDIV (emitted at BOTH F32 and F64).
    /// The coverage gate (which has only the opcode, not the instruction) cannot
    /// pick a width, so it demands EVERY width be proven — otherwise one width
    /// could ship silently unproven. The row fails on the FIRST missing/
    /// undischarged width and names it. `case` mirrors the owning verifier's
    /// matching convention (x86 sensitive, AArch64 insensitive).
    fn check_all_queries(
        &self,
        display: String,
        queries: &[WidthProof],
        case: MatchCase,
    ) -> OpcodeAuditRow {
        let mut notes = Vec::with_capacity(queries.len());
        for wp in queries {
            match self.discharge_one(wp.query, wp.category, case) {
                Ok(note) => notes.push(note),
                Err((finding, note)) => {
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: Some(finding),
                        note,
                    };
                }
            }
        }
        OpcodeAuditRow {
            opcode_display: display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: None,
            note: notes.join("; "),
        }
    }

    /// Find the single proof matching `query` in `category` and discharge it.
    /// On success returns a human-readable note; on failure returns the
    /// [`CoverageFinding`] plus a note. Mirrors the lookup + discharge in the
    /// function verifiers, including each verifier's case-matching convention.
    fn discharge_one(
        &self,
        query: &str,
        category: ProofCategory,
        case: MatchCase,
    ) -> Result<String, (CoverageFinding, String)> {
        let candidates = self.db.by_category(category);
        let proof = candidates.iter().find(|p| match case {
            MatchCase::Sensitive => p.obligation.name.contains(query),
            MatchCase::Insensitive => p
                .obligation
                .name
                .to_lowercase()
                .contains(&query.to_lowercase()),
        });

        match proof {
            None => Err((
                CoverageFinding::NoMatchingProof {
                    query: query.to_string(),
                },
                format!("no proof matching {query:?} in {category:?}"),
            )),
            Some(cp) => {
                // STRICT HONESTY GATE (task #61, STRICT decision): a STRUCTURALLY
                // DEGENERATE proof (`trust_ir_expr == aarch64_expr`, an X==X
                // self-equality) evaluates `Valid` trivially and proves NOTHING
                // about the lowering. It NEVER counts as coverage — purely
                // structural, with NO allowlist exemption. A degenerate proof is
                // rejected here whether it is on the KNOWN_DEGENERATE_PENDING_FIX
                // debt ledger, on the (former) GENUINE_IDENTITY_ALLOWLIST, or a
                // brand-new unclassified degenerate. The sole credit criterion is
                // `is_genuinely_proven()` (trust_ir_expr != aarch64_expr): a wrong
                // opcode/instruction on the machine side can only ever refute when
                // the two sides are STRUCTURALLY DISTINCT. X==X obligations remain
                // in the DB as model-consistency / documented debt but contribute
                // ZERO to coverage. Fail-closed by construction.
                if cp.obligation.is_degenerate() {
                    return Err((
                        CoverageFinding::DegenerateProof {
                            proof_name: cp.obligation.name.clone(),
                        },
                        format!(
                            "DEGENERATE (X==X, model-consistency only, not proven): {}",
                            cp.obligation.name
                        ),
                    ));
                }
                let strength =
                    VerificationStrength::for_obligation_with_config(&cp.obligation, &self.config);
                match verify_by_evaluation_with_config(&cp.obligation, &self.config) {
                    VerificationResult::Valid => Ok(match strength {
                        VerificationStrength::Statistical { .. } => format!(
                            "{} [{} — accepted regression evidence, NOT a formal proof]",
                            cp.obligation.name, strength
                        ),
                        _ => format!("{} [{}]", cp.obligation.name, strength),
                    }),
                    VerificationResult::Invalid { counterexample } => Err((
                        CoverageFinding::ProofNotDischarged {
                            proof_name: cp.obligation.name.clone(),
                            detail: counterexample,
                        },
                        cp.obligation.name.clone(),
                    )),
                    VerificationResult::Unknown { reason } => Err((
                        CoverageFinding::ProofNotDischarged {
                            proof_name: cp.obligation.name.clone(),
                            detail: format!("Unknown: {reason}"),
                        },
                        cp.obligation.name.clone(),
                    )),
                }
            }
        }
    }
}

impl Default for CoverageGate {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Exhaustive opcode classifiers (the load-bearing exhaustiveness)
// ---------------------------------------------------------------------------
//
// These are wildcard-free. If `AArch64Opcode` / `X86Opcode` gains a variant,
// the crate WILL NOT COMPILE until that variant is classified here. That is the
// structural guarantee that no opcode can ship emittable-but-unproven without a
// human writing down a decision (and a reason, if fail-closed).
//
// Allowlist policy: an opcode may be `FailClosedAllowlisted` ONLY if either
//   (a) the encoder returns `EncodeError::UnsupportedOpcode` for it (no compiled
//       program can contain it — the pseudo-mask-extract / bool-select family),
//       or
//   (b) it is a structural/ABI/branch-target form whose correctness is covered
//       elsewhere (frame/regalloc/relocation proof families) rather than by a
//       per-instruction trust_ir<->machine equivalence in the function-verifier
//       mapping.
// Each `reason` documents which case applies.

/// Classify an AArch64 opcode. WILDCARD-FREE on purpose — see module note.
pub fn classify_aarch64(opcode: AArch64Opcode) -> OpcodeClass {
    use AArch64Opcode as O;
    use OpcodeClass::*;

    // Pseudo / trap forms are skipped by the verifier; mirror that here. Keep
    // this list in sync with `AArch64Opcode::is_pseudo` + the verifier's
    // `trap_skip_reason`. Classified in the single exhaustive WILDCARD-FREE
    // match below so a newly-added opcode fails to compile until a human
    // classifies it (the structural fix for the #68-fneg class).
    match opcode {
        // ---- Pseudo / trap forms: skipped by the verifier (no value proof) ----
        O::Phi | O::StackAlloc | O::Copy | O::Nop | O::Retain | O::Release => PseudoOrTrap,
        // Emission-time alignment padding. EMITTABLE (encodes to the
        // architectural NOP 0xD503201F) but carries NO value/memory/branch
        // semantics — there is no trust_ir expression to prove equivalent.
        // Its two real obligations are covered elsewhere: (1) the word IS the
        // architectural NOP — enforced by the exact A64 decode-check arm for
        // AlignNop over the final bytes; (2) every offset derivation counts it
        // — enforced structurally (it is a real arena instruction walked by
        // branch resolution/encoding/EH re-derivation alike) and by the EH
        // `encoder offset == re-derived offset` cross-check. The lowerer never
        // selects it; only the loop-head alignment pass creates it, after all
        // proof-carrying passes have run.
        O::AlignNop => FailClosedAllowlisted {
            reason: "alignment padding NOP: no value semantics to prove; byte-exactness \
                     covered by the A64 decode-check (word must equal 0xD503201F) and \
                     offset integrity by the EH offset cross-check. Created only at \
                     emission by loop_align, never selected by the lowerer.",
        },
        O::Brk
        | O::TrapOverflow
        | O::TrapBoundsCheck
        | O::TrapBoundsCheckExact
        | O::TrapNull
        | O::TrapNullIfZero
        | O::TrapDivZero
        | O::TrapDivZeroIfZero
        | O::TrapShiftRange
        | O::TrapShiftRangeIfOOB
        | O::TrapOverflowExact => PseudoOrTrap,

        // ---- Emitted value/effect surface: MUST carry accepted evidence or RED ----
        O::AddRR | O::AddRI | O::SubRR | O::SubRI | O::MulRR | O::Madd | O::Msub | O::Neg => {
            EmittableNeedsProof
        }
        O::SDiv | O::UDiv => EmittableNeedsProof,
        O::CmpRR | O::CmpRI | O::CMPWrr | O::CMPXrr | O::CMPWri | O::CMPXri => EmittableNeedsProof,
        O::Tst => EmittableNeedsProof,
        O::CSet => EmittableNeedsProof,
        O::BCond | O::Bcc => EmittableNeedsProof,
        // HONESTY (task #61): RET's only mapped proof is the degenerate ledger
        // entry "Call lowering: RET branches to LR" (X==X, no independent machine
        // model). It proves nothing, so RET is NOT covered. The control-target
        // correctness is the CFG/return-edge, covered by the branch/call families
        // — same disposition as the AArch64 B/Br/Ret branch-target allowlist.
        O::Ret => FailClosedAllowlisted {
            reason: "return branch target — its only mapped value-proof was a DEGENERATE X==X \
                     (Call lowering: RET branches to LR) that proved nothing and was RETRACTED \
                     (#62); coverage NOT claimed. The return edge is covered by the \
                     Branch/CallLowering family (CFG edge, not a per-instruction value \
                     equivalence). Pending a faithful return-edge obligation.",
        },
        // HONESTY (task #61): the integer load/store opcodes' only mapped proofs
        // are the degenerate ledger entries "Load_I* -> LDR*ui"/"Store_I* -> STR*ui"
        // (X==X self-equalities — the trust_ir memory expression and the machine
        // side are the SAME constructed expression, no independent address-mode
        // encoder). They prove nothing, so these opcodes are NOT covered. The
        // effective-address memory correctness is tracked by the Memory/AddressMode
        // family; coverage is NOT claimed here pending a faithful independent
        // address-mode encoder obligation (debt: KNOWN_DEGENERATE_PENDING_FIX).
        O::LdrRI
        | O::LdrbRI
        | O::LdrhRI
        | O::LdrsbRI
        | O::LdrshRI
        | O::LdrRO
        | O::LdrbRO
        | O::LdrhRO
        | O::VolatileLdrRI
        | O::VolatileLdrbRI
        | O::VolatileLdrhRI
        | O::StrRI
        | O::StrbRI
        | O::StrhRI
        | O::StrRO
        | O::StrbRO
        | O::StrhRO
        | O::VolatileStrRI
        | O::VolatileStrbRI
        | O::VolatileStrhRI => EmittableNeedsProof,
        // Typed assembler aliases are not selected by the lowering pipeline.
        O::STRWui
        | O::STRXui
        | O::STRSui
        | O::STRDui => FailClosedAllowlisted {
            reason: "typed STR assembler alias is never selected by lowering; canonical emitted \
                     stores remain in the value/effect denominator",
        },
        O::StpPreIndex | O::StpRI | O::LdpRI | O::LdpPostIndex => EmittableNeedsProof,
        O::FaddRR | O::FsubRR | O::FmulRR | O::FnegRR | O::FminnmRR | O::FmaxnmRR => {
            EmittableNeedsProof
        }
        // Scalar FUSED multiply-add (FMADD): credited via OPERAND RECONSTRUCTION
        // against the shared single-rounding `fp.fma` bit-model, exactly like the
        // FADD/FMUL FP reconstruction. A round-TWICE unfused model (FMUL then
        // FADD) or a sign-flipped FMSUB model REFUTES on a divergent triple.
        O::FmaddRR => EmittableNeedsProof,
        // HONESTY (task #61): FMOV (FPR<-FPR scalar copy) maps only to the
        // degenerate "CopyProp: COPY(x) == x" ledger entry (X==X); it proves
        // nothing, so it is NOT covered. The bit-preserving copy correctness needs
        // a faithful bit-identity obligation (cf. the x86 Copy_F32/F64 proofs which
        // ARE genuine and on the allowlist). Pending that, coverage NOT claimed.
        O::FmovFprFpr => EmittableNeedsProof,
        O::FcvtzsRR | O::FcvtzuRR | O::ScvtfRR | O::UcvtfRR | O::FcvtSD | O::FcvtDS => {
            EmittableNeedsProof
        }
        O::Sxtb | O::Sxth | O::Sxtw | O::Uxtb | O::Uxth | O::Uxtw => EmittableNeedsProof,
        // HONESTY (task #61): the GPR register-copy moves (MOV/MOVWrr/MOVXrr) map
        // only to the degenerate "CopyProp: COPY(x) == x" ledger entry (X==X); it
        // proves nothing, so they are NOT covered. The bit-preserving copy needs a
        // faithful bit-identity obligation (cf. the x86 Copy_I32/I64 proofs which
        // ARE genuine and on the allowlist). Pending that, coverage NOT claimed.
        O::MovR => EmittableNeedsProof,
        O::MOVWrr | O::MOVXrr => FailClosedAllowlisted {
            reason: "typed MOV assembler alias is never selected by lowering; canonical emitted \
                     MovR remains in the value/effect denominator",
        },
        // MOVN/MOVK are genuinely emittable, so missing width-sensitive or
        // contextual proof coverage must remain an honest RED gate result.
        // They are not eligible for the never-selected fail-closed allowlist.
        O::Movz | O::MOVZWi | O::MOVZXi | O::Movn | O::Movk => EmittableNeedsProof,
        O::AndRR | O::AndRI | O::OrrRR | O::OrrRI | O::EorRR | O::EorRI => EmittableNeedsProof,
        // EOR with a ROR-shifted second source (EOR Rd, Rn, Rm, ROR #k) —
        // emitted by the rotate-fusion peephole (`eor_rotate_fuse`) for the ARX
        // `x ^= ROTL(v, r)` idiom (salsa20). CREDITED via the FAITHFUL
        // rotate-XOR obligations (lowering_proof::all_eor_ror_shift_proofs — the
        // SOURCE is the frontend ROTL-XOR idiom `a ^ ((b<<r)|(b>>(w-r)))`, the
        // MACHINE is the shifted-register EOR-ROR model `a ^ ((b>>k)|(b<<(w-k)))`
        // with r = w-k: structurally DISTINCT (the two shifted halves in the
        // opposite OR order), provably equal), gate-bound through
        // `aarch64_width_polymorphic_proofs` so BOTH the W (32) and X (64) forms
        // must discharge. The wrong-amount, wrong-shift-kind (ROR-vs-LSR) and
        // operand-swap controls REFUTE (see `eor_ror_shift_wrong_controls`).
        O::EorRRShift => EmittableNeedsProof,
        // EOR with an LSL/LSR-shifted second source (EOR Rd, Rn, Rm, LSL|LSR #k).
        // Credited via RECONSTRUCTION, not a static-DB obligation: a same-algebra
        // theorem here would be the degenerate `a ^ (b<<k) == a ^ (b<<k)` X==X
        // retracted under #62. `MachineSideProvenance::Reconstructed` rebuilds the
        // machine side from the REAL emitted opcode + operand positions, so a
        // wrong shift KIND (LSL vs LSR), a wrong AMOUNT, or swapped Rn/Rm refutes.
        O::EorRRLsl | O::EorRRLsr => EmittableNeedsProof,
        // ADD/SUB with an LSL-shifted second source (ADD/SUB Rd, Rn, Rm, LSL #k) —
        // emitted by the shift-ALU fusion peephole (`shift_alu_fuse`) for an
        // explicit `y + (x<<k)` / `y - (x<<k)` and the mul-by-constant strength
        // reduction (LslRI + AddRR). CREDITED via the FAITHFUL ring obligations
        // (lowering_proof::all_add_sub_lsl_shift_proofs — the SOURCE is
        // `base +/- src*2^k` (bvmul), the MACHINE is `base +/- (src<<k)` (bvshl):
        // structurally DISTINCT, provably equal — the bvmul-vs-bvshl shape of
        // proof_ldrsw_ro_scaled_addr), gate-bound through
        // `aarch64_width_polymorphic_proofs` so BOTH the W (32) and X (64) forms
        // must discharge. The wrong-amount, ADD-vs-SUB, and SUB operand-swap
        // controls REFUTE (see `add_sub_lsl_shift_wrong_controls`).
        O::AddRRShift | O::SubRRShift => EmittableNeedsProof,
        // ADD with an LSR-shifted second source (ADD Rd, Rn, Rm, LSR #k) —
        // emitted by the shift-ALU fusion peephole (`shift_alu_fuse`) for the
        // srem/sdiv-by-constant magic sign-bit correction (`lsr t, x, #31;
        // add r, r, t`) and the udiv magic add-back (`lsr t, sub, #1;
        // add r, mh, t`). CREDITED via the FAITHFUL obligations
        // (lowering_proof::all_add_lsr_shift_proofs — the SOURCE is
        // `base + src/2^k` (bvudiv), the MACHINE is `base + (src>>u k)` (bvlshr):
        // structurally DISTINCT, provably equal — the LSR analogue of the
        // bvmul-vs-bvshl ring shape above), gate-bound through
        // `aarch64_width_polymorphic_proofs` so BOTH the W (32) and X (64) forms
        // must discharge. The wrong-amount, ASR-not-LSR, LSL-not-LSR, and
        // SUB-not-ADD controls REFUTE (see `add_lsr_shift_wrong_controls`).
        O::AddRRShiftLsr => EmittableNeedsProof,
        // RECONSTRUCTION (task #63 Step 4, resolves #57): the scalar shift opcodes
        // (LSL/LSR/ASR) are now CREDITED via OPERAND RECONSTRUCTION. The gate
        // rebuilds the machine side from the REAL opcode with the FAITHFUL
        // hardware-amount-masked encoder (`encode_lsl_rr_masked` etc.) under a
        // LOAD-BEARING `amount < width` precondition: in range the mask is the
        // identity and the two sides agree; OUT of range the masked machine side
        // and the clamp-to-0 trust_ir side DIVERGE, so the precondition is
        // genuinely required for Valid (strip it and a shift by exactly `width`
        // refutes — that is the #57 fix, no longer cosmetic). A wrong shift opcode
        // (LSL-for-LSR ⇒ bvshl vs bvlshr) also refutes. They are EmittableNeedsProof
        // and the reconstruction-credit branch in `audit_aarch64` reports COVERED.
        O::LslRR | O::LslRI | O::LsrRR | O::LsrRI | O::AsrRR | O::AsrRI => EmittableNeedsProof,

        // ---- Fail-closed / covered-elsewhere allowlist (with reasons) ----
        //
        // (a) Branch-target forms: correctness is the CFG edge, proven by the
        //     branch/CFG/relocation families, not a per-instruction value
        //     equivalence. Emittable but no opcode_to_proof_query value-proof.
        // Direct PC-relative branch / call (B / BL): now credited per-instruction
        // to the AY-discharged BRANCH26 call-relocation proof
        // (proof_branch26_call_target: `B/BL == S+A`, faithful P+offset vs S+A).
        // So they carry a real proof and are per-compile promotable.
        O::B | O::Bl | O::BL | O::TailCall => EmittableNeedsProof,
        // Indirect branch/call (Br / Blr / BLR): the register target is computed
        // by the surrounding proofs and the transfer is architecturally fixed, so
        // a per-instruction value-proof would be the target==target tautology —
        // CoveredElsewhere (see function_verifier::is_covered_elsewhere_indirect_branch).
        O::Br | O::Blr | O::BLR => FailClosedAllowlisted {
            reason: "indirect branch/call target — covered elsewhere (register target \
                     established by surrounding proofs; transfer architecturally fixed)",
        },
        O::Cbz | O::Cbnz | O::Tbz | O::Tbnz => FailClosedAllowlisted {
            reason: "compare-and-branch target — covered by Branch proofs (CFG edge, not value)",
        },

        // (b) Kept-carrier checked-overflow DETECTION forms (#67). ADDS/SUBS
        //     (flag-recompute, V-flag / carry rule) are COVERED by the registered
        //     checked-overflow proof family: bound by
        //     `FunctionVerifier::opcode_to_proof_query` to the faithful
        //     `Checked{Sadd,Ssub}_I64` obligations, which discharge FORMALLY via
        //     the strict ay gate (fast — no multiply hardness). They report
        //     [COVERED].
        O::AddsRR | O::SubsRR => EmittableNeedsProof,

        // (b.0) SMULH/UMULH (high-half overflow product). The genuine equivalence
        //       theorem (full 2w-bit product != sign/zero-ext of the wrapped w-bit
        //       value, vs. the SMULH/UMULH high-half predicate) is REAL and
        //       non-degenerate, but its FORMAL discharge at 64-bit is SMT-hard
        //       (128-bit `bvmul` times out — confirmed >120s; even the 32-bit
        //       packed shape times out). The opcode rows remain in the denominator
        //       and the default evaluator accepts their non-degenerate 64-bit
        //       obligations as STATISTICAL regression evidence, not formal proof.
        //       The same overflow-equivalence theorem is also EXHAUSTIVELY
        //       verified at width-8 (all 2^16 cases) AND ay-formal at width-8 by
        //       the registered `exact_{s,u}mul_flag_equivalence_i8` proofs. The
        //       predicate is width-uniform, so width-8 witnesses its shape; the
        //       full 64-bit discharge is pending solver capacity. This is NOT a
        //       64-bit formal claim.
        O::Smulh | O::Umulh => EmittableNeedsProof,

        // (b.1) The flag-setting IMMEDIATE forms ADDS/SUBS #imm have NO lowering
        //       emission path (only the RR forms are selected; the sole AddsRI/
        //       SubsRI reference is a scheduler-cost match) and no AddsRI/SubsRI-
        //       specific proof exists. Fail-closed as never-selected rather than
        //       silently binding them to the RR-form proof.
        O::AddsRI | O::SubsRI => FailClosedAllowlisted {
            reason: "flag-setting immediate form (ADDS/SUBS #imm) never selected by the lowerer — \
                     fail-closed (no AddsRI/SubsRI emission path; only the RR forms are emitted)",
        },

        // (b.2) i128 carry-chain (ADC/SBC) and 32->64 widening multiply (SMULL/
        //       UMULL). The packed Checked*_I64 proofs do NOT model carry
        //       propagation across 128-bit halves nor 32->64 widening, so binding
        //       them here would be an unfaithful (f81e45b-class) mapping. SMULL
        //       remains an explicit RED denominator row; UMULL is now covered by
        //       its own faithful widening obligation (proof_umull_rr — the
        //       single-form zext64*zext64 theorem; the sext confusion refutes).
        // i128 carry-chain HIGH limb (ADC/SBC): now credited to the FAITHFUL
        // whole-chain composition proof (proof_iadd/isub_i128_whole_chain: the
        // ADDS;ADC / SUBS;SBC pair reconstructs the native 128-bit value vs the
        // root BvAdd/BvSub — structurally distinct, NOT X==X). The shared low-limb
        // ADDS/SUBS is re-routed to the same proof block-aware (see
        // function_verifier::i128_carry_chain_low_limb_query); the i64 checked-add
        // path is unchanged.
        O::Adc | O::Sbc => EmittableNeedsProof,
        O::Smull | O::Umull => EmittableNeedsProof,

        // HONESTY (task #61): CSEL/CSINC/CSNEG map to the IfConversion ledger
        // entries ("diamond CSEL ≡ …", "CSINC — …", "CSNEG — …"), which are on
        // KNOWN_DEGENERATE_PENDING_FIX — they are X==X self-equalities (the machine
        // side was built to mirror the spec, no independent CSEL/CSINC/CSNEG
        // encoder). They prove nothing, so these opcodes are NOT covered. Pending a
        // faithful independent conditional-select machine encoder, coverage is NOT
        // claimed. (CSINV likewise stays allowlisted — no registered proof at all.)
        O::Csel | O::Csinc | O::Csneg => EmittableNeedsProof,
        O::Csinv => FailClosedAllowlisted {
            reason: "CSINV is encoder-supported but never selected by lowering; emitted \
                     CSEL/CSINC/CSNEG remain RED in the value/effect denominator",
        },
        // FCSEL (scalar FP conditional select, EOR the integer CSEL family above)
        // — emitted by the FP-`Select` isel path (CMP cond,#0 + FCSEL cc). Unlike
        // the integer CSEL family, it IS covered: via the FAITHFUL bit-preserving
        // mux obligations (all_fcsel_proofs — the SOURCE is `ite(trust_ir icmp,
        // a, b)` over RAW FPR bits, the MACHINE is `ite(eval_condition(cc,
        // encode_cmp(sel,0)), a, b)`; structurally DISTINCT — a direct compare vs
        // the NZCV-subtraction flag model — provably equal). Bound through
        // `aarch64_width_polymorphic_proofs` so BOTH the S (f32) and D (f64) forms
        // discharge; the inverted-cond and operand-swap controls REFUTE (see
        // `fcsel_wrong_controls`). Bit-preserving by construction: NaN payloads,
        // signed zeros and denormals pass through untouched (no FP arithmetic).
        O::FcselRR => EmittableNeedsProof,
        // Bitfield EXTRACT (UBFM unsigned / SBFM signed) is CREDITED via the
        // FAITHFUL extract-ENCODING proofs: the isel encoding `immr=lsb,
        // imms=lsb+width-1`, decoded by the ARM hardware UBFM/SBFM (mask width
        // `imms-immr+1`), equals the trust_ir ExtractBits/SextractBits (mask width
        // `width`). The machine and source sides are STRUCTURALLY DISTINCT (the
        // machine mask/shift amounts are arithmetic trees over the ENCODING, NOT
        // the recovered width — so this is NOT the degenerate X==X that reusing
        // `encode_ubfm_extract` would be), so a wrong immr/imms formula REFUTES.
        // Emitted at BOTH register widths; the width-polymorphic gate requires the
        // w32 AND w64 proofs (see `aarch64_width_polymorphic_proofs`).
        O::Ubfm | O::Sbfm => EmittableNeedsProof,
        // BFM (bitfield INSERT — read-modify-write), ROR-immediate, and scalar
        // RBIT (a SWAR bit-reversal
        // butterfly) still lack a faithful per-opcode obligation.
        O::Bfm | O::RorRI | O::Rbit => EmittableNeedsProof,
        // RECONSTRUCTION (task #63 Step 4): ORN/BIC are now CREDITED via OPERAND
        // RECONSTRUCTION. BIC rebuilds to `Rn & ~Rm` (trust_ir BandNot) and ORN to
        // `Rn | ~Rm` (trust_ir BorNot) from the REAL opcode; ORN with the zero
        // register in the rn slot reconstructs as the MVN/Bnot alias (`~Rm`). Both
        // are non-commutative, so a wrong-wiring (swapped operands) refutes —
        // genuine reconstruction content. They are EmittableNeedsProof and the
        // reconstruction-credit branch in `audit_aarch64` reports COVERED.
        O::OrnRR | O::BicRR => EmittableNeedsProof,

        // Scalar FP abs / sqrt / div: bound to the registered FloatingPoint
        // value proofs whose machine side IS that exact instruction, at BOTH F32
        // and F64 (width-polymorphic; see `aarch64_width_polymorphic_proofs`).
        // They report [COVERED].
        O::FabsRR | O::FsqrtRR | O::FdivRR => EmittableNeedsProof,
        // FRINTM/FRINTP/FRINTZ — round to integral (floor/ceil/trunc). Now
        // credited per-instruction via OPERAND RECONSTRUCTION (the unary FP
        // template): the machine side is `encode_frint{m,p,z}` rebuilt from the
        // REAL emitted opcode, paired with the trust_ir `Ffloor`/`Fceil`/`Ftrunc`
        // round node — a wrong rounding direction REFUTES on a non-integral
        // input. (Still ALSO backed by the Ffloor/Fceil/Ftrunc_F{32,64}
        // width-polymorphic DB proofs.)
        O::FrintmRR | O::FrintpRR | O::FrintzRR => EmittableNeedsProof,

        // Scalar FP compare (FCMP + CSET): credited to the FAITHFUL
        // `Fcmp_<cond>_F{32,64}` proofs whose machine side models FCMP→NZCV then
        // CSET reading `from_floatcc(cond)` (encode_fcmp via the nzcv flag
        // model); a wrong condition-code mapping REFUTES. opcode_to_proof_query
        // binds a representative condition; all 14 conditions × 2 widths are
        // registered and discharged.
        O::Fcmp => EmittableNeedsProof,
        // Scalar FMOV-immediate: credited per-instruction via OPERAND
        // RECONSTRUCTION — the machine side is the hardware VFPExpandImm DECODE
        // (a structural bit-assembly, `encode_fmov_imm_bits`) of the 8-bit field
        // the codegen encoder picks, proven to round-trip to the named constant's
        // IEEE bits. A wrong field/placement REFUTES (not `const == const`).
        O::FmovImm => EmittableNeedsProof,

        // GPR<->FPR FMOV is a material bit-preserving value transfer. The shared
        // bitvector-domain identity is degenerate X==X, so these emitted forms
        // remain explicit RED rows pending an independently decoded transfer model.
        O::FmovFprGpr | O::FmovGprFpr => EmittableNeedsProof,

        // (a) Remaining FP forms not in the value mapping (half-precision casts):
        //     pending FP proof mapping. The half-precision FCVT forms genuinely
        //     change the IEEE format (round/widen/narrow), so — unlike the
        //     bit-preserving FMOV moves above — they remain RED pending faithful
        //     half-precision value evidence.
        O::FcvtSH | O::FcvtHS | O::FcvtDH | O::FcvtHD => EmittableNeedsProof,

        // (b) Move-immediate / PC-relative / GOT / TLS address materialization:
        //     correctness is the relocation/addressing proof family.
        // ADRP + ADD PC-relative address materialization is now credited
        // per-instruction to the AY-discharged MachO data-relocation proofs
        // (PAGE21 `ADRP == page(S+A)`, PAGEOFF12 `ADRP+ADD == S+A`; faithful
        // page+offset reconstruction, NOT a const==const X==X). So it carries a
        // real proof and is per-compile promotable. See function_verifier's
        // Adrp/AddPCRel -> MachOEmission proof query.
        // ADRP/ADD page+offset, the TLS-descriptor load (LdrTlvp), and the GOT load
        // (LdrGot, fn-pointer/extern-symbol address) are credited to the
        // AY-discharged Mach-O relocation proofs (PAGE21/PAGEOFF12 +
        // TLVP_LOAD_PAGEOFF12 + GOT_LOAD_PAGEOFF12 ADRP+LDR == G+A).
        // ADR (the dense-`match` / fieldless-enum JUMP-TABLE PC-relative base) is
        // credited to proof_adr_jumptable_pcrel (`ADR Xd == table_base`, the ring
        // identity `P + (T - P) == T`, the byte-granular sibling of BRANCH26).
        O::Adrp | O::AddPCRel | O::LdrTlvp | O::LdrGot | O::Adr => EmittableNeedsProof,
        // LdrGottprel (ELF initial-exec GOT-TPREL load) has solver-backed
        // formal evidence from the ELF TLSIE relocation obligations
        // (`aarch64_elf_tls_reloc_proofs`: TLSIE_ADR_GOTTPREL_PAGE21 ADRP ==
        // page(G+A); TLSIE_LD64_GOTTPREL_LO12_NC ADRP+LDR addresses exactly
        // the 8-aligned GOT slot G+A) — the ELF TLS sibling of LdrGot/LdrTlvp
        // above. This instruction-level evidence does not authorize the
        // production Certified object inventory; every AArch64 ELF relocation
        // row remains fail-closed there.
        O::LdrGottprel => EmittableNeedsProof,
        // LDRSW Xt,[Xn,Xm,LSL#2] (the jump-table scaled table-entry load) is
        // credited to the FAITHFUL scaled-EFFECTIVE-ADDRESS proof
        // proof_ldrsw_ro_scaled_addr (AddressMode): `base + (index<<2) ==
        // base + 4*index` (bvshl vs bvmul; a wrong scale REFUTES). HONEST SCOPE:
        // the address-mode credit only — strictly stronger than the degenerate
        // `("load", Memory)` query, NOT a full memory-load proof (the dereference +
        // i32->i64 sext loaded VALUE remains the shared Ldr* unfaithful-load debt).
        O::LdrswRO => EmittableNeedsProof,
        // MovI is accepted through the non-degenerate hw0 MOVZ obligation;
        // AddRIShift12 remains RED. LdrLiteral is never selected.
        O::MovI | O::AddRIShift12 => EmittableNeedsProof,
        O::LdrLiteral => FailClosedAllowlisted {
            reason: "PC-relative literal-load form is encoder-supported but never selected by lowering",
        },
        // ELF local-exec TLS TPREL adds: in-object bytes are the FIXED
        // `ADD Xd, Xn, #0 (, LSL #12)` skeletons (imm12 placeholder 0); the
        // added value is entirely the linker's TPREL(S) patch under
        // `R_AARCH64_TLSLE_ADD_TPREL_HI12`/`_LO12_NC`, so correctness is the
        // ELF TLS relocation contract (kind<->model agreement is enforced
        // fail-closed in `aarch64_elf_reloc_kind`), not a per-instruction
        // trust_ir<->machine value proof.
        O::AddTprelHi12 | O::AddTprelLo12 => FailClosedAllowlisted {
            reason: "ELF TLS local-exec TPREL add — correctness is the linker-patched TLSLE relocation family",
        },

        // (a) Writeback memory, system-register, and active atomic families are
        //     emitted effects/values and stay in the denominator. Partial
        //     Memory/Atomic queries do not earn complete-opcode credit.
        O::LdrPreIndex | O::StrPreIndex | O::LdrPostIndex | O::StrPostIndex => EmittableNeedsProof,
        O::Mrs => EmittableNeedsProof,
        O::Dmb => FailClosedAllowlisted {
            reason: "covered elsewhere: non-value fence ordering is checked by the \
                     AtomicOperations Fence_* -> DMB {ISH,ISHLD,ISHST} family and \
                     dataflow_integrity treats Fence as a synchronization barrier",
        },
        O::Dsb | O::Isb => FailClosedAllowlisted {
            reason: "DSB/ISB are encoder-supported system forms but are never selected by lowering",
        },
        O::Ldar
        | O::Ldarb
        | O::Ldarh
        | O::Stlr
        | O::Stlrb
        | O::Stlrh
        | O::Cas
        | O::Casa
        | O::Casal
        | O::Casl
        | O::Swp
        | O::Swpa
        | O::Swpal
        | O::Swpl => EmittableNeedsProof,
        O::Ldaxr | O::Stlxr => FailClosedAllowlisted {
            reason: "exclusive-loop LDAXR/STLXR forms are encoder-supported but never selected by lowering",
        },
        O::Ldadd
        | O::Ldadda
        | O::Ldaddal
        | O::Ldaddl
        | O::Ldclr
        | O::Ldclra
        | O::Ldclral
        | O::Ldclrl
        | O::Ldeor
        | O::Ldeora
        | O::Ldeoral
        | O::Ldeorl
        | O::Ldset
        | O::Ldseta
        | O::Ldsetal
        | O::Ldsetl
        | O::Ldsmax
        | O::Ldsmaxa
        | O::Ldsmaxal
        | O::Ldsmaxl
        | O::Ldsmin
        | O::Ldsmina
        | O::Ldsminal
        | O::Ldsminl
        | O::Ldumax
        | O::Ldumaxa
        | O::Ldumaxal
        | O::Ldumaxl
        | O::Ldumin
        | O::Ldumina
        | O::Lduminal
        | O::Lduminl => EmittableNeedsProof,
        // NEON BITWISE vector ops (AND/ORR/EOR/BIC/NOT) are CREDITED via the
        // FAITHFUL per-LANE-intent == whole-register lowering proofs: the SOURCE is
        // the trust_ir per-lane vector op (split the V128 into the 16 `.16B` byte
        // lanes, apply the lane bitwise op, concat back) and the MACHINE is the
        // single whole-128-bit-register op the lowerer emits. The two sides are
        // STRUCTURALLY DISTINCT (a 16-lane concat tree vs one whole-register op),
        // so this is NOT the degenerate X==X the OLD same-shape `proof_vector_*`
        // proofs are, and a wrong machine op (ORR for AND, or BIC without the `~vm`
        // complement) REFUTES. ONE 128-bit obligation per opcode suffices because
        // bitwise ops are lane-width-INDEPENDENT over the register. Bound by
        // `opcode_to_proof_query` (NeonLowering, "<opcode>.16b lanewise-intent").
        O::NeonAndV | O::NeonOrrV | O::NeonEorV | O::NeonBicV | O::NeonNotV => EmittableNeedsProof,
        // NEON LANE-WISE COMPUTE ops (integer arith / compare / min-max / immediate
        // shift) are CREDITED via the FAITHFUL per-lane D-REGISTER-PAIR obligations
        // (neon_lowering_proofs::proof_neon_*_lanewise_4s). The SOURCE slices each
        // lane DIRECTLY from the two 64-bit D-halves of the Q register and applies
        // the per-lane op; the MACHINE is the real `encode_neon_*` encoder over the
        // reassembled whole register (`Concat(hi, lo)`). The two sides are
        // STRUCTURALLY DISTINCT (raw-half `Var` leaf vs an `Extract`-of-`Concat`),
        // so this is NOT the degenerate same-shape X==X the OLD `proof_vector_*`
        // obligations are, and a WRONG NEON instruction — wrong op (SUB for ADD),
        // wrong SIGNEDNESS (SMAX for UMAX, CMGT for CMHI, USHR for SSHR), wrong
        // DIRECTION (CMGE for CMGT), or wrong LANE WIDTH — REFUTES (see the
        // `neon_lanewise_compute_wrong_encodings_refute` negative controls). One
        // `.4S` obligation per opcode suffices (the arrangement the reduction /
        // vectorization passes emit; the D-pair decomposition is arrangement-
        // parametric). Bound by `opcode_to_proof_query` (NeonLowering,
        // "<opcode>.4s lanewise-intent"). HONEST SCOPE: this certifies the emitted
        // instruction computes the right per-lane op at the right width — the same
        // right-instruction guarantee the gate certifies for every opcode — with NO
        // cross-lane reconstruction content, because NEON lanes are independent.
        O::NeonAddV
        | O::NeonSubV
        | O::NeonMulV
        | O::NeonCmeqV
        | O::NeonCmgeV
        | O::NeonCmgtV
        | O::NeonCmhiV
        | O::NeonCmhsV
        | O::NeonShlVImm
        | O::NeonUshrVImm
        | O::NeonSshrVImm
        | O::NeonSmaxV
        | O::NeonSminV
        | O::NeonUmaxV
        | O::NeonUminV
        // NEON POPCOUNT-FOLD ops (per-byte population count + unsigned add long
        // pairwise) are CREDITED via the FAITHFUL D-REGISTER-PAIR obligations
        // (neon_lowering_proofs::proof_neon_cntv_lanewise_16b / _uaddlpv_*). The
        // SOURCE slices each INPUT lane DIRECTLY from the two 64-bit D-halves and
        // applies the per-byte popcount / pairwise zext-add; the MACHINE is the real
        // `encode_neon_cnt` / `encode_neon_uaddlp` over the reassembled register.
        // STRUCTURALLY DISTINCT (raw-half `Var` leaf vs an `Extract`-of-`Concat`),
        // and a WRONG encoding — CNT-as-identity, UADDLP-as-pairwise-SUB — REFUTES
        // (see `neon_popcount_wrong_encoding_controls`). Bound by
        // `opcode_to_proof_query` (NeonLowering, "<opcode>.16b/…lanewise-intent").
        | O::NeonCntV
        | O::NeonUaddlpV
        // NEON SIGNED add-long-pairwise (`SADDLP .16B->.8H` / `.8H->.4S`) is
        // CREDITED via the FAITHFUL D-REGISTER-PAIR obligations
        // (neon_lowering_proofs::proof_neon_saddlpv_16b_8h / _8h_4s) — the exact
        // signed sibling of the UADDLP obligations: the SOURCE slices each INPUT
        // lane from the raw D-halves and applies the pairwise SIGN-extending add;
        // the MACHINE is the real `encode_neon_saddlp` over the reassembled
        // register. A WRONG encoding — SADDLP-as-UADDLP (the classic sign
        // confusion), SADDLP-as-pairwise-SUB — REFUTES (see
        // `neon_saddlp_wrong_encoding_controls`). Bound by `opcode_to_proof_query`
        // (NeonLowering, "saddlpv.16b->.8h lanewise-intent").
        | O::NeonSaddlpV
        // NEON BIT (bitwise insert if true, tied destination) is CREDITED via the
        // FAITHFUL per-byte-lane obligation
        // (neon_lowering_proofs::proof_neon_bitv_lanewise_16b): SOURCE = 16-lane
        // per-byte `d ^ ((d ^ n) & m)`; MACHINE = the whole-register
        // `encode_neon_bit`. Lane-width-independent (like AND/ORR/EOR/BIC), so one
        // `.16B` obligation covers the `.2D` min/max use. The BSL/BIT/BIF wiring
        // confusions REFUTE (see `neon_bit_wrong_encoding_controls`). Bound by
        // `opcode_to_proof_query` (NeonLowering, "bitv.16b lanewise-intent").
        | O::NeonBitV
        // NEON SIGNED-ABS (`ABS.4S`) is CREDITED via the FAITHFUL D-REGISTER-PAIR
        // obligation (neon_lowering_proofs::proof_neon_absv_lanewise_4s). The SOURCE
        // slices each 32-bit lane DIRECTLY from the two 64-bit D-halves and applies
        // the per-lane signed abs (`ite(a <s 0, 0 - a, a)`, so abs(INT_MIN)==INT_MIN);
        // the MACHINE is the real `encode_neon_abs` over the reassembled register.
        // STRUCTURALLY DISTINCT (raw-half `Var` leaf vs an `Extract`-of-`Concat`),
        // and a WRONG encoding — abs-as-identity, abs-as-negate-always — REFUTES
        // (see `neon_abs_wrong_encoding_controls`). Bound by `opcode_to_proof_query`
        // (NeonLowering, "absv.4s lanewise-intent").
        | O::NeonAbsV
        // NEON UNSIGNED DOT-PRODUCT-ACCUMULATE (`UDOT.4S`, FEAT_DotProd) is CREDITED
        // via the FAITHFUL D-REGISTER-PAIR obligation
        // (neon_lowering_proofs::proof_neon_udotv_lanewise_4s). The SOURCE slices the
        // 4 input byte lanes of Vn/Vm AND the 32-bit ACCUMULATOR lane of Vd DIRECTLY
        // from the raw 64-bit D-halves and computes
        // `acc + sum_j(zext32(n_j) * zext32(m_j))`; the MACHINE is the real
        // `encode_neon_udot` over the reassembled registers. STRUCTURALLY DISTINCT
        // (raw-half `Var` leaf vs an `Extract`-of-`Concat`), and a WRONG encoding —
        // dot-without-accumulate, UDOT-as-SDOT (sign-extending), wrong byte group —
        // REFUTES (see `neon_udot_wrong_encoding_controls`). Bound by
        // `opcode_to_proof_query` (NeonLowering, "udotv.4s lanewise-intent").
        | O::NeonUdotV
        // NEON BYTE-WISE EXTRACT/CONCATENATE (`EXT.16B #1/#4/#8/#12/#15`) is
        // CREDITED via the FAITHFUL D-REGISTER-PAIR obligations
        // (neon_lowering_proofs::proof_neon_extv_16b, one per emitted immediate:
        // the whole-i32-lane middle-window shifts #4/#8/#12 the stencil
        // vectorizer emits, plus the single-byte shifted-NEIGHBOR streams #1
        // (`a[iv+1]` forward) / #15 (`a[iv-1]` backward) the neon-bytesum stencil
        // count-if forms). The SOURCE selects every output byte DIRECTLY from the
        // raw 64-bit D-halves of Vn/Vm — including the bytes that CROSS the
        // D-half boundary, EXT's defining property — while the MACHINE is the
        // real `encode_neon_ext` (the ARM ARM Vm:Vn concatenation-extract in its
        // exact 128-bit `(Vn >> imm*8) | (Vm << (128-imm*8))` form) over the
        // reassembled registers. STRUCTURALLY DISTINCT (per-byte raw-half `Var`
        // extracts vs whole-register shift/OR), and a WRONG encoding — swapped
        // operands (the complementary window), a wrong immediate (off by one i32
        // lane), the OPPOSITE neighbor direction (#1<->#15), ext-as-identity —
        // REFUTES (see `neon_ext_wrong_encoding_controls`). The encoder REJECTS
        // every immediate other than 1/4/8/12/15 fail-closed. Bound by
        // `opcode_to_proof_query` (NeonLowering, "extv.16b lanewise-intent").
        | O::NeonExtV
        // NEON WIDENING MULTIPLY-ACCUMULATE-LONG (`SMLAL/SMLAL2/UMLAL/UMLAL2
        // .4S -> .2D`, the i32->i64 widening MAC the neon_array widening-dot
        // vectorizer emits) is CREDITED via the FAITHFUL D-REGISTER-PAIR ACCUMULATE
        // obligations (neon_lowering_proofs::all_neon_smlal_proofs — one whole-
        // register obligation per opcode whose SOURCE concatenates BOTH `.2D` lanes,
        // so a single-lane miswire refutes). The SOURCE slices the `.2D` accumulator
        // lane of Vd AND the two `.4S` operand lanes of Vn/Vm DIRECTLY from the raw
        // 64-bit D-halves and computes `acc_j + EXT64(n_s)*EXT64(m_s)` (EXT64 =
        // sign_ext(32) for SMLAL / zero_ext(32) for UMLAL, EXACT i32xi32->i64
        // product; s = j low / 2+j high); the MACHINE is the real `encode_neon_smlal`
        // over the reassembled registers. STRUCTURALLY DISTINCT (raw-half `Var` leaf
        // vs an `Extract`-of-`Concat`), and a WRONG encoding — sign confusion
        // (SMLAL-as-UMLAL), dot-without-accumulate, wrong `.4S` half (low-as-high),
        // truncating-32-bit-mul — REFUTES (see `neon_smlal_wrong_encoding_controls`).
        // Low vs high are SEPARATE opcodes (FCVTL/FCVTL2 precedent); the encoder
        // fail-closes on any non-.4S input. Bound by `opcode_to_proof_query`
        // (NeonLowering, "{smlalv,smlal2v,umlalv,umlal2v}.2d … widening-mac-intent").
        | O::NeonSmlalV
        | O::NeonSmlal2V
        | O::NeonUmlalV
        | O::NeonUmlal2V
        // NEON WIDENING ADD-WIDE (`UADDW/UADDW2 .4S -> .2D`, the unsigned
        // u32->u64 widening add the neon_array widening abs-sum vectorizer
        // (TRACK D) emits for `s(i64) += zext64(abs_bits(a_i32[i] [+ inv]))`,
        // replacing the UMLAL-by-ones MAC — per lane `acc_j + zext64(u_s)` ==
        // `acc_j + zext64(u_s)*1`) is CREDITED via the FAITHFUL D-REGISTER-PAIR
        // obligations (neon_lowering_proofs::all_neon_uaddw_proofs — one whole-
        // register obligation per opcode whose SOURCE concatenates BOTH `.2D`
        // lanes, so a single-lane miswire refutes). The SOURCE slices the `.2D`
        // addend lane of Vn AND the source `.4S` lane of Vm DIRECTLY from the
        // raw 64-bit D-halves and computes `addend_j + zext64(m_s)` (UNSIGNED
        // u32->u64 extension; s = j low / 2+j high); the MACHINE is the real
        // `encode_neon_uaddw` over the reassembled registers. STRUCTURALLY
        // DISTINCT (raw-half `Var` leaf vs an `Extract`-of-`Concat`), and a
        // WRONG encoding — sign confusion (UADDW-as-SADDW), widen-without-addend
        // (UXTL), wrong `.4S` half (low-as-high), truncating-32-bit-add —
        // REFUTES (see `neon_uaddw_wrong_encoding_controls`). Low vs high are
        // SEPARATE opcodes (SMLAL/FCVTL2 precedent); the ISA's plain THREE-
        // OPERAND form (Vd pure def, the addend is the SEPARATE source Vn — NOT
        // tied); the encoder fail-closes on any non-.4S input. Bound by
        // `opcode_to_proof_query` (NeonLowering, "[uaddwv,uaddw2v].2d ...
        // widening-add-intent").
        | O::NeonUaddwV
        | O::NeonUaddw2V
        // NEON SIGNED WIDENING ADD-WIDE (`SADDW/SADDW2 .4S -> .2D`, the signed
        // i32->i64 widening add the neon_predsum widening i64-accumulator
        // condsum emits for `s(i64) += (a_i32[iv] as i64) [if pred]`, replacing
        // the SMLAL-by-ones MAC — per lane `acc_j + sext64(masked_s)` ==
        // `acc_j + sext64(masked_s)*sext64(1)`) is CREDITED via the FAITHFUL
        // D-REGISTER-PAIR obligations (neon_lowering_proofs::
        // all_neon_saddw_proofs — one whole-register obligation per opcode
        // whose SOURCE concatenates BOTH `.2D` lanes, so a single-lane miswire
        // refutes). The SOURCE slices the `.2D` addend lane of Vn AND the
        // source `.4S` lane of Vm DIRECTLY from the raw 64-bit D-halves and
        // computes `addend_j + sext64(m_s)` (SIGNED i32->i64 extension; s = j
        // low / 2+j high); the MACHINE is the real `encode_neon_saddw` over the
        // reassembled registers. STRUCTURALLY DISTINCT (raw-half `Var` leaf vs
        // an `Extract`-of-`Concat`), and a WRONG encoding — zext confusion
        // (SADDW-as-UADDW, the mirror of the UADDW proofs' SADDW control: the
        // sign axis refutes BOTH ways), widen-without-addend (SXTL), wrong
        // `.4S` half (low-as-high), truncating-32-bit-add — REFUTES (see
        // `neon_saddw_wrong_encoding_controls`). Low vs high are SEPARATE
        // opcodes (SMLAL/UADDW precedent); the ISA's plain THREE-OPERAND form
        // (Vd pure def, the addend is the SEPARATE source Vn — NOT tied); the
        // encoder fail-closes on any non-.4S input. Bound by
        // `opcode_to_proof_query` (NeonLowering, "[saddwv,saddw2v].2d ...
        // widening-add-intent").
        | O::NeonSaddwV
        | O::NeonSaddw2V => EmittableNeedsProof,
        // NEON 32-BIT PAIR SWAP (`REV64 Vd.4S, Vn.4S`) emitted by the AoS
        // stride-2 complex-butterfly vectorizer (neon_butterfly) to swap each
        // `{rp, ip}` pair in-register before the twiddle multiply. CREDITED via
        // the FAITHFUL D-REGISTER-PAIR obligation
        // (neon_lowering_proofs::proof_neon_rev64v_4s): the SOURCE selects each
        // output 32-bit lane DIRECTLY from the raw D-halves at the swapped index
        // (`j ^ 1` — the swap NEVER crosses a 64-bit container, REV64's defining
        // property), the MACHINE is the real `encode_neon_rev64_4s` (the ARM ARM
        // within-container element reverse in whole-register shift/mask form)
        // over the reassembled register. STRUCTURALLY DISTINCT, and a WRONG
        // encoding — identity, DOUBLEWORD swap (wrong granularity), half-lane
        // smear (#16) — REFUTES (see `neon_rev64_wrong_encoding_controls`). The
        // encoder REJECTS every arrangement except the byte forms and `.4S`
        // fail-closed. Bound by `opcode_to_proof_query` (NeonLowering,
        // "rev64v.4s pair-swap-intent").
        O::NeonRev64V => EmittableNeedsProof,
        // NEON PER-BYTE 8-BIT REVERSE (`RBIT Vd.16B, Vn.16B`) emitted by the
        // neon-bitrev vectorizer for `out[i] = a[i].reverse_bits()` over a
        // `[u8; N]` — the EXACT instruction LLVM -O3 emits for that loop.
        // CREDITED via the FAITHFUL D-REGISTER-PAIR obligation
        // (neon_lowering_proofs::proof_neon_rbitv_16b): the SOURCE selects every
        // output bit DIRECTLY from the raw D-halves at the mirrored WITHIN-byte
        // index (output bit 8k+p <- input bit 8k+7-p — the reversal NEVER leaves
        // the byte, RBIT.16B's defining property), the MACHINE is the real
        // `encode_neon_rbit_16b` (the within-byte SWAR reversal butterfly in
        // whole-register shift/mask form) over the reassembled register.
        // STRUCTURALLY DISTINCT, and a WRONG encoding — identity, a byte swap
        // (REV16.8B — permutes BYTES not bits), a 16-bit-lane bit reverse (wrong
        // width) — REFUTES (see `neon_rbit_wrong_encoding_controls`). The
        // encoder REJECTS every arrangement except the byte forms fail-closed.
        // Bound by `opcode_to_proof_query` (NeonLowering,
        // "rbitv.16b per-byte-reverse-intent").
        O::NeonRbitV => EmittableNeedsProof,
        // NEON VECTOR MULTIPLY-ACCUMULATE (`MLA.4S`, the same-width tied-
        // accumulator MAC the neon_predsum MLA-BY-MASK condsum accumulate
        // emits for the `Gpr32` `.4S` masked-add `s(i32) += a_i32[iv] [if
        // pred]` — the compare mask lane is exactly -1/0, so `MLA(acc, a,
        // mask)` contributes `-a mod 2^32` on TRUE lanes and 0 otherwise; the
        // accumulators hold the NEGATED sum, folded by one wrapping SubRR at
        // the drain) is CREDITED via the FAITHFUL D-REGISTER-PAIR obligation
        // (neon_lowering_proofs::all_neon_mla_proofs — one whole-register
        // obligation with ALL FOUR `.4S` lanes concatenated, so a single-lane
        // miswire refutes). The SOURCE slices the accumulator lane of Vd and
        // the source lanes of Vn/Vm DIRECTLY from the raw 64-bit D-halves and
        // computes `acc_i + n_i*m_i` (mod 2^32 — the ISA's truncating MLA);
        // the MACHINE is the real `encode_neon_mla` over the reassembled
        // registers. STRUCTURALLY DISTINCT (raw-half `Var` leaf vs an
        // `Extract`-of-`Concat`), and a WRONG encoding — MLS-confusion
        // (subtracting), MUL-confusion (no accumulate), lane-swap — REFUTES
        // (see `neon_mla_wrong_encoding_controls`). Vd is a TIED def-use (the
        // accumulate READS it — has_tied_def_use, the UDOT/xMLAL class); the
        // encoder fail-closes on any non-.4S arrangement. Bound by
        // `opcode_to_proof_query` (NeonLowering, "mlav.4s lanewise
        // mul-accumulate-intent").
        O::NeonMlaV
        // NEON PAIRWISE WIDENING ACCUMULATE (`UADALP .4S -> .2D`, the tied-
        // accumulator pairwise widen the neon_array widening abs-sum
        // vectorizer TRACK D emits for `s(i64) += zext64(abs_bits(a_i32[i]
        // [+ inv]))`, replacing the UADDW/UADDW2 pair — same four zext64
        // terms per Q, adjacent-pair grouping, a pure mod-2^64 reassociation
        // under the both-lanes drain) is CREDITED via the FAITHFUL
        // D-REGISTER-PAIR obligation (neon_lowering_proofs::
        // all_neon_uadalp_proofs — one whole-register obligation with BOTH
        // `.2D` lanes concatenated, so a single-lane miswire refutes). The
        // SOURCE slices the `.2D` accumulator lane of Vd AND the adjacent
        // `.4S` source lane pair of Vn DIRECTLY from the raw 64-bit D-halves
        // and computes `acc_j + zext64(n_2j) + zext64(n_2j+1)` (UNSIGNED
        // u32->u64 extension); the MACHINE is the real `encode_neon_uadalp`
        // over the reassembled registers. STRUCTURALLY DISTINCT, and a WRONG
        // encoding — SADALP-sign-confusion, UADDLP-no-accumulate,
        // wrong-pairing — REFUTES (see
        // `neon_uadalp_wrong_encoding_controls`). Vd is a TIED def-use (the
        // accumulate READS it — has_tied_def_use; contrast the non-
        // accumulating NeonUaddlpV); the encoder fail-closes on any non-.4S
        // input. Bound by `opcode_to_proof_query` (NeonLowering, "uadalpv.2d
        // pairwise widening-accumulate-intent").
        | O::NeonUadalpV => EmittableNeedsProof,
        // NEON FP vector arith / compare (FaddV/FsubV/FmulV/FdivV/FcmgtV) are
        // CREDITED via the FAITHFUL per-lane D-REGISTER-PAIR FP obligations
        // (neon_lowering_proofs::all_neon_fp_lanewise_proofs — one obligation
        // per op x arrangement x lane, 30 total, gate-bound through
        // `aarch64_width_polymorphic_proofs` so BOTH `.4S` and `.2D` must
        // discharge). The SOURCE slices each lane DIRECTLY from the raw
        // D-halves and reinterprets its bits as the IEEE lane value
        // (`((_ to_fp eb sb) bits)`); the MACHINE is the real
        // `encode_neon_f*` lane encoder over the reassembled `Concat(hi, lo)`
        // register. STRUCTURALLY DISTINCT, so wrong-lane-wiring and
        // op-confusion (FADD-as-FSUB, FMUL-as-FDIV, FCMGT-as-FCMGE/FCMEQ)
        // REFUTE (see `neon_fp_lanewise_wrong_encoding_controls`).
        //
        // HONESTY — the SCOPE of this credit (read before citing): both sides
        // express the per-lane IEEE op with the SAME SMT FP node, so these
        // obligations certify the LANE PLUMBING (bits -> op -> lane, the same
        // right-instruction guarantee the gate certifies elsewhere) and NOT an
        // independent symbolic model of the FP circuits. The FP semantic
        // weight rests on the shared QF_FP model + the SILICON-VALIDATED
        // integer-only bit-model bridge (tests/bdefs_differential_bridge_neon_fp.rs)
        // + the whole-array bit-identity differential fuzz (fpmapfuzz).
        O::NeonFaddV
        | O::NeonFsubV
        | O::NeonFmulV
        | O::NeonFdivV
        | O::NeonFcmgtV => EmittableNeedsProof,
        // NEON FP fused multiply-accumulate (FMLA/FMLS), per-lane int->FP
        // conversion (UCVTF/SCVTF vector, integer form), and the FP lane->scalar
        // extract (DUP Dd, Vn.D[lane]) emitted by the IV-synthesized FP-reduction
        // vectorizer (neon_fpred) — all at `.2D`. They are CREDITED via the
        // FAITHFUL per-lane D-REGISTER-PAIR obligations
        // (neon_lowering_proofs::all_neon_fpred_proofs — 10: {FMLA, FMLS, UCVTF,
        // SCVTF, DupScalarD} x .2D 2 lanes), gate-bound through
        // `aarch64_width_polymorphic_proofs` so BOTH `.2D` lanes must discharge.
        // FMLA/FMLS use the shared SINGLE-rounding `fp.fma` (exactly the scalar
        // FMADD credit, lifted per lane — a round-twice model REFUTES);
        // UCVTF/SCVTF the per-lane int->FP convert (the scalar ScvtfRR/UcvtfRR
        // int->FP credit, lifted per lane, modeled directly with z3 `to_fp` over
        // the widened sign-bit-clear operand for the UNSIGNED case); DupScalarD a
        // faithful 64-bit lane bit-copy. The SOURCE slices each lane DIRECTLY from
        // the raw D-halves; the MACHINE is the real `encode_neon_{fmla,fmls,
        // scvtf_vec,ucvtf_vec,dup_scalar_d}` over the reassembled `Concat(hi, lo)`.
        // STRUCTURALLY DISTINCT, so op-confusion (FMLA<->FMLS), accumulator
        // miswire, sign confusion (UCVTF<->SCVTF), and wrong-lane wiring REFUTE
        // (see `neon_fpred_wrong_encoding_controls`). HONESTY as the FP lane ops:
        // both sides share the SMT FP node, so these certify the LANE/OP/WIDTH
        // plumbing, NOT an independent symbolic FP-circuit model.
        O::NeonFmlaV | O::NeonFmlsV | O::NeonUcvtfV | O::NeonScvtfV | O::NeonDupScalarD => {
            EmittableNeedsProof
        }
        // NEON FP fused multiply-accumulate BY ELEMENT (FMLA Vd.T, Vn.T,
        // Vm.Ts[lane]) emitted by the elementwise-FP vectorizer (neon_fmap) for
        // the `y[i] += da*x[i]` shape — the scalar invariant `da` kept in a lane
        // (no DUP broadcast). CREDITED via the FAITHFUL per-(arrangement, dest
        // lane, selector) obligations (neon_lowering_proofs::all_neon_fmla_lane_proofs
        // — {.4S selector 0..3 x dest 0..3} + {.2D selector 0..1 x dest 0..1} = 20),
        // gate-bound through `aarch64_width_polymorphic_proofs` so the complete
        // 20-row selector-by-destination matrix must discharge. Semantics are the
        // SINGLE-rounding `fp.fma` (the scalar FMADD credit, lifted per lane) with
        // the multiplier BROADCAST from lane `selector` of Vm — a wrong-lane
        // selector, FMLA<->FMLS polarity, or accumulator miswire REFUTES (see
        // `neon_fmla_lane_wrong_encoding_controls`). HONESTY as the FP lane ops:
        // both sides share the SMT FP node, certifying LANE/OP/WIDTH plumbing.
        O::NeonFmlaLaneV => EmittableNeedsProof,
        // NEON `f32 -> f64` widening convert (FCVTL/FCVTL2) emitted by the FP
        // array-reduction vectorizer (neon_farray) for the widening dot
        // (`sum += (double)a_f32[i]*(double)b_f32[i]`). CREDITED via the FAITHFUL
        // per-lane obligations (neon_lowering_proofs::all_neon_fcvtl_proofs — 4:
        // {FCVTL low half, FCVTL2 high half} x .2D 2 lanes), gate-bound through
        // `aarch64_width_polymorphic_proofs` so BOTH `.2D` lanes must discharge.
        // Widening `f32 -> f64` is EXACT (fpext, no rounding); the SOURCE slices
        // the source f32 lane DIRECTLY from the raw D-halves and widens, the
        // MACHINE is the real `encode_neon_fcvtl_vec` over the reassembled
        // `Concat(hi, lo)`. STRUCTURALLY DISTINCT, so the wrong-HALF (FCVTL as
        // FCVTL2) and wrong-lane controls REFUTE (see
        // `neon_fcvtl_wrong_encoding_controls`).
        O::NeonFcvtlV | O::NeonFcvtl2V => EmittableNeedsProof,
        // NEON lane -> GPR extract (UMOV Wd/Xd, Vn.<T>[lane]) — the single op
        // every NEON lane->scalar extract lowers through: the reduction drains
        // (neon_find/array/reduce/fmap/minmax/predsum + the vectorize/isel
        // ordered-sub reducers) at `.S`/`.D`, AND the
        // V{16I8,8I16,4I32,2I64}ExtractLane isel at `.B`/`.H`/`.S`/`.D`. CREDITED
        // via the FAITHFUL per-(element-size, lane) obligations
        // (neon_lowering_proofs::all_neon_umov_proofs — 30: `.16B` 16 lanes,
        // `.8H` 8, `.4S` 4, `.2D` 2), gate-bound through
        // `aarch64_width_polymorphic_proofs` so EVERY emitted (size, lane) must
        // discharge (a single-lane or wrong-size miswiring cannot hide). UMOV
        // ZERO-EXTENDS the selected lane into the GPR (`.B`/`.H`/`.S` -> 32-bit
        // `Wd`; `.D` -> 64-bit `Xd`). The SOURCE slices each lane DIRECTLY from
        // the raw D-halves and zero-extends; the MACHINE is the real
        // `encode_neon_umov_general` over the reassembled `Concat(hi, lo)`.
        // STRUCTURALLY DISTINCT, so wrong-lane and wrong-size (the element-size
        // operand) REFUTE (see `neon_umov_wrong_encoding_controls`). Every lane
        // is a COMPILE-TIME-CONSTANT immediate (no dynamic lane exists), so the
        // whole matrix is provable — nothing left allowlisted. Unlike the FP lane
        // ops, BOTH sides are PURE QF_BV (no shared opaque node): a COMPLETE
        // faithful proof of the extract + zero-extend.
        O::NeonUmovGen => EmittableNeedsProof,
        // Emitted NEON horizontal-reduce and permute ops still lack faithful
        // obligations and stay RED — NOT faked:
        //   * Horizontal reduces (NeonUmaxv UMAXV, NeonAddpScalar ADDP): a
        //     CROSS-lane fold to a scalar; `encode_neon_umaxv_4s` models UMAXV but
        //     no independent faithful obligation is registered, and ADDP has no
        //     encoder at all.
        //   * Permutes (NeonDupGen/DupElem broadcast, NeonInsGen insert, NeonMovi
        //     byte-broadcast const, NeonRev32V lane-group reverse): DUP/INS/MOVI
        //     have encoders but their faithful obligations would be a
        //     broadcast/insert that collapses to a degenerate same-shape X==X in
        //     this model; REV32 keeps only the byte-form encoders and its
        //     permutation semantics are not yet expressed. Left RED pending a
        //     genuine permute obligation. (NeonUmovGen, the
        //     lane->scalar extract, is NO LONGER here — it is EMITTABLE and
        //     COVERED via all_neon_umov_proofs' faithful per-(size,lane) matrix;
        //     NeonRev64V is NO LONGER here either — the butterfly vectorizer
        //     emits its `.4S` pair-swap form, now EMITTABLE and COVERED via the
        //     faithful proof_neon_rev64v_4s obligation. NeonRbitV is NO LONGER
        //     here either — the neon-bitrev vectorizer emits its `.16B` per-byte
        //     bit reversal, now EMITTABLE and COVERED via the faithful
        //     proof_neon_rbitv_16b obligation.)
        //   * Post-index load/store (NeonLd1Post/St1Post): the SHARED whole-backend
        //     unfaithful-load debt — the SMT model has no faithful INDEPENDENT
        //     dereference encoder (the entire Ldr*/Str* family carries this; see
        //     aarch64_jumptable_proofs.rs / the integer Ldr*/Str* RED rows above).
        //     This is NOT a NEON-specific gap: the NEON vectorization's memory
        //     safety is established by the differential + guard-page OOB evidence,
        //     not by a per-instruction memory-value proof.
        O::NeonDupGen
        | O::NeonDupElem
        | O::NeonInsGen
        | O::NeonMovi
        | O::NeonUmaxv
        | O::NeonRev32V => EmittableNeedsProof,
        O::NeonAddpScalar => FailClosedAllowlisted {
            reason: "NEON horizontal-reduce / permute op — fail-closed pending a faithful \
                     cross-lane (reduce) or permute obligation; the same-shape NeonLowering \
                     proofs are degenerate X==X and the horizontal/permute semantics are not \
                     yet independently modeled",
        },
        O::NeonLd1Post | O::NeonSt1Post | O::NeonLdpQPost | O::NeonStpQPost => {
            EmittableNeedsProof
        }
    }
}

/// Classify an x86-64 opcode. WILDCARD-FREE on purpose — see module note.
pub fn classify_x86(opcode: X86Opcode) -> OpcodeClass {
    use OpcodeClass::*;
    use X86Opcode as O;

    // Pseudo forms (mirror `X86Opcode::is_pseudo`). The encoder returns
    // `UnsupportedOpcode` for the V*MaskExtract / V128BoolSelect pipeline
    // pseudos — fail-closed, allowlisted below rather than treated as no-op.
    match opcode {
        // ---- Pseudo / trap forms ----
        O::Phi | O::StackAlloc | O::Nop => PseudoOrTrap,
        O::Ud2 => PseudoOrTrap, // real trap instruction, no value proof

        // ---- Emittable, MUST be proven (mapped by X86FunctionVerifier) ----
        O::AddRR | O::AddRI | O::AddRM | O::Inc => EmittableNeedsProof,
        O::SubRR | O::SubRI | O::SubRM | O::Dec => EmittableNeedsProof,
        O::ImulRR | O::ImulRM | O::ImulRMSib | O::ImulRRI => EmittableNeedsProof,
        O::Neg => EmittableNeedsProof,
        O::Idiv | O::Div => EmittableNeedsProof,
        O::AndRR | O::AndRI | O::OrRR | O::OrRI | O::XorRR | O::XorRI | O::Not => {
            EmittableNeedsProof
        }
        O::ShlRR | O::ShlRI | O::ShrRR | O::ShrRI | O::SarRR | O::SarRI | O::RolRI => {
            EmittableNeedsProof
        }
        O::CmpRR | O::CmpRI | O::CmpRI8 | O::CmpRM => EmittableNeedsProof,
        O::TestRR | O::TestRI | O::TestRM => EmittableNeedsProof,
        O::Setcc | O::Cmovcc | O::Cmovcc32 => EmittableNeedsProof,
        // Indirect call targets: correctness is the CFG/relocation edge, not a
        // per-instruction value equivalence (the only available "proof" would be
        // the target==target tautology, which proves nothing). Verifier reports
        // Unverified (opcode_to_proof_query => None); the gate must classify them
        // fail-closed-allowlisted, mirroring AArch64 Blr. A PLT32 inventory row
        // is not a call proof and separately blocks production certification.
        O::CallR | O::CallM => FailClosedAllowlisted {
            reason: "indirect branch/call target — covered by Branch/CallLowering/relocation proofs (per-instruction value-equivalence is Unverified, not a tautology); mirrors AArch64 Blr",
        },
        // HONESTY (task #61): direct CALL and RET map only to the degenerate ledger
        // entries "x86_64: CALL branches to target" / "x86_64: RET branches to
        // stack return address" (X==X — target==target / addr==addr, no
        // independent machine model). They prove nothing, so these opcodes are NOT
        // covered. The relocation inventory names PLT32 but does not authorize
        // it; coverage is NOT claimed here pending a faithful control-edge
        // obligation (and separate Certified relocation authority).
        O::Call | O::Ret => FailClosedAllowlisted {
            reason: "direct call / return target — its only mapped proof was a KNOWN_DEGENERATE \
                     X==X (CALL/RET branches to target) that proved nothing and was RETRACTED \
                     (#62); coverage NOT claimed. Faithful control-edge and Certified relocation \
                     obligations remain pending.",
        },
        O::Addsd | O::Subsd | O::Mulsd | O::Divsd => EmittableNeedsProof,
        O::Addss | O::Subss | O::Mulss | O::Divss => EmittableNeedsProof,
        O::Addps | O::Subps | O::Mulps | O::Divps => EmittableNeedsProof,
        O::Addpd | O::Subpd | O::Mulpd | O::Divpd => EmittableNeedsProof,
        O::Cvtsi2sd
        | O::Cvtsi2ss
        | O::Cvttsd2si
        | O::Cvttss2si
        | O::Cvtsd2si
        | O::Cvtss2si
        | O::Cvtsd2ss
        | O::Cvtss2sd => EmittableNeedsProof,
        O::Popcnt | O::Tzcnt | O::Lzcnt | O::Bsf | O::Bsr => EmittableNeedsProof,
        O::Movzx | O::MovzxW | O::MovsxB | O::MovsxW | O::Movsx => EmittableNeedsProof,
        // HONESTY (task #61): MovRR / MovRR32 (reg-reg copy) bind the GENUINE
        // Copy_I64 / Copy_I32 bit-identity proofs (on GENUINE_IDENTITY_ALLOWLIST) —
        // they stay EmittableNeedsProof and report COVERED. MovRI (materialize an
        // immediate constant) maps ONLY to the degenerate "x86_64: MOV r,imm
        // materializes constant" ledger entry (X==X — const==const, no independent
        // model); it proves nothing, so it remains an explicit RED denominator
        // row rather than being hidden as an exclusion.
        O::MovRR | O::MovRR32 | O::MovRI => EmittableNeedsProof,
        O::MovdToXmm | O::MovdFromXmm | O::MovqToXmm | O::MovqFromXmm => EmittableNeedsProof,
        O::AtomicRmwCasLoop | O::AtomicRmwCasLoop8 | O::AtomicRmwCasLoop16 => EmittableNeedsProof,

        // ---- Fail-closed / covered-elsewhere allowlist (with reasons) ----
        //
        // (a) Encoder returns UnsupportedOpcode — no compiled program contains
        //     these; the x86 pipeline expands them before encoding.
        O::V4I32MaskExtract
        | O::V16I8MaskExtract
        | O::V8I16MaskExtract
        | O::V2I64MaskExtract
        | O::V128BoolSelect => FailClosedAllowlisted {
            reason: "encoder UnsupportedOpcode — vector pseudo expanded before emission",
        },

        // Proof-only exact bounds-check carrier (Sentinel S5): the encoder
        // returns UnsupportedOpcode, and the x86 pipeline either deletes it under
        // kernel authorization or expands it to CMP+Jcc(AE)+UD2 before emission.
        // No compiled program contains this opcode.
        O::TrapBoundsCheckExact => FailClosedAllowlisted {
            reason: "encoder UnsupportedOpcode — proof-only bounds carrier expanded/deleted before emission",
        },

        // Proof-only null-check carrier (Sentinel S5): the encoder returns
        // UnsupportedOpcode, and the x86 pipeline either deletes it under kernel
        // authorization or expands it to TEST+Jcc(E)+UD2 before emission. No
        // compiled program contains this opcode.
        O::TrapNullIfZeroExact => FailClosedAllowlisted {
            reason: "encoder UnsupportedOpcode — proof-only null carrier expanded/deleted before emission",
        },

        // Proof-only div-by-zero-check carrier (Sentinel S5): the encoder returns
        // UnsupportedOpcode, and the x86 pipeline either deletes it under kernel
        // authorization or expands it to TEST+Jcc(E)+UD2 before emission. No
        // compiled program contains this opcode.
        O::TrapDivZeroExact => FailClosedAllowlisted {
            reason: "encoder UnsupportedOpcode — proof-only div-zero carrier expanded/deleted before emission",
        },

        // Proof-only shift-range-check carrier (Sentinel S5): the encoder returns
        // UnsupportedOpcode, and the x86 pipeline either deletes it under kernel
        // authorization or expands it to CMP+Jcc(AE)+UD2 before emission. No
        // compiled program contains this opcode.
        O::TrapShiftRangeExact => FailClosedAllowlisted {
            reason: "encoder UnsupportedOpcode — proof-only shift-range carrier expanded/deleted before emission",
        },

        // Jcc maps to the CMP+Jcc `Icmp_*` composition proofs (as Setcc does) —
        // genuine, stays EmittableNeedsProof (reports COVERED).
        O::Jcc => EmittableNeedsProof,
        // HONESTY (task #61): JMP maps only to the degenerate "x86_64: JMP branches
        // to target" ledger entry (X==X — target==target, no independent machine
        // model); it proves nothing, so it is NOT covered. The unconditional CFG
        // edge is covered by the Branch/relocation family; coverage NOT claimed
        // here pending a faithful control-edge obligation. (Mirror of CALL.)
        O::Jmp => FailClosedAllowlisted {
            reason: "JMP (unconditional branch target) — its only mapped proof was the \
                     KNOWN_DEGENERATE X==X 'x86_64: JMP branches to target' that proved nothing \
                     and was RETRACTED (#62); coverage NOT claimed. The CFG edge is covered by \
                     the Branch/relocation family pending a faithful control-edge obligation.",
        },
        // JMP r64 — indirect near jump, emitted ONLY as a jump-table dispatch.
        // Its transfer target is `base + table[idx]`, computed by the preceding
        // LeaRip (table base, PROVEN RIP-relative EA) + MovRMSib (signed 64-bit
        // delta entry, scale=8) + AddRR; the case->target dense mapping is proven
        // ARCH-GENERICALLY
        // by the #62 gate `check_jump_table_preserved`. The indirect transfer
        // itself has no non-degenerate per-instruction value proof (target==target
        // is the retracted X==X class), so it is FailClosedAllowlisted covered-
        // elsewhere, mirroring CallR/CallM (AArch64 Br/Blr precedent).
        O::JmpR => FailClosedAllowlisted {
            reason: "JMP r64 (indirect jump-table dispatch) — transfer target is the PROVEN \
                     address chain LeaRip+MovRMSib(scale=8)+AddRR over a #62-verified dense table \
                     (check_jump_table_preserved); the indirect branch itself has no non-\
                     degenerate value proof (target==target = retracted X==X). Covered-elsewhere, \
                     mirrors CallR/CallM and AArch64 Br.",
        },

        // (b) Stack/ABI/sign-extend-accumulator/flag-carry forms: covered by
        //     frame/call-lowering proofs or pending i128 carry proofs (#67-class).
        O::Push | O::Pop => FailClosedAllowlisted {
            reason: "stack manipulation — covered by FrameLayout/CallLowering proofs",
        },
        O::Cdq | O::Cqo => FailClosedAllowlisted {
            reason: "sign-extend accumulator for IDIV — part of proven Sdiv sequence, not value-mapped",
        },
        // i128 carry-chain high limb (ADC/SBB). Now PROVEN: each binds to a
        // faithful 65-bit carry/borrow proof whose trust-ir spec is the high 64
        // bits of the full 128-bit sum/difference (x86_64_lowering_proofs
        // `proof_x86_adc_i128_hi` / `proof_x86_sbb_i128_hi`), mapped by
        // `opcode_to_proof_query` (AdcRR -> "Iadd_I128 hi -> ADC", SbbRR ->
        // "Isub_I128 hi -> SBB"). The low limb is the ordinary AddRR/SubRR.
        O::AdcRR | O::SbbRR => EmittableNeedsProof,
        // One-operand widening MUL (RDX:RAX = RAX * src), the unsigned
        // widening/overflow multiply for CheckedUmul. Width-polymorphic
        // (Gpr32/Gpr64 source); the per-instruction verifier binds the
        // width-correct low-half (value) proof via `mul_to_proof_query`. The
        // gate (see `x86_width_polymorphic_proofs`) requires BOTH the low-half
        // (RAX == wrapping mul) AND high-half (RDX != 0 == overflow) proofs at
        // i32 AND i64 to exist and discharge.
        O::Mul => EmittableNeedsProof,

        // Plain LEA (base+disp32) and SIB LEA (base+index*scale+disp32) are now
        // RECONSTRUCTED from the real operands: the machine side is rebuilt from
        // the real opcode's effective-address encoder (`encode_lea_base_disp` /
        // `encode_lea_base_index_scale_disp`) over fresh symbolic base/index, and
        // the source side is the same `base [+ index*scale] + disp` arithmetic.
        // A wrong scale or disp in the machine encoder DIVERGES from the source
        // (proved by the inject-wrong-scale/disp refutation tests). Credited
        // COVERED via reconstruction (`x86_reconstruction_discharges_valid` runs
        // before any DB lookup); the StackSlot base resolves to a 64-bit frame
        // pointer + slot at frame lowering and is modeled as the same fresh base
        // symbol. The retracted degenerate X==X EA "proofs" are no longer used.
        O::Lea | O::LeaSib => EmittableNeedsProof,
        // RIP-relative symbol-address materialization. Both opcodes only ever
        // carry a `Symbol(name)` operand (x86_64_isel select_global_ref /
        // select_extern_ref), so the opcode alone fixes the relocation
        // provenance, and the per-instruction verifier binds a registered proof
        // that composes the RIP-relative effective-address computation with the
        // proven SIGNED (LeaRip, in-module S + A) / GOT_LOAD (MovRipRel, GOT
        // slot G + A) relocation displacements (macho_data_reloc_proofs +
        // x86_64_lowering_proofs::x86_64_riprel_symbol_proofs).
        O::LeaRip | O::MovRipRel => EmittableNeedsProof,
        // MOV r64, [RIP+disp32] with a Mach-O `@TLVP` thread-local descriptor
        // reference (byte-identical encoding to MovRipRel; only the relocation
        // kind differs — X86_64_RELOC_TLV instead of GOT_LOAD). The EA
        // computation is the SAME RIP-relative reconstruction family as
        // MovRipRel; the TLV displacement's link-time semantics (descriptor
        // address; ld64 relaxes the load to LEA for image-local TLVs) is
        // relocation provenance, not value computation. FOLLOW-UP (before
        // flip-default-ON): extend the riprel symbol proofs with a TLV
        // displacement composition mirroring the GOT_LOAD one.
        O::MovRipRelTlv => FailClosedAllowlisted {
            reason: "MOV r64,[RIP+disp32] @TLVP descriptor load (x86-64 Darwin TLS) —                      same RIP-relative EA reconstruction family as the proven MovRipRel;                      the TLV relocation displacement needs its own composition proof                      (GOT_LOAD analogue) before default-ON.",
        },
        // (b) FP constant-pool RIP-relative loads (#65): the MovssRipRel /
        //     MovsdRipRel proofs reconstruct `RIP_next + disp32 == C` (the
        //     constant-pool entry address), with the opaque load of the f32/f64
        //     immediate covered by the Load_F* memory proofs — exactly the
        //     two-part shape of the symbol-address MovRipRel proof. Now proven.
        O::MovssRipRel | O::MovsdRipRel => EmittableNeedsProof,
        // Scaled-index 64-bit memory MOV `[base+index*scale+disp]` (SIB). Now
        // PROVEN: the shared `x86_reconstruct_effective_address` reconstructs the
        // `SibMemAddr` EA on both the trust_ir and INDEPENDENT machine encoders,
        // so MovRMSib/MovMRSib route to the same Load_I64/Store_I64 effective-
        // address memory proofs as MovRM/MovMR — a wrong base/index/scale/disp
        // REFUTES. Mapped by `opcode_to_proof_query` (MemLoad/MemStore, 64-bit).
        O::MovRMSib | O::MovMRSib => EmittableNeedsProof,
        // 32-bit SIB siblings (X10): same shared EA reconstruction at 32-bit
        // load/store width as MovRM32/MovMR32.
        O::MovRM32Sib | O::MovMR32Sib => EmittableNeedsProof,
        // 8-bit SIB siblings: the SAME shared EA reconstruction at 8-bit
        // load/store width as MovRM8/MovMR8. Closes the gap that kept EVERY
        // byte-indexed access (`&[u8]`, `Vec<u8>`, `[u8; N]`) out of indexed
        // addressing, since the SIB opcode set was 64/32-bit and float only.
        // Nothing new is trusted: a wrong base/index/scale/disp REFUTES through
        // the same `x86_reconstruct_effective_address` half, and the access
        // WIDTH is fixed by the opcode (8) exactly as it is for MovRM8/MovMR8.
        O::MovRM8Sib | O::MovMR8Sib => EmittableNeedsProof,
        // Scalar-FP SIB loads: the COMPOSITION of the two proofs directly above.
        // The effective address is reconstructed by the same shared
        // `x86_reconstruct_effective_address` that proves MovRMSib (SOURCE = the
        // trust_ir address chain, MACHINE = the INDEPENDENT x86 encoder), and the
        // loaded value is the same Load_F64/Load_F32 memory proof that already
        // covers MovsdRM/MovssRM. Nothing new is trusted: a wrong
        // base/index/scale/disp REFUTES via the EA half, a wrong access width or
        // lane REFUTES via the FP-load half. Mapped by `opcode_to_proof_query`
        // (MemLoad, width fixed by the opcode: 8 bytes for sd, 4 for ss).
        O::MovsdRMSib | O::MovssRMSib => EmittableNeedsProof,
        // MOVSXD r64, [base+index*4] (SIB) — sign-extending 32-bit load. This was
        // introduced for the original 4-byte jump-table design, but the active
        // path deliberately uses 8-byte deltas via the already-proven MovRMSib.
        // If another path emits MovsxdRMSib, the scaled effective
        // address `base+index*4` is the SAME `x86_reconstruct_effective_address`
        // family as MovRMSib; the loaded value is a COMPILER-EMITTED table entry
        // whose bytes (target_off - table_base) and sign-extension are covered by
        // the #62 dense-mapping gate + the vs-LLVM/vs-BST differential fuzz.
        // FOLLOW-UP (before flip-default-ON): upgrade to EmittableNeedsProof with a
        // genuine scaled-sign-extending-load proof mirroring AArch64
        // `proof_ldrsw_ro_scaled_addr` (dst == sext32(mem32[base+index*4])).
        O::MovsxdRMSib => FailClosedAllowlisted {
            reason: "MOVSXD r64,[base+index*4] (currently not emitted by the active 8-byte \
                     jump-table path) — scaled EA is the \
                     MovRMSib reconstruction family; the loaded value is a compiler-emitted \
                     #62-verified table entry, its sign-extension + bytes covered by the \
                     jump-table mapping gate + differential fuzz. Upgrade to a genuine \
                     scaled-sext-load proof (aarch64 LdrswRO analogue) before default-ON.",
        },

        // Plain GPR loads/stores map to the Load_/Store_ effective-address
        // memory proofs at every access width (atomic-origin moves are routed
        // to the AtomicLoad/AtomicStore proofs first).
        O::MovRM8
        | O::MovRM16
        | O::MovRM32
        | O::MovRM
        | O::MovMR8
        | O::MovMR16
        | O::MovMR32
        | O::MovMR
        // Volatile GPR loads/stores are byte-identical to the plain forms but
        // remain RED until one obligation covers both the value/effect and the
        // optimizer observation/ordering boundary.
        | O::VolatileMovRM8
        | O::VolatileMovRM16
        | O::VolatileMovRM32
        | O::VolatileMovRM
        | O::VolatileMovMR8
        | O::VolatileMovMR16
        | O::VolatileMovMR32
        | O::VolatileMovMR => EmittableNeedsProof,
        // (#65) Scalar-FP MOVSS/MOVSD reg-reg copy / load / store: now PROVEN.
        //   reg-reg copy => scalar bit-IDENTITY (Copy_F32/F64);
        //   load        => Load_F32/F64 effective-address memory proof;
        //   store        => Store_F32/F64 effective-address memory proof.
        // Mapped by `opcode_to_proof_query` (Movss/Movsd width is opcode-fixed).
        O::MovsdRR | O::MovsdRM | O::MovsdMR | O::MovssRR | O::MovssRM | O::MovssMR
        // Volatile FP scalar loads/stores are likewise denominator-bearing RED
        // until both memory semantics and the volatile boundary are covered.
        | O::VolatileMovssRM | O::VolatileMovssMR | O::VolatileMovsdRM | O::VolatileMovsdMR => {
            EmittableNeedsProof
        }
        // 128-bit XMM memory MOVES (MOVDQU unaligned / MOVDQA aligned, RM load +
        // MR store): the bridge emits these for whole-XMM spill/reload of a 128-bit
        // vector value. GENUINELY RECONSTRUCTED (not X==X) as TWO 64-bit halves at
        // effective addresses `ea` (low) and `ea+8` (high), little-endian, via the
        // PROVEN scalar effective-address machinery (`x86_reconstruct_effective_
        // address`): SOURCE addresses = trust_ir `encode_trust_ir_binop`, MACHINE
        // addresses = INDEPENDENT x86 `encode_lea_*`. A wrong base/index/scale/disp
        // (EA), a swapped half, a wrong half offset, or a wrong access width reads
        // different bytes ⇒ REFUTE. MOVDQA carries the HONEST `ea % 16 == 0`
        // precondition (SSE MOVDQA #GP-faults on a non-16-aligned address); MOVDQU
        // does not. Credited COVERED via reconstruction in `audit_x86` before any
        // DB lookup (see `reconstruct_x86_v128_mem_{load,store}` +
        // tests/reconstruction_x86.rs packed-move positives/refutations). The
        // reg-reg form MOVDQA{RR} stays separate explicit copy debt.
        O::MovdquRM | O::MovdquMR | O::MovdqaRM | O::MovdqaMR
        // Volatile V128 loads/stores require the same two-facet coverage.
        | O::VolatileMovdquRM | O::VolatileMovdquMR | O::VolatileMovdqaRM
        | O::VolatileMovdqaMR => EmittableNeedsProof,

        // Scalar square root SQRTSD/SQRTSS — bound to the Fsqrt_F64/F32 lowering
        // proofs (fp.sqrt), emitted via Opcode::Fsqrt for the sqrt intrinsic.
        // (ANDPS/ANDPD likewise moved to the proven set — see V128 Band above.)
        O::Sqrtsd | O::Sqrtss => EmittableNeedsProof,
        // Scalar round-to-integral ROUNDSD/ROUNDSS (SSE4.1) — emitted via
        // Opcode::Ffloor/Fceil/Ftrunc for the floorf*/ceilf*/truncf* intrinsics.
        // Mode-polymorphic: the gate requires all three rounding modes' proofs
        // (see `x86_width_polymorphic_proofs`); the verifier binds the exact
        // (width, mode) proof per instruction from the imm8.
        O::Roundsd | O::Roundss => EmittableNeedsProof,
        // Scalar min/max MINSD/MAXSD/MINSS/MAXSS + the NaN-fixup compare
        // CMPSD/CMPSS — emitted via Opcode::Fmin/Fmax for the Rust
        // f{32,64}::min/max intrinsics. Each binds (opcode_to_proof_query) to a
        // faithful per-instruction proof that models the EXACT hardware
        // semantics (MINSD = src-on-unordered/equal; CMPSD imm8=3 = isNaN mask)
        // — NOT IEEE fp.min, which MINSD does not implement. The surrounding
        // XOR-blend NaN fixup reuses the already-proven PXOR/PAND opcodes (like
        // the fneg/fabs sign idioms: the new opcode is proven, the bit-blend
        // structure is built from proven primitives).
        O::Minsd | O::Maxsd | O::Minss | O::Maxss | O::Cmpsd | O::Cmpss => EmittableNeedsProof,
        O::Bswap => FailClosedAllowlisted {
            reason: "BSWAP is encoder-supported but never selected by the current lowerer; \
                     not in the emitted set",
        },
        // PSADBW is a HORIZONTAL reduction (`Σ |a[i]-b[i]|` → two u64 lanes), now
        // PROVEN: it maps (via `x86_opcode_to_source_op`) to the
        // `X86SourceOp::PsadbwByteSad` RECONSTRUCTION, whose MACHINE side
        // (`encode_psadbw`, the real horizontal SAD) is verified equal to the
        // INDEPENDENT SOURCE spec (`encode_trust_ir_byte_sad`). Reconstructed
        // provenance credits it non-degenerate (a wrong emitted opcode — e.g.
        // lane-wise PADDB — reconstructs to a different machine expression and
        // REFUTES), the same rule as the lane-wise PADD*/PSUB* family and the
        // bit-count reductions. Emitted by the byte-sum vectorizer tier
        // (`recognize_byte_sum_reduction_loop`).
        O::Psadbw => EmittableNeedsProof,
        // BT r,imm8 sets CF := bit#imm of r. The x86 AND/CMP/Jcc→BT/Jcc peephole
        // emits it at Gpr32/Gpr64 with a static bit index k; the per-instruction
        // verifier binds the EXACT `BtRI_I{32,64}#k` CF proof via
        // `bt_to_proof_query`. The gate has only the opcode, so it is treated as
        // width-polymorphic (see `x86_width_polymorphic_proofs`) and demands a
        // representative i32 AND i64 BT-CF proof both exist and discharge —
        // neither width can ship without a proof.
        O::BtRI => EmittableNeedsProof,
        // (#65) SSE scalar FP compare: now PROVEN. UCOMISS (F32) and UCOMISD
        // (F64) are DISTINCT, single-width opcodes — each maps via
        // opcode_to_proof_query to its width-correct representative Fcmp proof
        // (Fcmp_Eq_F32/F64), a faithful UCOMIS flag-compare cert that mirrors
        // bare integer CmpRR -> Icmp_. A UCOMIS inside a recognized UCOMIS+SETcc
        // sequence gets the exact condition Fcmp proof via the sequence
        // recognizer first. Not width-polymorphic (each opcode is one width).
        O::Ucomisd | O::Ucomiss => EmittableNeedsProof,

        // (a) Bare atomic EXCHANGE opcode: NOT EMITTED by the lowerer (so never
        //     proof-covered — genuinely fail-closed, not "covered elsewhere").
        //     The atomic-EXCHANGE role is served by the separate
        //     `AtomicRmwCasLoop*` pseudo (classified EmittableNeedsProof above),
        //     which binds the AtomicRmwCasLoop_Xchg_I* certs; the bare `Xchg`
        //     fast path was deleted. If it reaches the gate it means an unproven
        //     path emitted it -> fail closed, never a silent pass.
        O::Xchg => FailClosedAllowlisted {
            reason: "bare atomic exchange opcode not emitted by the lowerer \
                     (atomic exchange goes through the proven AtomicRmwCasLoop pseudo) \
                     — fail closed",
        },
        // (a2) LOCK CMPXCHG (compare_exchange) [slice 4]. EMITTED for
        //      AtomicT::compare_exchange{,_weak} at i32/i64 and PROVEN: it binds
        //      GENUINE conditional-data-flow proofs via instruction_to_proof_query
        //      (Cmpxchg_I{32,64} -> returns-old + conditional-store + success-flag),
        //      real SMT obligations over symbolic (mem, expected, desired) state
        //      that model the equality-gated store and dual (old-value, ZF) output
        //      — NOT a #62 identity/tautology (the negative controls REFUTE an
        //      unconditional store, a returns-desired variant, and a backwards
        //      flag). That single-thread conditional semantics is what is
        //      SMT-proven; the cross-thread LOCK serialization / memory ordering
        //      CMPXCHG also provides is the same Intel-SDM architectural axiom the
        //      atomic load/store/RMW and MFENCE proofs already rest on (two-tier
        //      honesty, same footing as slices 1-3). Narrow i8/i16, weak spurious
        //      failure, and invalid failure orderings stay fail-closed upstream.
        O::Cmpxchg => EmittableNeedsProof,
        // Narrow i8/i16 LOCK CMPXCHG forms are actively selected for
        // AtomicU8/U16 compare_exchange. They stay in the denominator; the
        // deferral table records the missing width-complete facets.
        O::Cmpxchg8 | O::Cmpxchg16 => EmittableNeedsProof,
        // (b) MFENCE (SeqCst fence, slice 3). MFENCE is a genuine NO-OP on
        //     single-thread architectural data state: it writes no register and
        //     no memory byte (`encode_mfence` is the (reg, mem) IDENTITY). Its
        //     only faithful per-instruction value-equivalence obligation is
        //     therefore STRUCTURALLY X==X. Under the coverage gate's STRICT
        //     non-degeneracy policy (task #61), an X==X proof contributes ZERO to
        //     coverage regardless of allowlist — so this opcode must NOT be
        //     `EmittableNeedsProof` (that would demand a genuine non-X==X proof
        //     that cannot exist for a no-op, and leaves the gate RED). It is
        //     allowlisted with coverage NOT claimed, exactly like RET / CALL /
        //     the integer loads whose only value-proof was a retracted X==X.
        //     SOUNDNESS is NOT weakened: the single-thread identity IS registered
        //     and discharges, and is witnessed non-vacuous by two REFUTING
        //     negative controls (a fence clobbering a register / a memory byte
        //     REFUTES) under `proof_gate_strict`; the cross-thread ORDERING
        //     guarantee is the Intel-SDM axiom (8.2.5), same epistemic footing as
        //     the LOCK-serialization / MOV single-copy-atomicity axioms the atomic
        //     load/store proofs rest on. Acquire/Release/AcqRel fences emit ZERO
        //     instructions on x86 TSO and never reach the gate. (Slice 3 wrongly
        //     marked this EmittableNeedsProof -> emittable-but-uncoverable X==X ->
        //     a failing clean-tree gate; this is the correct classification.)
        O::Mfence => FailClosedAllowlisted {
            reason: "MFENCE (SeqCst fence) is a no-op on single-thread data state \
                     (writes no register, no memory) — its only faithful value proof \
                     is structurally X==X (the identity), which the strict gate credits \
                     ZERO; coverage NOT claimed. The identity is registered + witnessed \
                     non-vacuous by two refuting negative controls (proof_gate_strict); \
                     cross-thread ordering is the Intel-SDM axiom (8.2.5). Same \
                     disposition as RET/CALL.",
        },
        O::NopMulti => FailClosedAllowlisted {
            reason: "multi-byte NOP — alignment padding, semantically identity",
        },

        // PXOR is folded into the lane-wise packed bitwise arm below: it is emitted
        // in the SCALAR FP-NEG sign idiom (select_fneg: `Pxor dst,src,sign_mask`
        // flips the IEEE sign bit; x86-64 has no scalar XORPS/XORPD), as XMM zeroing,
        // and on the vector lane. The full-width XOR reconstruction (XOR being
        // bitwise) certifies the scalar low-lane sign-flip and the zeroing form alike.

        // LANE-WISE PACKED RECONSTRUCTION (v128 lane-vector semantics now built):
        // these packed ops are GENUINELY RECONSTRUCTED lane-wise by
        // `x86_reconstruction_discharges_valid` (runs before any DB lookup in
        // `audit_x86`). The MACHINE side is the real packed encoder
        // (`encode_paddd` = lane-wise bvadd over the 128-bit XMM at the element
        // width fixed by the opcode); the SOURCE side is the trust_ir scalar op
        // `map_lanes`-applied at the SAME arrangement (`encode_trust_ir_lanewise_*`).
        // A wrong lane op (PADD-for-PSUB), wrong lane WIDTH (i16x8 vs i32x4), or
        // wrong predicate (Eq-for-Sgt) REFUTES. They report [COVERED] via
        // reconstruction (not the degenerate static-DB X==X they previously matched).
        //   * Bitwise PAND/POR/PXOR/PANDN (+ ANDPS/ANDPD = FP-domain AND): full-
        //     width lane-independent bitwise. PANDN = (~a)&b (operand-complement
        //     asymmetry refutes).
        //   * PADD{B,W,D,Q}/PSUB{B,W,D,Q}/PMULLW/PMULLD: lane-exact add/sub/low-mul
        //     at the element width (B=i8x16, W=i16x8, D=i32x4, Q=i64x2).
        //   * PCMPEQ{B,W,D,Q}/PCMPGT{B,W,D,Q}: lane-exact Eq / signed-Gt mask at
        //     that element width (incl. the q-lane SSE4.1/4.2 forms).
        //   * PSLLD/PSRLD/PSRAD: uniform-IMMEDIATE dword shift (static-DB proof; the
        //     only form the lowerer emits — variable counts scalarize to GPR shifts).
        //   * PSLLQ/PSRLQ: uniform-IMMEDIATE qword shift (static-DB proof, the
        //     i64x2 siblings of PSLLD/PSRLD; the SSE2 vectorizer's packed 64-bit
        //     multiply compose is the only emitter and only uses the imm form).
        //   * PMULUDQ: even-lane 32->64 widening multiply, faithfully modeled as a
        //     SAME-WIDTH i64x2 lane op `lo32(a_q) * lo32(b_q)` (each qword lane's
        //     result depends only on that lane's low dword on both sides — the
        //     Intel-SDM even-dword indexing IS the qword lane's low half). The
        //     static-DB proof pits that spec against the INDEPENDENT machine-side
        //     even-dword-extract/zext/multiply encoding; a wrong lane pairing
        //     (odd dwords), a sign-extending model, or a low-half-only multiply
        //     REFUTES.
        //   * ADDPS/SUBPS/MULPS/DIVPS (4×f32), ADDPD/SUBPD/MULPD/DIVPD (2×f64):
        //     per-lane IEEE FP, one representative lane witnessing the full vector.
        O::Pand
        | O::Por
        | O::Pxor
        | O::Pandn
        | O::Paddb
        | O::Paddw
        | O::Paddd
        | O::Paddq
        | O::Psubb
        | O::Psubw
        | O::Psubd
        | O::Psubq
        | O::Pmullw
        | O::Pmulld
        | O::Pmuludq
        | O::Pcmpeqb
        | O::Pcmpeqw
        | O::Pcmpeqd
        | O::Pcmpeqq
        | O::Pcmpgtb
        | O::Pcmpgtw
        | O::Pcmpgtd
        | O::Pcmpgtq
        | O::Pslld
        | O::Psrld
        | O::Psrad
        | O::Psllq
        | O::Psrlq
        | O::Andpd
        | O::Andps => EmittableNeedsProof,

        // HONESTLY DEFERRED — no FAITHFUL lane-wise model exists for these, so they
        // are NOT credited (no fake proof). Each cannot be reconstructed as a clean
        // per-lane same-width scalar op:
        //   * PSHUFD needs the imm8 shuffle control (a permutation, not a per-lane
        //     value op);
        //   * PBLENDVB needs the implicit XMM0 mask register (a 3rd hidden operand);
        //   * PTEST sets RFLAGS (a cross-lane reduction, no value destination);
        //   * PMOVMSKB extracts per-lane sign bits to a GPR (cross-lane reduction);
        //   * PINSR*/PEXTR* would need imm8-indexed lane insert/extract modeling,
        //     but are not currently selected and remain excluded below;
        //   * PUNPCK*/PACKUSWB are interleave/saturating-narrow shuffles (lanes
        //     cross the boundary; not a per-lane same-width op);
        //   * MOVDQA{RR} is a 128-bit XMM register-register MOVE (structural, like
        //     the scalar copy family). NOTE: the MEMORY forms MOVDQA{RM,MR} (and
        //     MOVDQU{RM,MR}) were PROMOTED OUT of this deferred list — they are now
        //     GENUINELY RECONSTRUCTED as two 64-bit halves at ea/ea+8 (see the
        //     EmittableNeedsProof arm above). Do NOT re-add the RM/MR forms here.
        //     PMULUDQ was likewise PROMOTED OUT: its even-dword widening multiply
        //     is exactly a same-width i64x2 lane op on the qword lanes' low
        //     dwords, now backed by a refutable static-DB proof (see the
        //     EmittableNeedsProof arm above). Do NOT re-add it here.
        // The ten actively emitted forms stay IN the denominator as explicit RED
        // debt. PINSR*/PEXTR* are split out below because the current pipeline
        // never selects them.
        O::Pshufd
        | O::Pmovmskb
        | O::MovdqaRR
        | O::Punpckldq
        | O::Punpcklqdq
        | O::Ptest
        | O::Pblendvb
        | O::Punpcklbw
        | O::Punpckhbw
        | O::Packuswb => EmittableNeedsProof,
        O::Pinsrd | O::Pextrd | O::Pinsrq | O::Pextrq => FailClosedAllowlisted {
            reason: "PINSR*/PEXTR* are encoder-supported but never selected by the current \
                     lowering or pseudo-expansion pipeline; not in the emitted set",
        },
    }
}

/// Classify a RISC-V (RV64) opcode. WILDCARD-FREE on purpose — see module note.
///
/// HONESTY POLICY (see riscv_lowering_proofs.rs / riscv_semantics.rs headers):
///
///   * The clean dataflow ALU and direct comparison VALUE ops proven in stage 1
///     (ADD/SUB/MUL/AND/OR/XOR/SLL/SRL/SRA, the immediate shifts SLLI/SRLI, the
///     ADDI value role, and SLT/SLTU) are `EmittableNeedsProof` and credited by
///     operand reconstruction. LUI/XORI/SLTIU are also denominator-bearing but
///     remain explicit RED because the function verifier has no individual
///     reconstruction/binding for them.
///   * Pseudos (Phi/StackAlloc/Nop/TrapBoundsCheckExact) and the EBREAK trap are
///     `PseudoOrTrap` — no value-equivalence obligation (mirrors x86 UD2 / AArch64
///     BRK).
///   * Everything else is `FailClosedAllowlisted` with a TRUE reason:
///       - branches/jumps (Beq/Bne/Blt/Bge/Bltu/Bgeu/Jal/Jalr) — the CFG edge,
///         covered by branch/relocation families, not a per-instruction value proof;
///       - loads/stores (Lb/Lh/Lw/Ld/Lbu/Lhu/Lwu/Sb/Sh/Sw/Sd/Fld/Fsd) — memory
///         effective-address family, not a dataflow value proof;
///       - structural PC-relative address materialization (AUIPC);
///       - ALL dead, never-emitted variants: the W-forms (ADDW/.../REMUW), the
///         multiply-high family (MULH/MULHU/MULHSU), the divides/remainders
///         (DIV/DIVU/REM/REMU + W), and the entire FP-D extension. The encoder
///         path never selects these for pure-integer programs (the emitted set is
///         the 33 opcodes in the investigation note), so they fail closed as
///         never-selected rather than carry a fake proof.
///
/// SOUNDNESS: emitted value/effect uncertainty stays denominator-bearing RED.
/// Exclusion is reserved for structural/covered-elsewhere or demonstrated
/// never-selected forms.
pub fn classify_riscv(opcode: RiscVOpcode) -> OpcodeClass {
    use OpcodeClass::*;
    use RiscVOpcode as O;

    match opcode {
        // ---- Pseudo / trap forms (mirror `RiscVOpcode::is_pseudo` + EBREAK) ----
        O::Phi | O::StackAlloc | O::Nop | O::TrapBoundsCheckExact => PseudoOrTrap,
        // EBREAK is a real trap instruction (fixed encoding), not a pseudo, but
        // it carries no value-equivalence obligation — the RISC-V analogue of
        // x86 UD2 / AArch64 BRK.
        O::Ebreak => PseudoOrTrap,

        // ---- Reconstructed RISC-V dataflow surface (task #63, RISC-V) ----
        //
        // The 14 emittable ALU/shift/compare ops (ADD/SUB/MUL/AND/OR/XOR/SLL/SRL/
        // SRA, SLLI/SRLI, ADDI, SLT/SLTU) are now `EmittableNeedsProof` and CREDITED
        // via OPERAND RECONSTRUCTION (mirroring the proven AArch64 pattern). Their
        // static "riscv: …" proofs are degenerate X==X self-equalities that prove
        // NOTHING, so they were previously honestly allowlisted at 0% coverage.
        // `audit_riscv` now reconstructs the machine side FROM THE REAL EMITTED
        // OPCODE+OPERANDS (riscv_function_verifier::reconstruct_alu_obligation): a
        // wrong isel opcode (ADD-as-SUB, SLL-as-SRL ⇒ bvshl vs bvlshr) or wrong
        // operand wiring on a non-commutative op (SUB/shifts/SLT) REFUTES, so the
        // reconstruction-credit branch reporting COVERED is GENUINE — not the
        // vacuous identity. Shifts use the FAITHFUL hardware-amount-masked encoder
        // under a load-bearing `amount < width` precondition (#57). They are
        // EmittableNeedsProof and the reconstruction-credit branch in `audit_riscv`
        // reports COVERED.
        O::Add
        | O::Sub
        | O::Mul
        | O::And
        | O::Or
        | O::Xor
        | O::Sll
        | O::Srl
        | O::Sra
        | O::Slli
        | O::Srli
        | O::Addi
        | O::Slt
        | O::Sltu
        // LUI is emitted for constants; XORI and SLTIU are emitted comparison
        // idiom components. None has an individual reconstructed binding yet,
        // so the audit reports each as explicit DeferredUnfaithfulModel RED.
        | O::Lui
        | O::Xori
        | O::Sltiu => EmittableNeedsProof,

        // ---- Fail-closed / covered-elsewhere allowlist (with reasons) ----
        //
        // (b) Branches / jumps: correctness is the CFG edge, proven by the
        //     branch/CFG/relocation families, not a per-instruction value proof.
        O::Beq | O::Bne | O::Blt | O::Bge | O::Bltu | O::Bgeu | O::Jal | O::Jalr => {
            FailClosedAllowlisted {
                reason: "branch/jump target — CFG edge covered by branch+relocation family, \
                         not a per-instruction value proof",
            }
        }

        // (b) Loads / stores: covered by the memory effective-address family, not
        //     a dataflow value proof.
        O::Lb | O::Lh | O::Lw | O::Ld => FailClosedAllowlisted {
            reason: "integer load — covered by the memory/effective-address family, \
                     not a per-instruction dataflow value proof",
        },
        O::Lbu | O::Lhu | O::Lwu => FailClosedAllowlisted {
            reason: "zero-extending unsigned load is encoder-supported but never selected by the \
                     current lowerer; not in the emitted set",
        },
        O::Sb | O::Sh | O::Sw | O::Sd => FailClosedAllowlisted {
            reason: "integer store — covered by the memory/effective-address family, \
                     not a per-instruction dataflow value proof",
        },

        // AUIPC is PC-relative structural address materialization. LUI is
        // separately denominator-bearing because it actively materializes
        // ordinary constants too.
        O::Auipc => FailClosedAllowlisted {
            reason: "AUIPC PC-relative address materialization — covered by address/relocation \
                     provenance, not a standalone dataflow value proof",
        },

        // These immediate variants are encodable but have no producer in the
        // current lowering. XORI/SLTIU are split above because comparison idioms
        // do emit them.
        O::Andi | O::Ori | O::Slti | O::Srai => FailClosedAllowlisted {
            reason: "I-type immediate form is encoder-supported but never selected by the current \
                     lowerer; not in the emitted set",
        },

        // (b) DEAD never-emitted RV64I W-forms (32-bit ops on RV64). The
        //     pure-integer emitter selects the full-width 64-bit forms; the
        //     W-forms are encodable-but-never-selected. Fail-closed as
        //     never-selected (not in the emitted set).
        O::Addw
        | O::Subw
        | O::Sllw
        | O::Srlw
        | O::Sraw
        | O::Addiw
        | O::Slliw
        | O::Srliw
        | O::Sraiw => FailClosedAllowlisted {
            reason: "RV64I W-form (32-bit op) — never selected by isel for pure-integer \
                     programs (full-width 64-bit forms are emitted instead); not in the \
                     emitted set",
        },

        // (b) DEAD never-emitted M-extension high-multiply forms. The integer
        //     emitter uses MUL (low 64) only; MULH/MULHU/MULHSU are never
        //     selected. (Mirrors the AArch64 SMULH/UMULH disposition, but here
        //     they are simply never emitted, so allowlisting as never-selected is
        //     the clean honest call — no 64-bit formal claim is made or needed.)
        O::Mulh | O::Mulhsu | O::Mulhu => FailClosedAllowlisted {
            reason: "M-extension high-multiply (MULH/MULHU/MULHSU) — never selected by isel \
                     (only MUL low-64 is emitted); not in the emitted set",
        },

        // (b) DEAD never-emitted division / remainder (and their W-forms). The
        //     pure-integer self-host lane does not select hardware DIV/REM.
        O::Div | O::Divu | O::Rem | O::Remu | O::Mulw | O::Divw | O::Divuw | O::Remw | O::Remuw => {
            FailClosedAllowlisted {
                reason: "M-extension divide/remainder (and W-forms) — never selected by isel \
                         in the emitted integer set; not emitted, fail-closed as never-selected",
            }
        }

        // (b) DEAD never-emitted D-extension (double-precision FP). Pure-integer
        //     programs never select any FP-D opcode (FLD/FSD appear only for FPR
        //     spill, which is the regalloc/frame family, not a dataflow value
        //     proof). The whole FP-D surface is allowlisted as never-selected.
        O::FaddD
        | O::FsubD
        | O::FmulD
        | O::FdivD
        | O::FsqrtD
        | O::FeqD
        | O::FltD
        | O::FleD
        | O::FcvtDW
        | O::FcvtWD
        | O::FcvtDL
        | O::FcvtLD
        | O::FmvXD
        | O::FmvDX => FailClosedAllowlisted {
            reason: "D-extension floating-point — never selected by isel for pure-integer \
                         programs; not in the emitted set",
        },
        // FP-D load/store: only ever emitted for whole-FPR spill/reload, which is
        // the regalloc/frame family, not a per-instruction dataflow value proof.
        O::Fld | O::Fsd => FailClosedAllowlisted {
            reason: "FP-D load/store — only for FPR spill/reload (regalloc/frame family), \
                     not a per-instruction dataflow value proof; not in the pure-integer \
                     emitted set",
        },
    }
}

/// Classify a WebAssembly opcode. WILDCARD-FREE on purpose — see module note.
///
/// HONESTY POLICY (see wasm_function_verifier.rs / wasm_lowering_proofs.rs):
///
///   * The SCALAR VALUE OPS with a per-instruction trust-ir<->wasm value
///     equivalence (integer ALU/div-rem/bitwise/shift/compare, FP arith/compare,
///     FP unary, and the integer + FP-format width casts) are
///     `EmittableNeedsProof`. These are EXACTLY the opcodes
///     `wasm_function_verifier::opcode_to_source_op` reconstructs; `audit_wasm`
///     credits each via `wasm_reconstruction_discharges_valid` (the machine side
///     rebuilt from the REAL decoded opcode byte over symbolic value-stack
///     operands — a wrong byte / swapped non-commutative wiring REFUTES). This is
///     the value-equivalence denominator.
///   * STRUCTURAL forms — control flow (block/loop/if/else/end/br/br_if/br_table/
///     return/unreachable/drop/nop), linear memory (load/store), locals/globals
///     (local.get/set/tee, global.get/set), and calls
///     (call/call_indirect) — are `FailClosedAllowlisted` with a TRUE reason:
///     their correctness is the relooper / memory-model / call-ABI argument, NOT
///     a per-instruction VALUE equivalence, so they are OUT of the denominator.
///     `nop`/`unreachable` are `PseudoOrTrap` (no value obligation, like x86 UD2).
///   * Emitted scalar constants (`i32.const` / `i64.const`) are value
///     materialization and remain denominator-bearing RED until the real LEB
///     immediate is independently decoded and checked. Reserved, never-selected
///     `v128.const` remains explicitly excluded.
///   * Float/int conversions, reinterpret bitcasts, and popcnt are reconstructed
///     value ops and remain in the denominator.
///   * `f*.min`/`f*.max` are `FailClosedAllowlisted` as NEVER-SELECTED: the wasm
///     `int_binop_opcode` table emits no `BinOp::Fmin`/`Fmax` (only add/sub/mul/
///     div), so no compiled program contains them.
///   * The four lane-wise SIMD value ops are reconstructed and denominator-bearing.
///     Reserved v128 load/store/const forms are never selected and explicitly
///     excluded for that reason.
pub fn classify_wasm(opcode: WasmOpcode) -> OpcodeClass {
    use OpcodeClass::*;
    use WasmOpcode as O;

    match opcode {
        // ---- Reconstructable scalar value ops (the value-equivalence denom) ----
        //
        // Integer ALU / div-rem / bitwise / shift / compare (i32 + i64), FP
        // arith / compare / unary (f32 + f64), and the integer + FP-format width
        // casts. `audit_wasm` credits each via stack-machine operand
        // reconstruction (decode the REAL opcode byte; a wrong byte refutes).
        O::I32Add
        | O::I64Add
        | O::I32Sub
        | O::I64Sub
        | O::I32Mul
        | O::I64Mul
        | O::I32DivS
        | O::I64DivS
        | O::I32DivU
        | O::I64DivU
        | O::I32RemS
        | O::I64RemS
        | O::I32RemU
        | O::I64RemU
        | O::I32And
        | O::I64And
        | O::I32Or
        | O::I64Or
        | O::I32Xor
        | O::I64Xor
        | O::I32Shl
        | O::I64Shl
        | O::I32ShrS
        | O::I64ShrS
        | O::I32ShrU
        | O::I64ShrU => EmittableNeedsProof,
        O::I32Eq
        | O::I64Eq
        | O::I32Ne
        | O::I64Ne
        | O::I32LtS
        | O::I64LtS
        | O::I32LtU
        | O::I64LtU
        | O::I32GtS
        | O::I64GtS
        | O::I32GtU
        | O::I64GtU
        | O::I32LeS
        | O::I64LeS
        | O::I32LeU
        | O::I64LeU
        | O::I32GeS
        | O::I64GeS
        | O::I32GeU
        | O::I64GeU => EmittableNeedsProof,
        O::F32Add
        | O::F64Add
        | O::F32Sub
        | O::F64Sub
        | O::F32Mul
        | O::F64Mul
        | O::F32Div
        | O::F64Div => EmittableNeedsProof,
        O::F32Eq
        | O::F64Eq
        | O::F32Ne
        | O::F64Ne
        | O::F32Lt
        | O::F64Lt
        | O::F32Gt
        | O::F64Gt
        | O::F32Le
        | O::F64Le
        | O::F32Ge
        | O::F64Ge => EmittableNeedsProof,
        O::F32Abs
        | O::F64Abs
        | O::F32Neg
        | O::F64Neg
        | O::F32Sqrt
        | O::F64Sqrt
        | O::F32Ceil
        | O::F64Ceil
        | O::F32Floor
        | O::F64Floor
        | O::F32Trunc
        | O::F64Trunc => EmittableNeedsProof,
        O::I32WrapI64
        | O::I64ExtendI32S
        | O::I64ExtendI32U
        | O::F32DemoteF64
        | O::F64PromoteF32 => EmittableNeedsProof,
        // popcnt (ctpop bit-count) + bit-reinterpret (width-preserving bit-
        // identity): value-bearing ops RECONSTRUCTED via the stack-machine pattern
        // (`audit_wasm` credits them iff the reconstructed obligation discharges
        // Valid; a wrong opcode byte / wrong width refutes). They are IN the value-
        // equivalence denominator, NOT allowlisted out.
        O::I32Popcnt | O::I64Popcnt => EmittableNeedsProof,
        O::I32ReinterpretF32
        | O::I64ReinterpretF64
        | O::F32ReinterpretI32
        | O::F64ReinterpretI64 => EmittableNeedsProof,
        // Float<->int CONVERSIONS — value-bearing ops, now RECONSTRUCTED + COVERED.
        // The native evaluator now FAITHFULLY models rounding mode (RNE vs RTZ),
        // source signedness (zero-ext unsigned vs sign-ext signed) and saturation
        // (clamp to int range + NaN->0), so `audit_wasm` credits each via
        // `wasm_reconstruction_discharges_valid` (machine side rebuilt from the REAL
        // decoded opcode byte / 0xfc sub-index; a signed-for-unsigned or saturating-
        // for-wrapping or NaN-mishandling lowering REFUTES). They are IN the value-
        // equivalence denominator, no longer DeferredUnfaithfulModel.
        O::F32ConvertI32S
        | O::F32ConvertI32U
        | O::F32ConvertI64S
        | O::F32ConvertI64U
        | O::F64ConvertI32S
        | O::F64ConvertI32U
        | O::F64ConvertI64S
        | O::F64ConvertI64U
        | O::I32TruncSatF32S
        | O::I32TruncSatF32U
        | O::I32TruncSatF64S
        | O::I32TruncSatF64U
        | O::I64TruncSatF32S
        | O::I64TruncSatF32U
        | O::I64TruncSatF64S
        | O::I64TruncSatF64U => EmittableNeedsProof,

        // ---- Pseudo / trap (no value obligation, like x86 UD2 / AArch64 BRK) ----
        O::Nop | O::Unreachable => PseudoOrTrap,

        // ---- f*.min / f*.max: never selected by the wasm lowerer ----
        O::F32Min | O::F64Min | O::F32Max | O::F64Max => FailClosedAllowlisted {
            reason: "wasm f.min/f.max never selected by isel — the int_binop_opcode table emits \
                     only FP add/sub/mul/div; not in the emitted set (no BinOp::Fmin/Fmax arm)",
        },

        // Scalar constants are actively emitted value materialization. Without
        // independent LEB-immediate decoding, const==const would be degenerate,
        // so they remain explicit RED denominator rows.
        O::I32Const | O::I64Const => EmittableNeedsProof,
        O::V128Const => FailClosedAllowlisted {
            reason: "v128.const is reserved in the opcode surface but never selected by the \
                     current wasm lowerer (V128 values are rejected); not in the emitted set",
        },

        // ---- Locals / globals: structural slot access ----
        O::LocalGet | O::LocalSet | O::LocalTee | O::GlobalGet | O::GlobalSet => {
            FailClosedAllowlisted {
                reason: "local/global slot access — the local-slot allocation / SSA-to-stack \
                         binding (relooper) argument, not a per-instruction value equivalence",
            }
        }

        // ---- Linear memory load / store: memory-model family ----
        O::I32Load | O::I64Load | O::I32Store | O::I64Store => FailClosedAllowlisted {
            reason: "linear-memory load/store — covered by the wasm memory-model family \
                         (byte-addressed little-endian array theory, wasm_memory_proofs), not a \
                         per-instruction dataflow value equivalence",
        },
        O::V128Load | O::V128Store => FailClosedAllowlisted {
            reason: "v128 memory access is reserved in the opcode surface but never selected by \
                     the current wasm lowerer (V128 values are rejected); not in the emitted set",
        },

        // ---- Structured control flow: relooper / CFG family ----
        O::Block
        | O::Loop
        | O::If
        | O::Else
        | O::End
        | O::Br
        | O::BrIf
        | O::BrTable
        | O::Return
        | O::Drop => FailClosedAllowlisted {
            reason: "structured control flow / stack housekeeping — CFG edge correctness is the \
                     relooper structural bisimulation, not a per-instruction value equivalence",
        },

        // ---- Calls: call-ABI family ----
        O::Call | O::CallIndirect => FailClosedAllowlisted {
            reason: "call / call_indirect — compositional call-ABI correctness (arg/return \
                     stack discipline + table-index typecheck), not a per-instruction value \
                     equivalence",
        },

        // ---- SIMD / v128 LANE-WISE value ops: RECONSTRUCTED lane-wise, COVERED ----
        // The v128 lane-vector semantics are now built (smt.rs lane split/concat +
        // wasm_semantics SIMD encoders). `audit_wasm` credits each via stack-machine
        // operand reconstruction: the machine side is rebuilt from the REAL 0xfd
        // SUB-opcode (i32x4.add = lane-wise bvadd over the 128-bit vector; f32x4.add
        // = one representative binary32 lane), so a WRONG sub-opcode (mul-for-add) or
        // a WRONG lane width (i16x8 vs i32x4) REFUTES. They are IN the value-
        // equivalence denominator and COVERED. (v128.load/store moved to the memory
        // family; v128.const is reserved and never selected.)
        O::I32x4Add | O::I32x4Mul | O::F32x4Add | O::F32x4Mul => EmittableNeedsProof,
    }
}

/// Emitted x86-64 value/effect opcodes whose current proof binding is not
/// faithful and complete enough to earn coverage credit.
///
/// These rows deliberately remain `EmittableNeedsProof` and RED. Promotion
/// requires an independently refutable obligation for every value/effect facet;
/// volatile accesses additionally require evidence for the volatile
/// observation/ordering boundary, not merely their byte-identical plain-MOV
/// encoding.
pub fn x86_deferred_value_op_reason(opcode: X86Opcode) -> Option<&'static str> {
    use X86Opcode as O;
    match opcode {
        O::MovRI => Some(
            "MOV r,imm is actively emitted, but no independent immediate decode/value obligation \
             is registered; the former const==const model was a degenerate X==X",
        ),
        O::Cmpxchg8 | O::Cmpxchg16 => Some(
            "narrow LOCK CMPXCHG is actively emitted for AtomicU8/U16 compare_exchange, but the \
             current gate lacks width-faithful returns-old, conditional-store, and success-flag \
             obligations for the AL/AX forms",
        ),
        O::Pshufd => Some(
            "emitted PSHUFD lacks an independently decoded imm8-controlled lane-permutation \
             obligation",
        ),
        O::Pmovmskb => Some(
            "emitted PMOVMSKB lacks a faithful cross-lane sign-bit reduction to GPR obligation",
        ),
        O::MovdqaRR => Some(
            "emitted MOVDQA register copy lacks an independently decoded 128-bit bit-preservation \
             obligation; the reconstructed RM/MR memory forms do not cover RR",
        ),
        O::Punpckldq | O::Punpcklqdq | O::Punpcklbw | O::Punpckhbw => Some(
            "emitted PUNPCK interleave lacks a faithful cross-lane shuffle obligation for the \
             opcode's exact element width and low/high half",
        ),
        O::Ptest => Some(
            "emitted PTEST lacks a faithful whole-vector reduction to the complete observable \
             RFLAGS effect",
        ),
        O::Pblendvb => Some(
            "emitted PBLENDVB lacks a faithful three-input value obligation including its implicit \
             XMM0 mask register",
        ),
        O::Packuswb => Some(
            "emitted PACKUSWB lacks a faithful signed-saturating narrow plus lane-pack obligation",
        ),
        O::VolatileMovRM8
        | O::VolatileMovRM16
        | O::VolatileMovRM32
        | O::VolatileMovRM
        | O::VolatileMovMR8
        | O::VolatileMovMR16
        | O::VolatileMovMR32
        | O::VolatileMovMR
        | O::VolatileMovssRM
        | O::VolatileMovssMR
        | O::VolatileMovsdRM
        | O::VolatileMovsdMR
        | O::VolatileMovdquRM
        | O::VolatileMovdquMR
        | O::VolatileMovdqaRM
        | O::VolatileMovdqaMR => Some(
            "emitted volatile memory access has no accepted obligation that jointly covers the \
             complete load/store value or memory effect and preservation of the observable \
             volatile access/optimizer-ordering boundary; a byte-identical plain MOV proof alone \
             is insufficient",
        ),
        _ => None,
    }
}

/// Emitted RISC-V value opcodes that are not individually reconstructed or
/// mapped by the current function verifier.
pub fn riscv_deferred_value_op_reason(opcode: RiscVOpcode) -> Option<&'static str> {
    use RiscVOpcode as O;
    match opcode {
        O::Lui => Some(
            "LUI is actively emitted for constant materialization, but no independent U-immediate \
             decode/value obligation is registered",
        ),
        O::Xori => Some(
            "XORI is actively emitted inside comparison idioms, but the function verifier has no \
             individual opcode reconstruction/binding; the whole-sequence idiom proof does not \
             cover this standalone inventory row",
        ),
        O::Sltiu => Some(
            "SLTIU is actively emitted inside comparison idioms, but the function verifier has no \
             individual opcode reconstruction/binding; the whole-sequence idiom proof does not \
             cover this standalone inventory row",
        ),
        _ => None,
    }
}

/// For a value-bearing wasm opcode that is `EmittableNeedsProof` but is HONESTLY
/// DEFERRED (cannot be faithfully reconstructed yet), return the TRUE auditable
/// reason it is left RED. Returns `None` for the reconstructable scalar value ops
/// (those are credited via reconstruction) and for every non-`EmittableNeedsProof`
/// opcode.
///
/// HONESTY: these opcodes are value-bearing and stay IN the value-equivalence
/// denominator (RED), NOT allowlisted-out. A future reconstruction that faithfully
/// models them moves them from `DeferredUnfaithfulModel`-RED to covered. The two
/// emitted scalar constant forms are currently deferred because the gate has no
/// independent LEB immediate decoder; float/int conversions and lane-wise SIMD
/// are now faithfully reconstructed.
pub fn wasm_deferred_value_op_reason(opcode: WasmOpcode) -> Option<&'static str> {
    use WasmOpcode as O;
    match opcode {
        O::I32Const | O::I64Const => Some(
            "emitted scalar constant materialization has no independent signed-LEB immediate \
             decode/value obligation; const==const would be a degenerate self-equality",
        ),
        // The float<->int CONVERSIONS (int->FP convert ×8, saturating FP->int
        // trunc_sat ×8) are NO LONGER deferred: the native evaluator now FAITHFULLY
        // models rounding mode (RNE vs RTZ distinct), source signedness (zero-ext
        // unsigned vs sign-ext signed) and saturation (clamp to range + NaN->0), so
        // they RECONSTRUCT and are credited COVERED via
        // `wasm_reconstruction_discharges_valid` — a signed-for-unsigned or
        // saturating-for-wrapping (or NaN-mishandling) lowering now REFUTES. They
        // are deliberately ABSENT from this deferral table.
        //
        // The SIMD / v128 LANE-WISE value ops (i32x4.add/mul, f32x4.add/mul) are
        // ALSO no longer deferred: the v128 lane-vector semantics are now built and
        // each RECONSTRUCTS lane-wise (a wrong sub-opcode / wrong lane width
        // REFUTES). They are absent from this table too. v128.load/store/const are
        // reserved/never-selected (allowlisted-out), so they
        // never reach this deferral path.
        //
        _ => None,
    }
}

/// For a value-bearing AArch64 opcode that is `EmittableNeedsProof` but is
/// HONESTLY DEFERRED (its faithful obligations are not registered yet), return
/// the TRUE auditable reason it is left RED. Returns `None` for everything else.
///
/// HONESTY: these opcodes are value-bearing and stay IN the value-equivalence
/// denominator (RED), NOT allowlisted-out and NOT fake-covered. Many first
/// became visible in the universe backfill; later additions (including volatile
/// memory forms) must enter this table until faithful complete obligations land.
/// The enum-source inventory test prevents a variant from silently escaping the
/// audit, and this explicit table keeps its accepted debt visible and pinned.
/// Registering the missing obligations moves a row from RED to covered and
/// removes it from this table.
pub fn aarch64_deferred_value_op_reason(opcode: AArch64Opcode) -> Option<&'static str> {
    use AArch64Opcode as O;
    match opcode {
        O::LdrRI
        | O::LdrbRI
        | O::LdrhRI
        | O::LdrsbRI
        | O::LdrshRI
        | O::LdrRO
        | O::LdrbRO
        | O::LdrhRO
        | O::VolatileLdrRI
        | O::VolatileLdrbRI
        | O::VolatileLdrhRI => Some(
            "emitted scalar load lacks an independent faithful dereference/value model; the \
             legacy Memory query is a degenerate X==X and address-mode / roundtrip checks do \
             not establish the loaded value; volatile forms additionally require preservation \
             of the observable access and ordering boundary",
        ),
        O::StrRI
        | O::StrbRI
        | O::StrhRI
        | O::StrRO
        | O::StrbRO
        | O::StrhRO
        | O::VolatileStrRI
        | O::VolatileStrbRI
        | O::VolatileStrhRI => Some(
            "emitted scalar store lacks an independent faithful memory-effect model; the legacy \
             Memory query is a degenerate X==X and address-mode / roundtrip checks do not \
             establish the complete store effect; volatile forms additionally require \
             preservation of the observable access and ordering boundary",
        ),
        O::LdrPreIndex | O::LdrPostIndex | O::StrPreIndex | O::StrPostIndex => Some(
            "emitted writeback memory form lacks a faithful combined dereference/store plus \
             base-register-update obligation; the legacy load/store query is a degenerate X==X",
        ),
        O::FmovFprFpr => Some(
            "emitted scalar FPR copy has no independently decoded bit-preservation obligation; \
             the former CopyProp model collapsed to a degenerate X==X",
        ),
        O::MovR => Some(
            "emitted GPR copy has no independently decoded bit-preservation obligation; the \
             former CopyProp model collapsed to a degenerate X==X",
        ),
        // UMULL left this table when its faithful widening obligation landed
        // (lowering_proof::proof_umull_rr — zext64(Wn)*zext64(Wm) over BV64,
        // Concat-zext source vs encoder-faithful ZeroExtend+XZR machine; the
        // SMULL sext confusion refutes). SMULL stays a named RED row: the
        // SIGNED widening multiply has no faithful obligation of its own and
        // must NOT inherit the unsigned zext proof (#62 doctrine).
        O::Smull => Some(
            "emitted signed 32-to-64 widening multiply has no faithful widening result \
             obligation; checked-multiply/high-half evidence does not model SMULL semantics, \
             and the unsigned UMULL zext proof must not be inherited by the sext form",
        ),
        O::Csel | O::Csinc | O::Csneg => Some(
            "emitted conditional-select value semantics lack an independent instruction model; \
             the former IfConversion obligations were degenerate X==X and were retracted",
        ),
        O::Bfm => Some(
            "emitted bitfield insert is read-modify-write and has no faithful BFM decode/value \
             obligation; UBFM/SBFM extract evidence does not cover insertion",
        ),
        O::RorRI => Some(
            "emitted rotate-immediate lacks a faithful opcode-and-immediate reconstruction or \
             width-complete registered obligation",
        ),
        O::Rbit => Some(
            "emitted scalar bit reversal lacks a faithful SWAR/decode value obligation; the \
             separately modeled NEON per-byte RBIT does not cover scalar RBIT",
        ),
        O::FmovFprGpr | O::FmovGprFpr => Some(
            "emitted cross-register-class FMOV lacks an independently decoded matched-width \
             bit-transfer obligation; the shared-bitvector identity would be a degenerate X==X",
        ),
        O::FcvtSH | O::FcvtHS | O::FcvtDH | O::FcvtHD => Some(
            "emitted half-precision format conversion lacks width/direction-complete IEEE \
             conversion obligations for its actual source and destination formats",
        ),
        O::AddRIShift12 => Some(
            "emitted ADD-immediate-with-LSL#12 can materialize numeric values as well as \
             addresses, but no faithful shifted-immediate decode/value obligation is registered",
        ),
        O::Mrs => Some(
            "emitted MRS produces a system-register value (currently TPIDR_EL0), but no faithful \
             system-register selection and returned-value obligation is registered",
        ),
        O::Ldar | O::Ldarb | O::Ldarh => Some(
            "emitted acquire atomic load has no independent faithful returned-value plus ordering \
             obligation; the registered AtomicLoad model is a degenerate X==X under the strict \
             credit rule",
        ),
        O::Stlr | O::Stlrb | O::Stlrh => Some(
            "emitted release atomic store lacks one faithful width-complete memory-effect plus \
             release-ordering obligation; the registered store-then-load roundtrip omits the \
             ordering facet and cannot establish the complete opcode semantics",
        ),
        O::Cas | O::Casa | O::Casal | O::Casl => Some(
            "emitted compare-and-swap lacks a faithful combined success predicate, returned-old \
             value, conditional memory effect, and ordering obligation; the registered \
             success-path memory identity is degenerate X==X under the strict credit rule",
        ),
        O::Swp | O::Swpa | O::Swpal | O::Swpl => Some(
            "emitted LSE atomic swap lacks a faithful combined returned-old-value and memory-effect \
             obligation at each ordering; prior return-value identities were retracted",
        ),
        O::Ldadd
        | O::Ldadda
        | O::Ldaddal
        | O::Ldaddl
        | O::Ldclr
        | O::Ldclra
        | O::Ldclral
        | O::Ldclrl
        | O::Ldeor
        | O::Ldeora
        | O::Ldeoral
        | O::Ldeorl
        | O::Ldset
        | O::Ldseta
        | O::Ldsetal
        | O::Ldsetl => Some(
            "emitted LSE fetch-op RMW lacks one faithful width-and-ordering-complete obligation \
             covering both the returned old value and memory update; the registered I32 \
             memory-effect query proves only one semantic facet",
        ),
        O::Ldsmax
        | O::Ldsmaxa
        | O::Ldsmaxal
        | O::Ldsmaxl
        | O::Ldsmin
        | O::Ldsmina
        | O::Ldsminal
        | O::Ldsminl
        | O::Ldumax
        | O::Ldumaxa
        | O::Ldumaxal
        | O::Ldumaxl
        | O::Ldumin
        | O::Ldumina
        | O::Lduminal
        | O::Lduminl => Some(
            "emitted signed/unsigned min/max LSE RMW lacks a faithful combined returned-old-value \
             and conditional memory-effect obligation at each ordering",
        ),
        O::NeonLd1Post | O::NeonLdpQPost => Some(
            "emitted NEON post-index load: the base-register WRITEBACK is now PROVEN (the base \
             advances by exactly the bytes transferred, machine side DECODING imm7/Q out of the \
             real instruction word — neon_lowering_proofs::all_neon_post_index_writeback_proofs), \
             but the vector DEREFERENCE itself is still unmodeled: trust-cg-verify cannot reach \
             the real byte encoders (no trust-cg-codegen dependency) and SmtExpr has no \
             array-sorted Var, so arbitrary prior memory is not expressible and the earlier \
             per-opcode memory obligations were degenerate and retracted. RED on the transfer, \
             not on the writeback",
        ),
        O::NeonSt1Post | O::NeonStpQPost => Some(
            "emitted NEON post-index store: the base-register WRITEBACK is now PROVEN (the base \
             advances by exactly the bytes transferred, machine side DECODING imm7/Q out of the \
             real instruction word — neon_lowering_proofs::all_neon_post_index_writeback_proofs), \
             but the vector MEMORY EFFECT itself is still unmodeled: trust-cg-verify cannot reach \
             the real byte encoders (no trust-cg-codegen dependency) and SmtExpr has no \
             array-sorted Var, so arbitrary prior memory is not expressible and the earlier \
             per-opcode memory obligations were degenerate and retracted. RED on the transfer, \
             not on the writeback",
        ),
        // MOVN has a faithful concrete proof only for the 64-bit hw0 form.
        // Its 32-bit form complements 32 bits and zero-extends the result, so
        // the X-form theorem cannot honestly provide opcode-wide credit.
        O::Movn => Some(
            "the W-form MOVN width semantics (32-bit complement followed by zero-extension) \
             lack a faithful registered theorem; the existing hw0 theorem covers only X-form",
        ),
        // MOVK is value-bearing and contextual: it preserves all destination
        // bits outside the selected halfword.
        //
        // A faithful per-FORM obligation IS now registered — one
        // `ConstMat: MOVK {Xd,Wd} #imm16, LSL #hw splices halfword` per
        // architecturally legal (width, shift) pair, whose reference side is an
        // independent concat/extract splice (so a wrong slot or a clobbered
        // neighbouring halfword REFUTES; see the non-vacuity tests in
        // `const_materialize_proofs`). `FunctionVerifier` binds each emitted MOVK
        // to its concrete (width, shift) proof, so per-instruction promotion is
        // credited and the per-compile inventory admits MOVK.
        //
        // This row stays RED because THIS gate measures OPCODE-WIDE credit via
        // `opcode_to_proof_query`, and MOVK legitimately has no single
        // opcode-wide theorem: crediting one halfword's proof for all four would
        // be exactly the unfaithful inheritance #62 retracted. Clearing this row
        // requires an AArch64 form-polymorphic gate mechanism (the analogue of
        // `x86_width_polymorphic_proofs`), not a new theorem.
        O::Movk => Some(
            "MOVK has faithful PER-FORM splice obligations (one per legal width/shift, bound \
             per-instruction by the function verifier) but no single opcode-wide theorem; this \
             opcode-wide gate lacks an AArch64 form-polymorphic mechanism to credit them",
        ),
        _ => None,
    }
}

/// One required proof for a width-polymorphic opcode: the category it lives in,
/// the name substring to match, and the destination width that emission encodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WidthProof {
    /// Category the proof is registered under.
    pub category: ProofCategory,
    /// Name substring to match (case-sensitive, mirroring the x86 verifier).
    pub query: &'static str,
    /// Encoded destination width in bits (32 or 64) this query represents.
    pub encoded_width_bits: u32,
}

/// Width-polymorphic x86 opcodes whose coverage demands BOTH an i32 AND an i64
/// proof. Returns `None` for ordinary, single-width opcodes.
///
/// SOUNDNESS: the byte/word MOVSX/MOVZX opcodes encode i*->i64 (the encoder sets
/// REX.W), but the lowerer also emits them for a 32-bit destination, and the
/// 3-operand IMUL (`ImulRRI`) is emitted with a Gpr64 destination in the GEP
/// path. The coverage gate sees only the opcode, so it cannot pick a width; it
/// therefore requires that BOTH widths have a discharged proof, so neither width
/// can ship silently unproven. BOTH the i32 and i64 byte/word sign/zero-extension
/// proofs — and the IMUL-imm forms — are registered under
/// [`ProofCategory::X8664Lowering`] (the x86-specific REX.W
/// `proof_x86_mov{sx,zx}_{8,16}_to_{32,64}` proofs in x86_64_lowering_proofs.rs);
/// the width-equality check below thus compares two x86-specific proofs.
/// `Movsx` (MOVSXD) is omitted: it is the only single-width extend (always
/// i32->i64), already covered by its opcode-level `Sextend_I32_to_I64` query.
pub fn x86_width_polymorphic_proofs(opcode: X86Opcode) -> Option<&'static [WidthProof]> {
    use ProofCategory::X8664Lowering as X86;
    /// Compact constructor for a `WidthProof` table entry.
    const fn p(category: ProofCategory, query: &'static str, w: u32) -> WidthProof {
        WidthProof {
            category,
            query,
            encoded_width_bits: w,
        }
    }
    // Per-arm `const` bindings so the slice is const-promoted to `'static`
    // (a bare `&[p(..), ..]` in return position is a temporary — E0515).
    match opcode {
        X86Opcode::Movzx => {
            const PS: &[WidthProof] = &[
                p(X86, "Uextend_I8_to_I32", 32),
                p(X86, "Uextend_I8_to_I64", 64),
            ];
            Some(PS)
        }
        X86Opcode::MovzxW => {
            const PS: &[WidthProof] = &[
                p(X86, "Uextend_I16_to_I32", 32),
                p(X86, "Uextend_I16_to_I64", 64),
            ];
            Some(PS)
        }
        X86Opcode::MovsxB => {
            const PS: &[WidthProof] = &[
                p(X86, "Sextend_I8_to_I32", 32),
                p(X86, "Sextend_I8_to_I64", 64),
            ];
            Some(PS)
        }
        X86Opcode::MovsxW => {
            const PS: &[WidthProof] = &[
                p(X86, "Sextend_I16_to_I32", 32),
                p(X86, "Sextend_I16_to_I64", 64),
            ];
            Some(PS)
        }
        X86Opcode::ImulRRI => {
            const PS: &[WidthProof] = &[p(X86, "Imul_I32_Imm", 32), p(X86, "Imul_I64_Imm", 64)];
            Some(PS)
        }
        // BT r,imm8 is width+bit-polymorphic. The gate cannot pick a bit, so it
        // requires a representative i32 AND i64 BT-CF proof (bit 0) to exist and
        // discharge; the full per-bit family (k in 0..width) is registered by
        // `all_x86_64_bit_manip_proofs` and bound per-instance by the verifier's
        // `bt_to_proof_query`. The trailing space pins `#0` (not `#0..` like #03).
        X86Opcode::BtRI => {
            const PS: &[WidthProof] = &[p(X86, "BtRI_I32#0 ", 32), p(X86, "BtRI_I64#0 ", 64)];
            Some(PS)
        }
        // One-operand widening MUL: require the low-half (value) AND high-half
        // (overflow) proofs at both i32 and i64 — neither half/width can ship
        // without a proof. The per-instruction verifier binds the low-half
        // (value) proof; the high-half overflow proof is gate-required here.
        X86Opcode::Mul => {
            const PS: &[WidthProof] = &[
                p(X86, "Umul_I32 (low half RAX)", 32),
                p(X86, "Umul_I64 (low half RAX)", 64),
                p(X86, "Umul_I32 (high half RDX != 0)", 32),
                p(X86, "Umul_I64 (high half RDX != 0)", 64),
            ];
            Some(PS)
        }
        // ROUNDSS/ROUNDSD are MODE-polymorphic: one opcode realizes floor/ceil/
        // trunc via the imm8[1:0] rounding-select. The gate sees only the opcode,
        // so it cannot pick a mode; it therefore requires that ALL THREE emitted
        // rounding modes have a discharged proof, so no mode can ship silently
        // unproven. The per-instruction verifier binds the EXACT (width, mode)
        // proof from the immediate via `round_to_proof_query`. ROUNDSS proofs are
        // F32, ROUNDSD proofs are F64 (the opcode fixes the width).
        X86Opcode::Roundss => {
            const PS: &[WidthProof] = &[
                p(X86, "FFloor_F32", 32),
                p(X86, "FCeil_F32", 32),
                p(X86, "FTrunc_F32", 32),
            ];
            Some(PS)
        }
        X86Opcode::Roundsd => {
            const PS: &[WidthProof] = &[
                p(X86, "FFloor_F64", 64),
                p(X86, "FCeil_F64", 64),
                p(X86, "FTrunc_F64", 64),
            ];
            Some(PS)
        }
        // LOCK CMPXCHG (compare_exchange) [slice 4] is width-polymorphic: the ONE
        // opcode is emitted at BOTH i32 and i64 (the source-register class picks
        // the width; `select_cmpxchg` restricts to i32/i64). The gate has only the
        // opcode, so it requires the THREE CORE conditional-data-flow obligations
        // to discharge at BOTH widths — returns-old, the both-branches conditional
        // store, AND the success flag — so no width and no facet of the dual-output
        // CAS can ship silently unproven. (The two SUPPLEMENTARY branch proofs,
        // `success branch stores desired` and `failure branch preserves memory`,
        // are registered and validated by `test_all_x86_64_proofs`; they are extra
        // non-vacuity coverage that the both-branches `conditional store` already
        // gate-requires, so they are not re-listed here — this keeps the coverage
        // gate from re-discharging six memory-array proofs at 100k samples.) The
        // per-instruction verifier binds the width-correct returns-old proof via
        // `instruction_to_proof_query` (reading the source reg class).
        X86Opcode::Cmpxchg => {
            const PS: &[WidthProof] = &[
                p(X86, "Cmpxchg_I32 returns old value", 32),
                p(X86, "Cmpxchg_I32 conditional store", 32),
                p(X86, "Cmpxchg_I32 success flag", 32),
                p(X86, "Cmpxchg_I64 returns old value", 64),
                p(X86, "Cmpxchg_I64 conditional store", 64),
                p(X86, "Cmpxchg_I64 success flag", 64),
            ];
            Some(PS)
        }
        _ => None,
    }
}

/// Width-polymorphic AArch64 opcodes whose coverage demands EVERY FP width.
/// Returns `None` for ordinary, single-width opcodes.
///
/// SOUNDNESS: scalar FABS/FSQRT/FDIV are emitted at BOTH F32 (`FABS Sd`, …) and
/// F64 (`FABS Dd`, …) under one opcode. The coverage gate sees only the opcode,
/// so it cannot pick a width; it therefore requires that BOTH the F32 AND F64
/// value proofs (`Fabs_F{32,64}`/`Fsqrt_F{32,64}`/`Fdiv_F{32,64}`, registered
/// under [`ProofCategory::FloatingPoint`] by `all_fp_lowering_proofs`) exist and
/// discharge, so neither width can ship silently unproven. This is the AArch64
/// analogue of [`x86_width_polymorphic_proofs`]. The queries are lower-case
/// substrings: the AArch64 verifier (and the gate's `MatchCase::Insensitive`)
/// lower-case both the proof name and the query before `contains`.
pub fn aarch64_width_polymorphic_proofs(opcode: AArch64Opcode) -> Option<&'static [WidthProof]> {
    use ProofCategory::BitwiseShift as BWS;
    use ProofCategory::CmpCombine as CC;
    use ProofCategory::ExtensionTruncation as ET;
    use ProofCategory::FloatingPoint as FP;
    use ProofCategory::NeonLowering as NL;
    /// Compact constructor for a `WidthProof` table entry.
    const fn p(category: ProofCategory, query: &'static str, w: u32) -> WidthProof {
        WidthProof {
            category,
            query,
            encoded_width_bits: w,
        }
    }
    match opcode {
        // TST shares one opcode across W/X and writes all four flags. These are
        // complete packed-NZCV obligations, not a single condition-code view;
        // both widths must discharge before the opcode earns coverage.
        AArch64Opcode::Tst => {
            const PS: &[WidthProof] = &[
                p(CC, "tst packed nzcv w32", 32),
                p(CC, "tst packed nzcv w64", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::FabsRR => {
            const PS: &[WidthProof] = &[p(FP, "fabs_f32", 32), p(FP, "fabs_f64", 64)];
            Some(PS)
        }
        AArch64Opcode::FsqrtRR => {
            const PS: &[WidthProof] = &[p(FP, "fsqrt_f32", 32), p(FP, "fsqrt_f64", 64)];
            Some(PS)
        }
        AArch64Opcode::FrintmRR => {
            const PS: &[WidthProof] = &[p(FP, "ffloor_f32", 32), p(FP, "ffloor_f64", 64)];
            Some(PS)
        }
        AArch64Opcode::FrintpRR => {
            const PS: &[WidthProof] = &[p(FP, "fceil_f32", 32), p(FP, "fceil_f64", 64)];
            Some(PS)
        }
        AArch64Opcode::FrintzRR => {
            const PS: &[WidthProof] = &[p(FP, "ftrunc_f32", 32), p(FP, "ftrunc_f64", 64)];
            Some(PS)
        }
        AArch64Opcode::FdivRR => {
            const PS: &[WidthProof] = &[p(FP, "fdiv_f32", 32), p(FP, "fdiv_f64", 64)];
            Some(PS)
        }
        // Integer logical / shift ops (AND/ORR/EOR, LSL/LSR/ASR) are emitted at
        // BOTH I32 (`AND Wd,Wn,Wm`, …) and I64 (`AND Xd,Xn,Xm`, …) under one
        // opcode. The gate sees only the opcode, so it cannot pick a width; it
        // therefore requires that BOTH the I32 AND I64 GENERAL bitvector proofs
        // (`Band_I{32,64} -> AND`, `Bor_I*`, `Bxor_I*`, `Ishl_I*`, `Ushr_I*`,
        // `Sshr_I*`, registered under [`ProofCategory::BitwiseShift`] by
        // `all_bitwise_shift_proofs`) exist and discharge, so neither width can
        // ship silently unproven. This is the AArch64 analogue of x86's
        // ImulRRI/MOVSX/MOVZX gating. The queries are lower-case (the AArch64
        // verifier and `MatchCase::Insensitive` lower-case both sides). NOTE:
        // LSR is the LOGICAL shift right == `Ushr_I` (there is no `Lshr`); ASR
        // is the ARITHMETIC shift right == `Sshr_I`.
        AArch64Opcode::AndRR | AArch64Opcode::AndRI => {
            const PS: &[WidthProof] = &[p(BWS, "band_i32", 32), p(BWS, "band_i64", 64)];
            Some(PS)
        }
        AArch64Opcode::OrrRR | AArch64Opcode::OrrRI => {
            const PS: &[WidthProof] = &[p(BWS, "bor_i32", 32), p(BWS, "bor_i64", 64)];
            Some(PS)
        }
        AArch64Opcode::EorRR | AArch64Opcode::EorRI => {
            const PS: &[WidthProof] = &[p(BWS, "bxor_i32", 32), p(BWS, "bxor_i64", 64)];
            Some(PS)
        }
        // EOR with a ROR-shifted source (EOR Rd, Rn, Rm, ROR #k) is emitted at
        // BOTH the W (32) and X (64) register forms under ONE opcode by the
        // rotate-fusion peephole, so the gate demands BOTH faithful rotate-XOR
        // obligations discharge (neither width can ship silently unproven). Bound
        // to `all_eor_ror_shift_proofs` (SOURCE = frontend ROTL-XOR idiom,
        // MACHINE = shifted-register EOR-ROR model, structurally distinct /
        // provably equal; wrong-amount / wrong-shift-kind / operand-swap refute).
        AArch64Opcode::EorRRShift => {
            const PS: &[WidthProof] = &[
                p(BWS, "eor_ror_shift_i32", 32),
                p(BWS, "eor_ror_shift_i64", 64),
            ];
            Some(PS)
        }
        // ADD/SUB with an LSL-shifted source (ADD/SUB Rd, Rn, Rm, LSL #k) are each
        // emitted at BOTH the W (32) and X (64) register forms under ONE opcode by
        // the shift-ALU fusion peephole, so the gate demands BOTH faithful ring
        // obligations discharge (neither width can ship silently unproven). Bound
        // to `all_add_sub_lsl_shift_proofs` (SOURCE = `base +/- src*2^k` bvmul,
        // MACHINE = `base +/- (src<<k)` bvshl, structurally distinct / provably
        // equal; wrong-amount / ADD-vs-SUB / SUB operand-swap refute).
        AArch64Opcode::AddRRShift => {
            const PS: &[WidthProof] = &[
                p(BWS, "add_lsl_shift_i32", 32),
                p(BWS, "add_lsl_shift_i64", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::SubRRShift => {
            const PS: &[WidthProof] = &[
                p(BWS, "sub_lsl_shift_i32", 32),
                p(BWS, "sub_lsl_shift_i64", 64),
            ];
            Some(PS)
        }
        // ADD with an LSR-shifted source (ADD Rd, Rn, Rm, LSR #k) is emitted at
        // BOTH the W (32) and X (64) register forms under ONE opcode by the
        // shift-ALU fusion peephole, so the gate demands BOTH faithful
        // obligations discharge (neither width can ship silently unproven).
        // Bound to `all_add_lsr_shift_proofs` (SOURCE = `base + src/2^k` bvudiv,
        // MACHINE = `base + (src>>u k)` bvlshr, structurally distinct / provably
        // equal; wrong-amount / ASR-not-LSR / LSL-not-LSR / SUB-not-ADD refute).
        AArch64Opcode::AddRRShiftLsr => {
            const PS: &[WidthProof] = &[
                p(BWS, "add_lsr_shift_i32", 32),
                p(BWS, "add_lsr_shift_i64", 64),
            ];
            Some(PS)
        }
        // FCSEL (scalar FP conditional select) is emitted at BOTH the S (f32) and
        // D (f64) forms under ONE opcode (the ftype derives from the FPR class),
        // so the gate demands BOTH faithful bit-preserving-mux obligations
        // discharge (neither width ships silently unproven). Bound to
        // `all_fcsel_proofs` under FloatingPoint (SOURCE = `ite(trust_ir icmp, a,
        // b)` over raw FPR bits, MACHINE = `ite(eval_condition(cc,
        // encode_cmp(sel,0)), a, b)`; structurally distinct / provably equal;
        // inverted-cond / operand-swap refute controls).
        AArch64Opcode::FcselRR => {
            const PS: &[WidthProof] = &[p(FP, "fcsel_f32", 32), p(FP, "fcsel_f64", 64)];
            Some(PS)
        }
        AArch64Opcode::LslRR | AArch64Opcode::LslRI => {
            const PS: &[WidthProof] = &[p(BWS, "ishl_i32", 32), p(BWS, "ishl_i64", 64)];
            Some(PS)
        }
        AArch64Opcode::LsrRR | AArch64Opcode::LsrRI => {
            const PS: &[WidthProof] = &[p(BWS, "ushr_i32", 32), p(BWS, "ushr_i64", 64)];
            Some(PS)
        }
        AArch64Opcode::AsrRR | AArch64Opcode::AsrRI => {
            const PS: &[WidthProof] = &[p(BWS, "sshr_i32", 32), p(BWS, "sshr_i64", 64)];
            Some(PS)
        }
        // Bitfield EXTRACT (UBFM/SBFM) is emitted at BOTH the 32-bit (W) and
        // 64-bit (X) register forms under ONE opcode (isel.rs
        // select_bitfield_extract: `is_32` only selects the register class, the
        // opcode is the same). The gate sees only the opcode, so it requires BOTH
        // the w32 AND w64 FAITHFUL extract-ENCODING proofs (immr=lsb,
        // imms=lsb+width-1 decoded by the hardware UBFM/SBFM == ExtractBits/
        // SextractBits) exist and discharge — neither width can ship silently
        // unproven. Registered under ExtensionTruncation by
        // `register_bitfield_extract_proofs`; queries lower-case (insensitive
        // match). Disjoint from the sextend/uextend extends in the same category.
        AArch64Opcode::Ubfm => {
            const PS: &[WidthProof] =
                &[p(ET, "ubfm extract w32", 32), p(ET, "ubfm extract w64", 64)];
            Some(PS)
        }
        AArch64Opcode::Sbfm => {
            const PS: &[WidthProof] =
                &[p(ET, "sbfm extract w32", 32), p(ET, "sbfm extract w64", 64)];
            Some(PS)
        }
        // NEON FP vector arith / compare are emitted at BOTH `.4S` (f32 lanes)
        // and `.2D` (f64 lanes) under one opcode by the elementwise-FP
        // vectorizer (neon_fmap), so the gate demands a representative lane
        // obligation for EACH arrangement (all lanes are registered and
        // discharged by the DB + ay batch tests). HONESTY: these are the
        // LANE-PLUMBING obligations — see all_neon_fp_lanewise_proofs — whose
        // FP semantic weight rests on the shared FP model + the
        // silicon-validated NEON-FP differential bridge, NOT an independent
        // symbolic FP circuit.
        AArch64Opcode::NeonFaddV => {
            const PS: &[WidthProof] = &[
                p(NL, "faddv.4s lane0 lanewise-fp-intent", 32),
                p(NL, "faddv.2d lane0 lanewise-fp-intent", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonFsubV => {
            const PS: &[WidthProof] = &[
                p(NL, "fsubv.4s lane0 lanewise-fp-intent", 32),
                p(NL, "fsubv.2d lane0 lanewise-fp-intent", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonFmulV => {
            const PS: &[WidthProof] = &[
                p(NL, "fmulv.4s lane0 lanewise-fp-intent", 32),
                p(NL, "fmulv.2d lane0 lanewise-fp-intent", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonFdivV => {
            const PS: &[WidthProof] = &[
                p(NL, "fdivv.4s lane0 lanewise-fp-intent", 32),
                p(NL, "fdivv.2d lane0 lanewise-fp-intent", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonFcmgtV => {
            const PS: &[WidthProof] = &[
                p(NL, "fcmgtv.4s lane0 lanewise-fp-intent", 32),
                p(NL, "fcmgtv.2d lane0 lanewise-fp-intent", 64),
            ];
            Some(PS)
        }
        // NEON FP-reduction-vectorizer (`neon_fpred`) ops are emitted ONLY at
        // `.2D` (2 x f64), but with TWO lanes — so the gate demands BOTH lane
        // obligations discharge (a single-lane miswiring cannot hide). Bound to
        // the FAITHFUL per-lane obligations (all_neon_fpred_proofs): FMLA/FMLS via
        // the SINGLE-rounding `fp.fma` (the scalar FMADD credit lifted per lane),
        // UCVTF/SCVTF via the per-lane int->FP convert, DupScalarD via the 64-bit
        // lane bit-copy. HONESTY (see all_neon_fpred_proofs' module docs): both
        // sides share the SMT FP node, so these certify LANE/OP/WIDTH plumbing —
        // the wrong-encoding controls (FMLA<->FMLS, accumulator miswire, sign
        // confusion, wrong-lane) REFUTE — NOT an independent FP-circuit model.
        AArch64Opcode::NeonFmlaV => {
            // `.2D` (f64, neon_fpred / neon_farray) AND `.4S` (f32, the
            // neon_butterfly complex FFT butterfly and the f32 neon_fmap map
            // chain) are both emitted under this opcode; the gate demands BOTH
            // arrangements' faithful per-lane obligations discharge.
            const PS: &[WidthProof] = &[
                p(NL, "fmlav.2d lane0 fused-fp-intent", 64),
                p(NL, "fmlav.2d lane1 fused-fp-intent", 64),
                p(NL, "fmlav.4s lane0 fused-fp-intent", 32),
                p(NL, "fmlav.4s lane3 fused-fp-intent", 32),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonFmlsV => {
            const PS: &[WidthProof] = &[
                p(NL, "fmlsv.2d lane0 fused-fp-intent", 64),
                p(NL, "fmlsv.2d lane1 fused-fp-intent", 64),
                p(NL, "fmlsv.4s lane0 fused-fp-intent", 32),
                p(NL, "fmlsv.4s lane3 fused-fp-intent", 32),
            ];
            Some(PS)
        }
        // FMLA by element (Vd += Vn * Vm[selector]): emitted at BOTH `.4S`
        // (f32, the daxpy shape) and `.2D` (f64). The opcode carries both a
        // selector immediate and a vector arrangement, so coverage must be tied
        // to the COMPLETE selector x destination matrix. Merely checking sel0 /
        // dest0 at each width leaves the gate green if any of the other 18
        // obligation registrations silently disappears.
        AArch64Opcode::NeonFmlaLaneV => {
            const PS: &[WidthProof] = &[
                p(NL, "fmlalanev.4s sel0 dest0 fused-fp-intent", 32),
                p(NL, "fmlalanev.4s sel0 dest1 fused-fp-intent", 32),
                p(NL, "fmlalanev.4s sel0 dest2 fused-fp-intent", 32),
                p(NL, "fmlalanev.4s sel0 dest3 fused-fp-intent", 32),
                p(NL, "fmlalanev.4s sel1 dest0 fused-fp-intent", 32),
                p(NL, "fmlalanev.4s sel1 dest1 fused-fp-intent", 32),
                p(NL, "fmlalanev.4s sel1 dest2 fused-fp-intent", 32),
                p(NL, "fmlalanev.4s sel1 dest3 fused-fp-intent", 32),
                p(NL, "fmlalanev.4s sel2 dest0 fused-fp-intent", 32),
                p(NL, "fmlalanev.4s sel2 dest1 fused-fp-intent", 32),
                p(NL, "fmlalanev.4s sel2 dest2 fused-fp-intent", 32),
                p(NL, "fmlalanev.4s sel2 dest3 fused-fp-intent", 32),
                p(NL, "fmlalanev.4s sel3 dest0 fused-fp-intent", 32),
                p(NL, "fmlalanev.4s sel3 dest1 fused-fp-intent", 32),
                p(NL, "fmlalanev.4s sel3 dest2 fused-fp-intent", 32),
                p(NL, "fmlalanev.4s sel3 dest3 fused-fp-intent", 32),
                p(NL, "fmlalanev.2d sel0 dest0 fused-fp-intent", 64),
                p(NL, "fmlalanev.2d sel0 dest1 fused-fp-intent", 64),
                p(NL, "fmlalanev.2d sel1 dest0 fused-fp-intent", 64),
                p(NL, "fmlalanev.2d sel1 dest1 fused-fp-intent", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonUcvtfV => {
            // `.2D` (i64->f64, neon_fpred) AND `.4S` (i32->f32, neon_farray IOTA
            // fill) are both emitted under this opcode; the gate demands BOTH
            // arrangements' faithful per-lane obligations discharge.
            const PS: &[WidthProof] = &[
                p(NL, "ucvtfv.2d lane0 int-to-fp-intent", 64),
                p(NL, "ucvtfv.2d lane1 int-to-fp-intent", 64),
                p(NL, "ucvtfv.4s lane0 int-to-fp-intent", 32),
                p(NL, "ucvtfv.4s lane3 int-to-fp-intent", 32),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonScvtfV => {
            const PS: &[WidthProof] = &[
                p(NL, "scvtfv.2d lane0 int-to-fp-intent", 64),
                p(NL, "scvtfv.2d lane1 int-to-fp-intent", 64),
                p(NL, "scvtfv.4s lane0 int-to-fp-intent", 32),
                p(NL, "scvtfv.4s lane3 int-to-fp-intent", 32),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonDupScalarD => {
            const PS: &[WidthProof] = &[
                p(NL, "dupscalard.d lane0 lane-copy-intent", 64),
                p(NL, "dupscalard.d lane1 lane-copy-intent", 64),
            ];
            Some(PS)
        }
        // NEON f32->f64 widening convert (FCVTL/FCVTL2) is emitted ONLY at `.2D`
        // (2 x f64 output), but with TWO lanes — so the gate demands BOTH lane
        // obligations discharge (a single-lane miswiring cannot hide). Bound to
        // the FAITHFUL per-lane obligations (all_neon_fcvtl_proofs): each output
        // lane is the EXACT `fpext` of a source f32 lane (low half for FCVTL,
        // high half for FCVTL2). The wrong-HALF (FCVTL<->FCVTL2) and wrong-lane
        // controls REFUTE.
        AArch64Opcode::NeonFcvtlV => {
            const PS: &[WidthProof] = &[
                p(NL, "fcvtlv.2d lane0 fpext-intent", 64),
                p(NL, "fcvtlv.2d lane1 fpext-intent", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonFcvtl2V => {
            const PS: &[WidthProof] = &[
                p(NL, "fcvtl2v.2d lane0 fpext-intent", 64),
                p(NL, "fcvtl2v.2d lane1 fpext-intent", 64),
            ];
            Some(PS)
        }
        // NEON lane -> GPR extract (UMOV) is emitted at ALL FOUR element sizes
        // under one opcode — `.16B`/`.8H`/`.4S` -> a 32-bit `Wd`, `.2D` -> a
        // 64-bit `Xd` — each at a COMPILE-TIME-CONSTANT lane immediate. The gate
        // sees only the opcode, so it demands EVERY emitted (size, lane) prove:
        // the FULL matrix (`.16B` 16 lanes + `.8H` 8 + `.4S` 4 + `.2D` 2 = 30),
        // bound to the FAITHFUL per-(size,lane) obligations (all_neon_umov_proofs)
        // so a single-lane OR wrong-size miswiring cannot hide. Both sides are
        // PURE QF_BV (raw-D-half slice vs `encode_neon_umov_general` over the
        // reassembled register): a COMPLETE faithful extract + zero-extend proof;
        // the wrong-lane / wrong-size controls REFUTE.
        AArch64Opcode::NeonUmovGen => {
            const PS: &[WidthProof] = &[
                // `.16B` -> Wd (zero-ext 8 -> 32), lanes 0..=15.
                p(NL, "umovgen.16b lane00 extract-to-gpr32", 32),
                p(NL, "umovgen.16b lane01 extract-to-gpr32", 32),
                p(NL, "umovgen.16b lane02 extract-to-gpr32", 32),
                p(NL, "umovgen.16b lane03 extract-to-gpr32", 32),
                p(NL, "umovgen.16b lane04 extract-to-gpr32", 32),
                p(NL, "umovgen.16b lane05 extract-to-gpr32", 32),
                p(NL, "umovgen.16b lane06 extract-to-gpr32", 32),
                p(NL, "umovgen.16b lane07 extract-to-gpr32", 32),
                p(NL, "umovgen.16b lane08 extract-to-gpr32", 32),
                p(NL, "umovgen.16b lane09 extract-to-gpr32", 32),
                p(NL, "umovgen.16b lane10 extract-to-gpr32", 32),
                p(NL, "umovgen.16b lane11 extract-to-gpr32", 32),
                p(NL, "umovgen.16b lane12 extract-to-gpr32", 32),
                p(NL, "umovgen.16b lane13 extract-to-gpr32", 32),
                p(NL, "umovgen.16b lane14 extract-to-gpr32", 32),
                p(NL, "umovgen.16b lane15 extract-to-gpr32", 32),
                // `.8H` -> Wd (zero-ext 16 -> 32), lanes 0..=7.
                p(NL, "umovgen.8h lane00 extract-to-gpr32", 32),
                p(NL, "umovgen.8h lane01 extract-to-gpr32", 32),
                p(NL, "umovgen.8h lane02 extract-to-gpr32", 32),
                p(NL, "umovgen.8h lane03 extract-to-gpr32", 32),
                p(NL, "umovgen.8h lane04 extract-to-gpr32", 32),
                p(NL, "umovgen.8h lane05 extract-to-gpr32", 32),
                p(NL, "umovgen.8h lane06 extract-to-gpr32", 32),
                p(NL, "umovgen.8h lane07 extract-to-gpr32", 32),
                // `.4S` -> Wd (32-bit lane, no ext), lanes 0..=3.
                p(NL, "umovgen.4s lane00 extract-to-gpr32", 32),
                p(NL, "umovgen.4s lane01 extract-to-gpr32", 32),
                p(NL, "umovgen.4s lane02 extract-to-gpr32", 32),
                p(NL, "umovgen.4s lane03 extract-to-gpr32", 32),
                // `.2D` -> Xd (64-bit lane, no ext), lanes 0..=1.
                p(NL, "umovgen.2d lane00 extract-to-gpr64", 64),
                p(NL, "umovgen.2d lane01 extract-to-gpr64", 64),
            ];
            Some(PS)
        }
        // ARRANGEMENT-COMPLETENESS BINDINGS.
        //
        // Everything below is EMITTED at more than one arrangement. Without an
        // entry here an opcode is credited by its SINGLE representative
        // `opcode_to_proof_query` (e.g. "addv.4s lanewise-intent"), so the other
        // emitted arrangements' obligations are never DEMANDED — they could be
        // deleted or silently broken and the gate would stay green. The audit
        // behind this list walked every NEON emission site under
        // `crates/trust-cg-opt/src/`, resolved each arrangement immediate
        // (including the dynamic `ctx.arr_code` / `w.farr` forms) to concrete
        // values, and diffed that against the registered obligations.
        //
        // Opcodes whose trailing immediate is NOT an arrangement are
        // deliberately absent: NeonUmovGen takes an element size, NeonMovi an
        // imm8, NeonLdpQPost/NeonStpQPost a post-index offset, NeonExtV a byte
        // shift, and the whole-register bitwise ops (AndV/OrrV/EorV/NotV) carry
        // none at all (the encoder derives Q from the destination class).
        AArch64Opcode::NeonRev64V => {
            // `.4S` = the complex-FFT butterfly's {rp,ip} pair swap
            // (neon_butterfly); `.16B` = the byte-order reversal inside the
            // `<2 x i64>` bit-reverse lowering (vectorize.rs).
            const PS: &[WidthProof] = &[
                p(NL, "rev64v.4s pair-swap-intent", 32),
                p(NL, "rev64v.16b byte-reverse-intent", 8),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonMovi => {
            // All four element views of the same Q=1 byte-replicated write, so
            // the replication is pinned at every granularity a consumer reads at.
            const PS: &[WidthProof] = &[
                p(NL, "movi.16b byte-replicated-immediate-intent", 8),
                p(NL, "movi.8h byte-replicated-immediate-intent", 16),
                p(NL, "movi.4s byte-replicated-immediate-intent", 32),
                p(NL, "movi.2d byte-replicated-immediate-intent", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonInsGen => {
            const PS: &[WidthProof] = &[
                p(NL, "insgen.16b lane00 gpr-insert-intent", 8),
                p(NL, "insgen.16b lane15 gpr-insert-intent", 8),
                p(NL, "insgen.8h lane00 gpr-insert-intent", 16),
                p(NL, "insgen.8h lane07 gpr-insert-intent", 16),
                p(NL, "insgen.4s lane00 gpr-insert-intent", 32),
                p(NL, "insgen.4s lane03 gpr-insert-intent", 32),
                p(NL, "insgen.2d lane00 gpr-insert-intent", 64),
                p(NL, "insgen.2d lane01 gpr-insert-intent", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonDupGen => {
            // Every emitted element size, at a lane where the sizes genuinely
            // differ as well as at lane 0 — a DUP that populated only lane 0
            // would satisfy a lane-0-only pin while dropping the broadcast.
            const PS: &[WidthProof] = &[
                p(NL, "dupgen.16b lane00 gpr-broadcast-intent", 8),
                p(NL, "dupgen.16b lane15 gpr-broadcast-intent", 8),
                p(NL, "dupgen.8h lane00 gpr-broadcast-intent", 16),
                p(NL, "dupgen.8h lane07 gpr-broadcast-intent", 16),
                p(NL, "dupgen.4s lane00 gpr-broadcast-intent", 32),
                p(NL, "dupgen.4s lane03 gpr-broadcast-intent", 32),
                p(NL, "dupgen.2d lane00 gpr-broadcast-intent", 64),
                p(NL, "dupgen.2d lane01 gpr-broadcast-intent", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonDupElem => {
            // Both emitted arrangements, at EVERY lane: the lane index is what
            // the permutation is about, so a lane-0-only pin would leave the
            // selection axis unproven.
            const PS: &[WidthProof] = &[
                p(NL, "dupelem.4s lane00 broadcast-intent", 32),
                p(NL, "dupelem.4s lane01 broadcast-intent", 32),
                p(NL, "dupelem.4s lane02 broadcast-intent", 32),
                p(NL, "dupelem.4s lane03 broadcast-intent", 32),
                p(NL, "dupelem.2d lane00 broadcast-intent", 64),
                p(NL, "dupelem.2d lane01 broadcast-intent", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonRev32V => {
            // `.16B` = the `<4 x i32>` reverse_bits lowering; `.8B` (Q=0) = the
            // mixed-width path, which also ZEROES the upper half.
            const PS: &[WidthProof] = &[
                p(NL, "rev32v.16b byte-reverse-intent", 8),
                p(NL, "rev32v.8b byte-reverse-intent", 8),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonRbitV => {
            // `.16B` = the `[u8; N]` reverse_bits map; `.8B` (Q=0) = the
            // vectorizer's mixed-width path, which also ZEROES the upper half.
            const PS: &[WidthProof] = &[
                p(NL, "rbitv.16b per-byte-reverse-intent", 8),
                p(NL, "rbitv.8b per-byte-reverse-intent", 8),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonAddV => {
            const PS: &[WidthProof] = &[
                p(NL, "addv.4s lanewise-intent", 32),
                p(NL, "addv.2d lanewise-intent", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonSubV => {
            const PS: &[WidthProof] = &[
                p(NL, "subv.4s lanewise-intent", 32),
                p(NL, "subv.2d lanewise-intent", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonCmeqV => {
            const PS: &[WidthProof] = &[
                p(NL, "cmeqv.4s lanewise-intent", 32),
                p(NL, "cmeqv.2d lanewise-intent", 64),
                p(NL, "cmeqv.16b lanewise-intent", 8),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonCmgeV => {
            const PS: &[WidthProof] = &[
                p(NL, "cmgev.4s lanewise-intent", 32),
                p(NL, "cmgev.2d lanewise-intent", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonCmgtV => {
            const PS: &[WidthProof] = &[
                p(NL, "cmgtv.4s lanewise-intent", 32),
                p(NL, "cmgtv.2d lanewise-intent", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonCmhiV => {
            const PS: &[WidthProof] = &[
                p(NL, "cmhiv.4s lanewise-intent", 32),
                p(NL, "cmhiv.2d lanewise-intent", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonCmhsV => {
            const PS: &[WidthProof] = &[
                p(NL, "cmhsv.4s lanewise-intent", 32),
                p(NL, "cmhsv.2d lanewise-intent", 64),
                p(NL, "cmhsv.16b lanewise-intent", 8),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonShlVImm => {
            const PS: &[WidthProof] = &[p(NL, "shlvimm.4s", 32), p(NL, "shlvimm.2d", 64)];
            Some(PS)
        }
        AArch64Opcode::NeonUshrVImm => {
            const PS: &[WidthProof] = &[
                p(NL, "ushrvimm.4s", 32),
                p(NL, "ushrvimm.2d", 64),
                p(NL, "ushrvimm.16b", 8),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonSshrVImm => {
            const PS: &[WidthProof] = &[p(NL, "sshrvimm.4s", 32), p(NL, "sshrvimm.2d", 64)];
            Some(PS)
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The emittable-opcode universe
// ---------------------------------------------------------------------------
//
// The wildcard-free classifier `match`es above give compile-time classification
// exhaustiveness. These four arrays give the ENUMERATION the audit iterates.
// The universe tests independently parse each owning enum declaration and
// compare every unit-variant name with the corresponding array's `Debug` names,
// in addition to rejecting duplicates and retaining a numeric release-baseline
// pin. Thus appending and classifying a variant while omitting it here fails the
// build gate instead of silently escaping the audit.

/// Every `AArch64Opcode` variant. Source of truth: `crates/trust-cg-ir/src/inst.rs`.
pub const ALL_AARCH64_OPCODES: &[AArch64Opcode] = {
    use AArch64Opcode::*;
    &[
        // Arithmetic
        AddRR,
        AddRI,
        AddRIShift12,
        SubRR,
        SubRI,
        MulRR,
        Msub,
        Smull,
        Umull,
        SDiv,
        UDiv,
        Neg,
        Madd,
        Smulh,
        Umulh,
        Adc,
        Sbc,
        AddsRR,
        AddsRI,
        SubsRR,
        SubsRI,
        // Logical
        AndRR,
        AndRI,
        OrrRR,
        OrrRI,
        EorRR,
        EorRI,
        // EOR with ROR-shifted source (rotate-fusion peephole), covered via its
        // faithful rotate-XOR obligations (all_eor_ror_shift_proofs; W+X forms,
        // wrong-amount / wrong-shift-kind / operand-swap refute controls).
        EorRRShift,
        EorRRLsl,
        EorRRLsr,
        // ADD/SUB with LSL-shifted source (shift-ALU fusion peephole), covered via
        // their faithful ring obligations (all_add_sub_lsl_shift_proofs; W+X forms,
        // wrong-amount / ADD-vs-SUB / SUB operand-swap refute controls).
        AddRRShift,
        SubRRShift,
        // ADD with LSR-shifted source (shift-ALU fusion peephole, LSR sibling —
        // the srem/sdiv magic sign-bit correction), covered via its faithful
        // obligations (all_add_lsr_shift_proofs; W+X forms, wrong-amount /
        // ASR-not-LSR / LSL-not-LSR / SUB-not-ADD refute controls).
        AddRRShiftLsr,
        OrnRR,
        BicRR,
        // Shifts
        LslRR,
        LsrRR,
        AsrRR,
        LslRI,
        LsrRI,
        AsrRI,
        RorRI,
        Rbit,
        // Compare / select
        CmpRR,
        CmpRI,
        Tst,
        Csel,
        Csinc,
        Csinv,
        Csneg,
        // Scalar FP conditional select (FP-`Select` isel path), covered via its
        // faithful bit-preserving-mux obligations (all_fcsel_proofs; S+D forms,
        // inverted-cond / operand-swap refute controls).
        FcselRR,
        CSet,
        CMPWrr,
        CMPXrr,
        CMPWri,
        CMPXri,
        // Bitfield
        Bfm,
        Sbfm,
        Ubfm,
        // Move
        MovR,
        MovI,
        Movz,
        Movn,
        Movk,
        FmovImm,
        MOVWrr,
        MOVXrr,
        MOVZWi,
        MOVZXi,
        // Memory (immediate)
        LdrRI,
        StrRI,
        LdrPreIndex,
        StrPreIndex,
        LdrPostIndex,
        StrPostIndex,
        LdrbRI,
        LdrhRI,
        LdrsbRI,
        LdrshRI,
        StrbRI,
        StrhRI,
        VolatileLdrRI,
        VolatileLdrbRI,
        VolatileLdrhRI,
        VolatileStrRI,
        VolatileStrbRI,
        VolatileStrhRI,
        LdrLiteral,
        LdpRI,
        StpRI,
        StpPreIndex,
        LdpPostIndex,
        STRWui,
        STRXui,
        STRSui,
        STRDui,
        // Memory (register-offset)
        LdrRO,
        StrRO,
        LdrbRO,
        LdrhRO,
        StrbRO,
        StrhRO,
        LdrswRO,
        // Address materialization
        Adr,
        Adrp,
        AddPCRel,
        AddTprelHi12,
        AddTprelLo12,
        LdrGot,
        LdrTlvp,
        LdrGottprel,
        // Branch / call
        B,
        BCond,
        Bcc,
        Cbz,
        Cbnz,
        Tbz,
        Tbnz,
        Br,
        Bl,
        BL,
        Blr,
        BLR,
        TailCall,
        Ret,
        // Extensions
        Sxtb,
        Sxth,
        Sxtw,
        Uxtb,
        Uxth,
        Uxtw,
        // Floating-point
        FaddRR,
        FsubRR,
        FmulRR,
        FdivRR,
        FmaddRR,
        FnegRR,
        FabsRR,
        FsqrtRR,
        // IEEE-754 minNum/maxNum (emitted by the fmin/fmax intrinsic lowering)
        // and round-to-integral floor/ceil/trunc (emitted by the
        // Ffloor/Fceil/Ftrunc lowering); previously absent from the audit
        // universe (an unaudited blind spot).
        FmaxnmRR,
        FminnmRR,
        FrintmRR,
        FrintpRR,
        FrintzRR,
        Fcmp,
        FmovFprFpr,
        FmovFprGpr,
        FmovGprFpr,
        FcvtzsRR,
        FcvtzuRR,
        ScvtfRR,
        UcvtfRR,
        FcvtSD,
        FcvtDS,
        FcvtSH,
        FcvtHS,
        FcvtDH,
        FcvtHD,
        // System / barriers
        Mrs,
        Dmb,
        Dsb,
        Isb,
        // Atomics (acquire/release/exclusive/CAS/swap)
        Ldar,
        Ldarb,
        Ldarh,
        Stlr,
        Stlrb,
        Stlrh,
        Ldaxr,
        Stlxr,
        Cas,
        Casa,
        Casal,
        // Release-only CAS (emitted by the exact-form release CAS orderings);
        // previously absent from the audit universe.
        Casl,
        Swp,
        // Acquire-only / release-only swaps (exact-form LSE orderings);
        // previously absent from the audit universe.
        Swpa,
        Swpal,
        Swpl,
        // Atomics (LSE RMW). The A-forms (acquire-only) and L-forms
        // (release-only) are the exact-ordering LSE variants added alongside
        // the base/AL forms; they were previously absent from the audit
        // universe (an unaudited blind spot).
        Ldadd,
        Ldadda,
        Ldaddal,
        Ldaddl,
        Ldclr,
        Ldclra,
        Ldclral,
        Ldclrl,
        Ldeor,
        Ldeora,
        Ldeoral,
        Ldeorl,
        Ldset,
        Ldseta,
        Ldsetal,
        Ldsetl,
        Ldsmax,
        Ldsmaxa,
        Ldsmaxal,
        Ldsmaxl,
        Ldsmin,
        Ldsmina,
        Ldsminal,
        Ldsminl,
        Ldumax,
        Ldumaxa,
        Ldumaxal,
        Ldumaxl,
        Ldumin,
        Ldumina,
        Lduminal,
        Lduminl,
        // NEON
        NeonAddV,
        NeonSubV,
        NeonMulV,
        NeonAndV,
        NeonOrrV,
        NeonEorV,
        NeonBicV,
        NeonNotV,
        NeonCmeqV,
        NeonCmgeV,
        NeonCmgtV,
        NeonCmhiV,
        NeonCmhsV,
        NeonFaddV,
        NeonFsubV,
        NeonFmulV,
        NeonFdivV,
        // NEON FP-reduction-vectorizer (`neon_fpred`) ops, all emitted at `.2D`:
        // fused multiply-accumulate/-subtract (FMLA/FMLS), per-lane int->FP
        // convert (UCVTF/SCVTF), and the lane->scalar 64-bit copy (DUP Dd,
        // Vn.D[lane]). Previously absent from the audit universe (an unaudited
        // blind spot); now credited via their FAITHFUL per-lane obligations
        // (all_neon_fpred_proofs, both `.2D` lanes each, real-solver discharged
        // with wrong-encoding refute controls).
        NeonFmlaV,
        NeonFmlsV,
        NeonUcvtfV,
        NeonScvtfV,
        NeonDupScalarD,
        // NEON FP fused multiply-accumulate BY ELEMENT (FMLA Vd.T, Vn.T,
        // Vm.Ts[lane]), emitted by the elementwise-FP vectorizer (neon_fmap) for
        // `y[i] += da*x[i]` with the scalar invariant `da` in a lane (no DUP).
        // Emitted at `.4S` (f32) and `.2D` (f64); credited via its FAITHFUL
        // per-(arrangement, dest lane, selector) obligations (all_neon_fmla_lane_proofs,
        // real-solver discharged with wrong-lane-selector / FMLA<->FMLS polarity /
        // accumulator-miswire refute controls).
        NeonFmlaLaneV,
        // NEON f32->f64 widening convert (FCVTL/FCVTL2), emitted by the FP
        // array-reduction vectorizer (neon_farray) for the widening dot. Credited
        // via their FAITHFUL per-lane obligations (all_neon_fcvtl_proofs, both
        // `.2D` lanes each, real-solver discharged with wrong-half/wrong-lane
        // refute controls).
        NeonFcvtlV,
        NeonFcvtl2V,
        // FP vector compare greater-than (emitted by the FP count-above
        // vectorizer's lane-mask compare).
        NeonFcmgtV,
        NeonShlVImm,
        NeonUshrVImm,
        NeonSshrVImm,
        // Lane-wise integer min/max (emitted by the min/max reduction pass). These
        // were previously absent from the audit universe (an unaudited blind spot);
        // added so the gate actually credits their FAITHFUL D-pair obligations.
        NeonSmaxV,
        NeonSminV,
        NeonUmaxV,
        NeonUminV,
        NeonDupGen,
        NeonDupElem,
        NeonInsGen,
        NeonUmovGen,
        NeonMovi,
        NeonAddpScalar,
        NeonUmaxv,
        NeonRbitV,
        NeonRev32V,
        NeonRev64V,
        // Popcount fold (emitted by the ctpop-reduction lowering); credited via
        // their FAITHFUL D-pair obligations.
        NeonCntV,
        NeonUaddlpV,
        NeonSaddlpV,
        NeonBitV,
        // Signed abs (emitted by the abs-sum reduction lowering); credited via its
        // FAITHFUL D-pair obligation.
        NeonAbsV,
        // Unsigned dot-product accumulate (emitted by the ctpop-reduction lowering's
        // UDOT fast path); credited via its FAITHFUL D-pair obligation.
        NeonUdotV,
        // Byte-wise extract/concatenate (emitted by the stencil vectorizer's
        // sliding-window rework); credited via its FAITHFUL D-pair obligations
        // (one per emitted immediate #4/#8/#12).
        NeonExtV,
        // Widening multiply-accumulate-long (SMLAL/SMLAL2/UMLAL/UMLAL2, emitted by
        // the neon_array widening-dot vectorizer for `s(i64) += ext(a_i32[i]) *
        // ext(b_i32[i])`); credited via their FAITHFUL D-pair accumulate obligations
        // (all_neon_smlal_proofs, one per opcode, both `.2D` lanes concatenated;
        // sign-confusion / no-accumulate / wrong-half / truncating-mul refute
        // controls).
        NeonSmlalV,
        NeonSmlal2V,
        NeonUmlalV,
        NeonUmlal2V,
        // Widening add-wide (UADDW/UADDW2, emitted by the neon_array widening
        // abs-sum vectorizer TRACK D for `s(i64) += zext64(abs_bits(a_i32[i]
        // [+ inv]))` — the three-operand unsigned wide add that replaces the
        // UMLAL-by-ones MAC); credited via their FAITHFUL D-pair obligations
        // (all_neon_uaddw_proofs, one per opcode, both `.2D` lanes concatenated;
        // sign-confusion / no-addend / wrong-half / truncating-add refute
        // controls).
        NeonUaddwV,
        NeonUaddw2V,
        // SIGNED widening add-wide (SADDW/SADDW2, emitted by the neon_predsum
        // widening i64-accumulator condsum for `s(i64) += (a_i32[iv] as i64)
        // [if pred]` — the three-operand signed wide add that replaces the
        // SMLAL-by-ones MAC); credited via their FAITHFUL D-pair obligations
        // (all_neon_saddw_proofs, one per opcode, both `.2D` lanes
        // concatenated; zext-confusion [SADDW-as-UADDW] / no-addend /
        // wrong-half / truncating-add refute controls).
        NeonSaddwV,
        NeonSaddw2V,
        // Vector multiply-accumulate (MLA.4S, emitted by the neon_predsum
        // MLA-by-mask condsum accumulate for the Gpr32 `.4S` masked-add —
        // `MLA(acc, a, mask)` accumulates the NEGATED predicated sum, folded
        // by one wrapping SubRR at the drain); credited via its FAITHFUL
        // D-pair obligation (all_neon_mla_proofs, all four `.4S` lanes
        // concatenated; MLS-confusion / MUL-no-accumulate / lane-swap refute
        // controls).
        NeonMlaV,
        // Pairwise widening accumulate (UADALP .4S -> .2D, emitted by the
        // neon_array widening abs-sum vectorizer TRACK D for `s(i64) +=
        // zext64(abs_bits(a_i32[i] [+ inv]))`, replacing the UADDW/UADDW2
        // pair — a pure mod-2^64 reassociation under the both-lanes drain);
        // credited via its FAITHFUL D-pair obligation (all_neon_uadalp_proofs,
        // both `.2D` lanes concatenated; SADALP-sign-confusion /
        // UADDLP-no-accumulate / wrong-pairing refute controls).
        NeonUadalpV,
        NeonLd1Post,
        NeonSt1Post,
        // LDP Q-pair post-index load (emitted by the NEON reduction/map
        // vectorizers' LOAD-PATH rework); allowlisted under the same SHARED
        // whole-backend unfaithful-load debt as NeonLd1Post/NeonSt1Post.
        NeonLdpQPost,
        // STP Q-pair post-index store (emitted by the NEON map/stencil/fmap
        // vectorizers' STORE-PATH pairing rework); allowlisted under the same
        // SHARED whole-backend unfaithful-STORE debt as NeonSt1Post — the STORE
        // sibling of NeonLdpQPost.
        NeonStpQPost,
        // Pseudo / trap
        Phi,
        StackAlloc,
        Copy,
        Nop,
        // Emission-time loop-head alignment padding (encodes to the
        // architectural NOP 0xD503201F). FailClosedAllowlisted: no value
        // semantics to prove; byte-exactness is covered by the A64 decode-check
        // and offset integrity by the EH offset cross-check. Created only at
        // emission by loop_align, never selected by the lowerer.
        AlignNop,
        Retain,
        Release,
        Brk,
        TrapOverflow,
        TrapBoundsCheck,
        TrapBoundsCheckExact,
        TrapNull,
        TrapNullIfZero,
        TrapDivZero,
        TrapDivZeroIfZero,
        TrapShiftRange,
        TrapShiftRangeIfOOB,
        TrapOverflowExact,
    ]
};

/// Every `X86Opcode` variant. Source of truth: `crates/trust-cg-ir/src/x86_64_ops.rs`.
pub const ALL_X86_OPCODES: &[X86Opcode] = {
    use X86Opcode::*;
    &[
        // Arithmetic
        AddRR,
        AddRI,
        AddRM,
        SubRR,
        SubRI,
        SubRM,
        ImulRR,
        ImulRRI,
        ImulRM,
        Idiv,
        Div,
        Neg,
        Inc,
        Dec,
        Cdq,
        Cqo,
        Mul,
        AdcRR,
        SbbRR,
        // Logical
        AndRR,
        AndRI,
        OrRR,
        OrRI,
        XorRR,
        XorRI,
        Not,
        // Shifts
        ShlRR,
        ShlRI,
        ShrRR,
        ShrRI,
        SarRR,
        SarRI,
        RolRI,
        // Move
        MovRR,
        MovRI,
        MovRM8,
        MovRM16,
        MovRM32,
        MovRM,
        MovMR8,
        MovMR16,
        MovMR32,
        MovMR,
        VolatileMovRM8,
        VolatileMovRM16,
        VolatileMovRM32,
        VolatileMovRM,
        VolatileMovMR8,
        VolatileMovMR16,
        VolatileMovMR32,
        VolatileMovMR,
        VolatileMovssRM,
        VolatileMovssMR,
        VolatileMovsdRM,
        VolatileMovsdMR,
        VolatileMovdquRM,
        VolatileMovdquMR,
        VolatileMovdqaRM,
        VolatileMovdqaMR,
        Movzx,
        MovzxW,
        MovsxB,
        MovsxW,
        Movsx,
        MovRR32,
        MovRipRel,
        MovRipRelTlv,
        Lea,
        LeaSib,
        LeaRip,
        MovRMSib,
        MovMRSib,
        MovRM8Sib,
        MovMR8Sib,
        MovsxdRMSib,
        MovsdRMSib,
        MovssRMSib,
        // Compare / test
        CmpRR,
        CmpRI,
        CmpRI8,
        CmpRM,
        TestRR,
        TestRI,
        TestRM,
        // Branch / control
        Jmp,
        JmpR,
        Jcc,
        Call,
        CallR,
        CallM,
        Ret,
        // SSE scalar double
        Addsd,
        Subsd,
        Mulsd,
        Divsd,
        Sqrtsd,
        Roundsd,
        Andpd,
        MovsdRR,
        MovsdRM,
        MovsdMR,
        Ucomisd,
        MovdquRM,
        MovdquMR,
        MovsdRipRel,
        Minsd,
        Maxsd,
        Cmpsd,
        // SSE scalar single
        Addss,
        Subss,
        Mulss,
        Divss,
        Sqrtss,
        Roundss,
        Andps,
        MovssRR,
        MovssRM,
        MovssMR,
        Ucomiss,
        MovssRipRel,
        Minss,
        Maxss,
        Cmpss,
        // Conditional move/set
        Cmovcc,
        Setcc,
        Cmovcc32,
        // Conversions
        Cvtsi2sd,
        Cvtsd2si,
        Cvtsi2ss,
        Cvtss2si,
        Cvtsd2ss,
        Cvtss2sd,
        Cvttsd2si,
        Cvttss2si,
        // Bit manipulation
        Bsf,
        Bsr,
        Tzcnt,
        Lzcnt,
        Popcnt,
        BtRI,
        Bswap,
        // Atomic / exchange / fence
        Xchg,
        Cmpxchg,
        Cmpxchg8,
        Cmpxchg16,
        Mfence,
        AtomicRmwCasLoop,
        AtomicRmwCasLoop8,
        AtomicRmwCasLoop16,
        // GPR <-> XMM
        MovdToXmm,
        MovdFromXmm,
        MovqToXmm,
        MovqFromXmm,
        // Stack
        Push,
        Pop,
        // SSE packed FP
        Addps,
        Subps,
        Mulps,
        Divps,
        Addpd,
        Subpd,
        Mulpd,
        Divpd,
        // SSE2 packed integer
        Pand,
        Pandn,
        Por,
        Pxor,
        Pcmpeqd,
        Pshufd,
        Pmovmskb,
        MovdqaRR,
        Pcmpgtd,
        MovdqaRM,
        MovdqaMR,
        Paddd,
        Psubd,
        Punpckldq,
        Punpcklqdq,
        Paddq,
        Psubq,
        Paddb,
        Paddw,
        Psubb,
        Psubw,
        // SSE4.1 lane insert/extract + vector pseudos
        Pinsrd,
        Pextrd,
        V4I32MaskExtract,
        Pmulld,
        Pcmpeqq,
        Pcmpgtq,
        Ptest,
        Pinsrq,
        Pextrq,
        V2I64MaskExtract,
        Pblendvb,
        V128BoolSelect,
        Pmuludq,
        Pmullw,
        Pcmpeqb,
        Pcmpeqw,
        Pcmpgtb,
        Pcmpgtw,
        V16I8MaskExtract,
        V8I16MaskExtract,
        Pslld,
        Psrld,
        Psrad,
        Psllq,
        Psrlq,
        Punpcklbw,
        Punpckhbw,
        Packuswb,
        Psadbw,
        ImulRMSib,
        MovRM32Sib,
        MovMR32Sib,
        // Pseudo / trap / pad
        TrapBoundsCheckExact,
        TrapNullIfZeroExact,
        TrapDivZeroExact,
        TrapShiftRangeExact,
        Phi,
        StackAlloc,
        Nop,
        NopMulti,
        Ud2,
    ]
};

/// Every `RiscVOpcode` variant. Source of truth: `crates/trust-cg-ir/src/riscv_ops.rs`.
///
/// Listed in the enum's declaration order. The wildcard-free `classify_riscv`
/// match forces a new variant to be classified at compile time; the universe
/// test's independent source-declaration comparison forces it to be enumerated
/// here too. The numeric pin is a release baseline, not the completeness oracle.
pub const ALL_RISCV_OPCODES: &[RiscVOpcode] = {
    use RiscVOpcode::*;
    &[
        // RV64I: Integer Register-Register
        Add,
        Sub,
        And,
        Or,
        Xor,
        Sll,
        Srl,
        Sra,
        Slt,
        Sltu,
        // RV64I: Integer Register-Immediate
        Addi,
        Andi,
        Ori,
        Xori,
        Slti,
        Sltiu,
        Slli,
        Srli,
        Srai,
        // RV64I: Upper Immediate
        Lui,
        Auipc,
        // RV64I: Word (32-bit) operations on RV64
        Addw,
        Subw,
        Sllw,
        Srlw,
        Sraw,
        Addiw,
        Slliw,
        Srliw,
        Sraiw,
        // RV64I: Load
        Lb,
        Lh,
        Lw,
        Ld,
        Lbu,
        Lhu,
        Lwu,
        // RV64I: Store
        Sb,
        Sh,
        Sw,
        Sd,
        // RV64I: Branch
        Beq,
        Bne,
        Blt,
        Bge,
        Bltu,
        Bgeu,
        // RV64I: Jump
        Jal,
        Jalr,
        // RV64M: Multiply / Divide
        Mul,
        Mulh,
        Mulhsu,
        Mulhu,
        Div,
        Divu,
        Rem,
        Remu,
        // RV64M: Word multiply/divide
        Mulw,
        Divw,
        Divuw,
        Remw,
        Remuw,
        // RV64D: Double-Precision Floating-Point
        FaddD,
        FsubD,
        FmulD,
        FdivD,
        FsqrtD,
        Fld,
        Fsd,
        FeqD,
        FltD,
        FleD,
        FcvtDW,
        FcvtWD,
        FcvtDL,
        FcvtLD,
        FmvXD,
        FmvDX,
        // System / trap
        Ebreak,
        // Pseudo-instructions
        Phi,
        StackAlloc,
        Nop,
        // Proof-only guard carrier
        TrapBoundsCheckExact,
    ]
};

/// Every `WasmOpcode` variant. Source of truth: `crates/trust-cg-ir/src/wasm_ops.rs`.
///
/// Listed in the enum's declaration order. The wildcard-free `classify_wasm`
/// match forces a new variant to be classified at compile time; the universe
/// test's independent source-declaration comparison forces it to be enumerated
/// here too. The numeric pin is a release baseline, not the completeness oracle.
pub const ALL_WASM_OPCODES: &[WasmOpcode] = {
    use WasmOpcode::*;
    &[
        // Integer ALU (i32 / i64)
        I32Add,
        I64Add,
        I32Sub,
        I64Sub,
        I32Mul,
        I64Mul,
        I32DivS,
        I64DivS,
        I32DivU,
        I64DivU,
        I32RemS,
        I64RemS,
        I32RemU,
        I64RemU,
        I32And,
        I64And,
        I32Or,
        I64Or,
        I32Xor,
        I64Xor,
        I32Shl,
        I64Shl,
        I32ShrS,
        I64ShrS,
        I32ShrU,
        I64ShrU,
        I32Popcnt,
        I64Popcnt,
        // Integer comparisons
        I32Eq,
        I64Eq,
        I32Ne,
        I64Ne,
        I32LtS,
        I64LtS,
        I32LtU,
        I64LtU,
        I32GtS,
        I64GtS,
        I32GtU,
        I64GtU,
        I32LeS,
        I64LeS,
        I32LeU,
        I64LeU,
        I32GeS,
        I64GeS,
        I32GeU,
        I64GeU,
        // FP arithmetic
        F32Add,
        F64Add,
        F32Sub,
        F64Sub,
        F32Mul,
        F64Mul,
        F32Div,
        F64Div,
        F32Min,
        F64Min,
        F32Max,
        F64Max,
        // FP comparisons
        F32Eq,
        F64Eq,
        F32Ne,
        F64Ne,
        F32Lt,
        F64Lt,
        F32Gt,
        F64Gt,
        F32Le,
        F64Le,
        F32Ge,
        F64Ge,
        // FP unary
        F32Abs,
        F64Abs,
        F32Neg,
        F64Neg,
        F32Sqrt,
        F64Sqrt,
        F32Ceil,
        F64Ceil,
        F32Floor,
        F64Floor,
        F32Trunc,
        F64Trunc,
        // Width / format casts
        I32WrapI64,
        I64ExtendI32S,
        I64ExtendI32U,
        F32DemoteF64,
        F64PromoteF32,
        F32ConvertI32S,
        F32ConvertI32U,
        F32ConvertI64S,
        F32ConvertI64U,
        F64ConvertI32S,
        F64ConvertI32U,
        F64ConvertI64S,
        F64ConvertI64U,
        I32ReinterpretF32,
        I64ReinterpretF64,
        F32ReinterpretI32,
        F64ReinterpretI64,
        I32TruncSatF32S,
        I32TruncSatF32U,
        I32TruncSatF64S,
        I32TruncSatF64U,
        I64TruncSatF32S,
        I64TruncSatF32U,
        I64TruncSatF64S,
        I64TruncSatF64U,
        // Constants
        I32Const,
        I64Const,
        // Locals / globals
        LocalGet,
        LocalSet,
        LocalTee,
        GlobalGet,
        GlobalSet,
        // Linear memory
        I32Load,
        I64Load,
        I32Store,
        I64Store,
        // Structured control flow
        Unreachable,
        Nop,
        Block,
        Loop,
        If,
        Else,
        End,
        Br,
        BrIf,
        BrTable,
        Return,
        Drop,
        // Calls
        Call,
        CallIndirect,
        // SIMD / v128 (deferred)
        V128Load,
        V128Store,
        V128Const,
        I32x4Add,
        I32x4Mul,
        F32x4Add,
        F32x4Mul,
    ]
};
