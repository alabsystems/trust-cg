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
//! # Not instruction credit (E0.2)
//!
//! The gate and the per-instruction verifiers no longer share a definition of
//! credit. A row here is still covered when a registry theorem found by name
//! (`name.contains(query)` in `discharge_one`) discharges, or when a
//! REPRESENTATIVE reconstructed obligation discharges, by sampling included.
//! Since E0.2 the function verifiers credit neither: a theorem selected by name
//! is reported as a registry name lookup, and a sampled discharge is reported
//! with its sample count, both `Unverified`. The gate keeps its own rule because
//! it answers a different question — does every emittable opcode have an
//! accepted obligation to aim at, or a named RED deferral — and because nothing
//! that decides promotion reads it: no crate outside `trust-cg-verify` uses it
//! as code, pinned by `coverage_gate_is_not_consulted_by_any_promotion_crate` in
//! `tests/coverage_gate_tests.rs`. A covered row is therefore never evidence
//! that an emitted instance of that opcode is verified.
//!
//! Not every [`GateArch`] is keyed on an opcode enum. The WebAssembly lane also
//! inventories three MODULE-level evidence families whose unit has no enum
//! variant to hang a row on — [`GateArch::WasmValueDomain`] (keyed on the spec
//! opcode BYTE), [`GateArch::WasmCfgStructural`] (keyed on the anti-tautology
//! mutant), and [`GateArch::WasmAbi`] (keyed on the family's own obligations,
//! structural checks and byte-mutation guards). They obey exactly the same
//! rules: credit needs live discharge, and a family that cannot honestly speak
//! registers a NAMED DEFERRAL that stays RED IN the denominator rather than
//! being allowlisted out or given a weak obligation.
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
    /// WebAssembly P3 **VALUE DOMAIN** — the sub-word / FP linear-memory
    /// accesses (spec §5.4.4, bytes 0x28..=0x40), the sign-extension operators
    /// (§5.4.6, 0xc0..=0xc4), and the named deferrals (`br_table`,
    /// `memory.size`/`memory.grow`, data segments).
    ///
    /// A SEPARATE arch rather than more [`GateArch::Wasm`] rows because this
    /// inventory is keyed on the SPEC OPCODE BYTE: `trust_cg_ir::WasmOpcode`
    /// enumerates only the two full-width integer load/store pairs, so the
    /// sub-word and FP accesses have no enum variant to hang a row on. Keying on
    /// the byte is not a workaround — the byte is what the backend emits and
    /// what the verifier decodes, and it keeps the P3 surface COUNTED from the
    /// moment the obligations exist instead of waiting on an enum to catch up.
    /// The 12 `i64` sub-word / sign-extension bytes the lowerer never selects
    /// are rows too, excluded as never selected with their reason, so the
    /// credited denominator is exactly the emitted surface. When `WasmOpcode`
    /// grows the variants these rows merge into [`GateArch::Wasm`] unchanged.
    WasmValueDomain,
    /// WebAssembly P4 **CFG STRUCTURAL** family (`crate::wasm_cfg_proofs`) — the
    /// per-compile necessary condition on the relooper's output: label liveness,
    /// branch operand discipline, `br_table` uniformity, join heights and types,
    /// bracket structure, and function-label arity.
    ///
    /// A SEPARATE arch for the same reason [`GateArch::WasmValueDomain`] is one:
    /// the unit is not a `WasmOpcode` variant but a MODULE-level property, so
    /// there is no enum row to hang it on. The credit unit here is the family's
    /// ANTI-TAUTOLOGY MUTANT — a deliberately-wrong module the checker must
    /// refute — plus the reference module the checker must accept. The seven
    /// invariant STATEMENTS are listed as excluded rows pointing at those mutant
    /// rows, so a statement is never counted as its own evidence, and the five
    /// named deferrals (relooper bisimulation first among them) plus the two
    /// measured blind spots stay RED IN the denominator.
    WasmCfgStructural,
    /// WebAssembly P4 **MEMORY / CALL-ABI** families (`crate::wasm_abi_proofs`) —
    /// shadow-stack frame refinement (family 2) and the call / table ABI
    /// discipline (family 3), over a corpus of REAL emitted module bytes.
    ///
    /// Rows are the family's own units: one per reconstructed SMT frame
    /// obligation, one per decidable structural check over the decoded module,
    /// one per anti-tautology byte-mutation guard, one per fail-closed refusal,
    /// and one per named deferral. The nine deferrals — five of which are the
    /// HOST's under `crates/trust-cg-codegen/src/wasm/OWNERSHIP.md` — stay RED IN
    /// the denominator, never allowlisted out.
    WasmAbi,
}

impl std::fmt::Display for GateArch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GateArch::AArch64 => f.write_str("aarch64"),
            GateArch::X86_64 => f.write_str("x86_64"),
            GateArch::RiscV => f.write_str("riscv"),
            GateArch::Wasm => f.write_str("wasm"),
            GateArch::WasmValueDomain => f.write_str("wasm-value-domain"),
            GateArch::WasmCfgStructural => f.write_str("wasm-cfg-structural"),
            GateArch::WasmAbi => f.write_str("wasm-abi"),
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

/// The `x86_64::MovRI` audit row for a given credit-hook RESULT.
///
/// `Ok` credits the row, and the note names the evidence and its non-claim. `Err`
/// is a REGRESSION and yields `ProofNotDischarged`, so the row counts as a
/// failure and leaves `covered_count`. It is deliberately NOT a
/// `DeferredUnfaithfulModel`: the tests that require every x86 RED row to be
/// named deferral debt then fail loudly instead of absorbing it.
/// `coverage_gate_tests` feeds this function, and the whole report, an `Err`.
pub fn x86_movri_audit_row(
    opcode_display: String,
    credit: Result<crate::x86_encoding_proofs::MovImmCredit, String>,
) -> OpcodeAuditRow {
    match credit {
        Ok(credit) => OpcodeAuditRow {
            opcode_display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: None,
            note: format!(
                "DECODED from the real emitted MOV r,imm bytes with an INDEPENDENT SDM-derived \
                 decoder (x86_encoding_proofs): {} captured encodings across {} physical forms \
                 denote their intended 64-bit register write; {} mutants REFUTE. Says nothing \
                 about whether the LOWERING chose the right constant.",
                credit.entries, credit.forms_seen, credit.mutants_refuted
            ),
        },
        Err(why) => OpcodeAuditRow {
            opcode_display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: Some(CoverageFinding::ProofNotDischarged {
                proof_name: "x86_encoding: MOV r,imm emitted bytes denote the intended register \
                             write"
                    .to_string(),
                detail: why,
            }),
            note: "MOV r,imm byte obligation did NOT discharge — a regression, not a deferral"
                .to_string(),
        },
    }
}

/// The gate row for one of the ten SSE lane opcodes.
///
/// `Ok` is a GREEN row whose note states the evidence and its limits; `Err` is
/// `ProofNotDischarged`, never a deferral, so a hook that stops discharging
/// fails the tests that require every x86 RED row to be named deferral debt.
pub fn x86_sse_lane_audit_row(
    opcode_display: String,
    row: crate::x86_sse_lane_proofs::SseLaneOp,
    credit: Result<crate::x86_sse_lane_proofs::SseLaneCredit, String>,
) -> OpcodeAuditRow {
    use crate::x86_sse_lane_proofs::SseLaneOp;
    match credit {
        Ok(c) => {
            let facet = match row {
                SseLaneOp::Ptest => format!(
                    "the six status flags agree with an independently stated whole-128-bit                      intent on {} witnesses (EVALUATION, exhaustive over the structured                      families and statistical beyond them)",
                    c.ptest_witnesses
                ),
                SseLaneOp::Packuswb => format!(
                    "the lane pack is an exact bit routing and the unsigned-saturating narrow                      agrees with an independently stated bit-pattern model on all {} inputs                      (EXHAUSTIVE)",
                    c.saturation_cases
                ),
                SseLaneOp::MovdqaRR => "the bytes denote the FULL-WIDTH 128-bit copy with the                                         intended direction and registers; it does NOT claim                                         MOVDQA differs from MOVDQU in value, and the two                                         sides of the ROUTING comparison are the SAME                                         construction for a copy, so what this row decides                                         is the mnemonic and direction, the destination, the                                         width and the operand identity — each with a                                         refuting control, and the bit table anchored by a                                         real MOVDQA on silicon"
                    .to_string(),
                SseLaneOp::Pmovmskb => "the sixteen sign bits are gathered in lane order into the                                         GPR ROOT, upper bits ZEROED (Vol 1 3.4.1.1); as for                                         MOVDQA the two sides state that gather the same                                         way, so the bit-for-bit comparison is backed by the                                         four wrong-mask controls and by _mm_movemask_epi8                                         on silicon rather than by two independent                                         formulations"
                    .to_string(),
                _ => "every result bit is routed from the same operand bit on both sides — an                       exact decision over all inputs, not a sample"
                    .to_string(),
            };
            OpcodeAuditRow {
                opcode_display,
                class: OpcodeClass::EmittableNeedsProof,
                finding: None,
                note: format!(
                    "DECODED from the real emitted bytes with an INDEPENDENT SDM-derived decoder                      and compared against a parametric statement of the machine-IR intent                      (x86_sse_lane_proofs): {facet}. Across the family, {} captured encodings                      ({} register-register, {} folded xmm,m128) over {} rows hold, {} bits were                      compared exactly, and {} byte mutants plus {} wrong-model controls REFUTE —                      every one of them through the obligation's own comparison and for the                      reason class it declares, per row, with an unbuildable model counted as                      a battery defect rather than as a refutation. The corpus is register-SPARSE                      and this credit quantifies over the captured encodings only; the full                      16x16 register sweep, the 256-immediate sweep, the live re-encode and the                      native-silicon differential run in x86_sse_lane_gate. Says nothing about                      whether instruction selection chose the right instruction, permutation,                      mask or operands, and for PSHUFD nothing about how isel PACKS the ORDER                      fields.",
                    c.entries,
                    c.register_forms,
                    c.memory_forms,
                    c.rows_covered,
                    c.bits_compared,
                    c.byte_mutants_refuted,
                    c.model_controls_refuted,
                ),
            }
        }
        Err(why) => OpcodeAuditRow {
            opcode_display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: Some(CoverageFinding::ProofNotDischarged {
                proof_name: "x86_sse_lane: emitted SSE lane bytes denote the intended routing"
                    .to_string(),
                detail: why,
            }),
            note: "the SSE lane obligation did NOT discharge — a regression, not a deferral"
                .to_string(),
        },
    }
}

/// The `x86_64::MovsxdRMSib` audit row for a given credit-hook RESULT.
///
/// `Ok` credits the row, and the note names the evidence AND the thing a reader
/// must not read into it: nothing emits this opcode. `Err` is a REGRESSION and
/// yields `ProofNotDischarged`, deliberately NOT a `DeferredUnfaithfulModel`, so
/// the tests that require every x86 RED row to be named deferral debt fail
/// loudly instead of absorbing it.
pub fn x86_movsxd_sib_audit_row(
    opcode_display: String,
    credit: Result<crate::x86_movsxd_sib_proofs::MovsxdSibCredit, String>,
) -> OpcodeAuditRow {
    match credit {
        Ok(c) => OpcodeAuditRow {
            opcode_display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: None,
            note: format!(
                "DECODED from the real emitted MOVSXD-SIB bytes with an INDEPENDENT SDM-derived \
                 decoder and compared against a parametric statement of the machine-IR intent \
                 (x86_movsxd_sib_proofs): {} captured encodings covering {} encoding facets \
                 denote the intended 64-bit destination write — a 32-bit SIGNED load at \
                 base+index*entry_size+disp. The two sides are structurally distinct (a SHIFT by \
                 the raw SIB scale field against a MULTIPLY by the entry size; an explicit \
                 sign-extend against a signed load), the ADDRESS facet is exact for every 64-bit \
                 base and index, and the VALUE facet is decided over {} witness comparisons whose \
                 family must exercise both sign cases. {} byte/source controls, {} wrong-model \
                 controls run THROUGH the comparison itself (including a machine side spelled \
                 exactly like the source side, which the comparison must REFUSE as a vacuous \
                 self-equality rather than credit) and {} \
                 hand-written SDM decoder controls all REFUTE for the reason class they declare, \
                 with {} SDM vectors the encoder never emits still HOLDING and an unbuildable \
                 control counted as a battery defect rather than a refutation. {} write-mask \
                 vectors decide the SDM Vol 1 3.4.1.1 DESTINATION WIDTH rule over every \
                 production in the decoder's language — not only the 64-bit one this family's \
                 Extension facet lets through — and {} vacuity controls give the anti-vacuity \
                 guard teeth in both directions; both rules, and the SDM rule that REX.B does not \
                 create a base register (decoder controls D1b/D1c and D4b/D4c), were otherwise \
                 asserted only in prose. NOTHING EMITS THIS \
                 OPCODE — the active jump-table path uses 8-byte deltas through MovRMSib — so no \
                 runtime claim follows, and this says nothing about whether instruction selection \
                 would choose the right table, selector, entry size or displacement.",
                c.entries,
                c.facets_seen,
                c.witness_comparisons,
                c.controls_refuted,
                c.model_controls_refuted,
                c.decoder_controls_refuted,
                c.hand_vectors_held,
                c.write_mask_vectors_checked,
                c.vacuity_controls_refuted,
            ),
        },
        Err(why) => OpcodeAuditRow {
            opcode_display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: Some(CoverageFinding::ProofNotDischarged {
                proof_name: "x86_movsxd_sib: emitted MOVSXD-SIB bytes denote the intended scaled \
                             sign-extending load"
                    .to_string(),
                detail: why,
            }),
            note: "the scaled sign-extending load obligation did NOT discharge — a regression, \
                   not a deferral"
                .to_string(),
        },
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
            GateArch::WasmValueDomain => self.audit_wasm_value_domain_rows(),
            GateArch::WasmCfgStructural => self.audit_wasm_cfg_rows(),
            GateArch::WasmAbi => self.audit_wasm_abi_rows(),
        };
        CoverageReport { arch, rows }
    }

    // -- AArch64 ----------------------------------------------------------

    fn audit_aarch64(&self, opcode: AArch64Opcode) -> OpcodeAuditRow {
        self.audit_aarch64_with(
            opcode,
            &AArch64AuditHooks {
                value_credit: &crate::aarch64_value_decode_proofs::a64_value_credit,
                volatile_credit: &crate::volatile_access_preservation::volatile_preservation_credit,
                plain_row: None,
                checked_mul_i128_credit: &crate::checked_mul_i128_proofs::checked_mul_i128_credit,
                bound_memory_credit: &real_bound_memory_credit,
            },
        )
    }

    /// The AArch64 audit with the volatile-row hooks INJECTED (X-OPCODES-P6).
    ///
    /// A volatile access row is credited only when BOTH facets hold: the
    /// volatile-access preservation hook accepts, and its plain counterpart's
    /// row (the dereference/value or memory-effect evidence) is covered.
    /// [`CoverageGate::audit`] passes the real
    /// `volatile_access_preservation::volatile_preservation_credit` and audits
    /// the real plain row. This seam lets a test hand the gate a failing
    /// preservation hook, or a plain row as it would read once the plain
    /// memory model is credited, and watch the six volatile rows follow.
    #[doc(hidden)]
    pub fn audit_aarch64_with_volatile_hooks(
        &self,
        volatile_credit: &dyn Fn() -> Result<
            crate::volatile_access_preservation::VolatilePreservationCredit,
            String,
        >,
        plain_row: Option<&dyn Fn(AArch64Opcode) -> OpcodeAuditRow>,
    ) -> CoverageReport {
        let hooks = AArch64AuditHooks {
            value_credit: &crate::aarch64_value_decode_proofs::a64_value_credit,
            volatile_credit,
            plain_row,
            checked_mul_i128_credit: &crate::checked_mul_i128_proofs::checked_mul_i128_credit,
            bound_memory_credit: &real_bound_memory_credit,
        };
        CoverageReport {
            arch: GateArch::AArch64,
            rows: ALL_AARCH64_OPCODES
                .iter()
                .map(|&op| self.audit_aarch64_with(op, &hooks))
                .collect(),
        }
    }

    /// The AArch64 audit with the decoded-value credit hook INJECTED.
    ///
    /// [`CoverageGate::audit`] always passes the real
    /// `aarch64_value_decode_proofs::a64_value_credit`. This seam lets a test
    /// hand the gate a FAILING hook and watch every decoded-value row leave the
    /// covered count as `ProofNotDischarged`, so the hook-failure arm runs with
    /// a real `Err` rather than being assumed.
    #[doc(hidden)]
    pub fn audit_aarch64_with_value_credit(
        &self,
        credit: &dyn Fn(
            AArch64Opcode,
        )
            -> Result<crate::aarch64_value_decode_proofs::A64ValueCredit, String>,
    ) -> CoverageReport {
        let hooks = AArch64AuditHooks {
            value_credit: credit,
            volatile_credit: &crate::volatile_access_preservation::volatile_preservation_credit,
            plain_row: None,
            checked_mul_i128_credit: &crate::checked_mul_i128_proofs::checked_mul_i128_credit,
            bound_memory_credit: &real_bound_memory_credit,
        };
        CoverageReport {
            arch: GateArch::AArch64,
            rows: ALL_AARCH64_OPCODES
                .iter()
                .map(|&op| self.audit_aarch64_with(op, &hooks))
                .collect(),
        }
    }

    /// The AArch64 audit with the i128 checked-multiply credit hook INJECTED.
    ///
    /// [`CoverageGate::audit`] always passes the real
    /// `checked_mul_i128_proofs::checked_mul_i128_credit`. This seam lets a
    /// test hand the gate a FAILING hook and watch the `Umulh` row leave the
    /// covered count as `ProofNotDischarged`, so the hook-failure arm runs
    /// with a real `Err` rather than being assumed.
    #[doc(hidden)]
    pub fn audit_aarch64_with_checked_mul_i128_credit(
        &self,
        credit: &dyn Fn() -> Result<crate::checked_mul_i128_proofs::CheckedMulI128Credit, String>,
    ) -> CoverageReport {
        let hooks = AArch64AuditHooks {
            value_credit: &crate::aarch64_value_decode_proofs::a64_value_credit,
            volatile_credit: &crate::volatile_access_preservation::volatile_preservation_credit,
            plain_row: None,
            checked_mul_i128_credit: credit,
            bound_memory_credit: &real_bound_memory_credit,
        };
        CoverageReport {
            arch: GateArch::AArch64,
            rows: ALL_AARCH64_OPCODES
                .iter()
                .map(|&op| self.audit_aarch64_with(op, &hooks))
                .collect(),
        }
    }

    /// The AArch64 audit with the bound-memory row credit hook INJECTED.
    ///
    /// [`CoverageGate::audit`] always passes the real
    /// `bound_memory_row_credit::{atomic,scalar,pair}_row_credit`. This
    /// seam lets a test hand the gate a failing hook and watch every
    /// bound-memory row (and the volatile rows that follow a plain one) leave
    /// the covered count.
    #[doc(hidden)]
    pub fn audit_aarch64_with_bound_memory_credit(
        &self,
        credit: &BoundMemoryCreditHook,
    ) -> CoverageReport {
        let hooks = AArch64AuditHooks {
            value_credit: &crate::aarch64_value_decode_proofs::a64_value_credit,
            volatile_credit: &crate::volatile_access_preservation::volatile_preservation_credit,
            plain_row: None,
            checked_mul_i128_credit: &crate::checked_mul_i128_proofs::checked_mul_i128_credit,
            bound_memory_credit: credit,
        };
        CoverageReport {
            arch: GateArch::AArch64,
            rows: ALL_AARCH64_OPCODES
                .iter()
                .map(|&op| self.audit_aarch64_with(op, &hooks))
                .collect(),
        }
    }

    fn audit_aarch64_with(
        &self,
        opcode: AArch64Opcode,
        hooks: &AArch64AuditHooks<'_>,
    ) -> OpcodeAuditRow {
        with_named_fp_ieee_evidence(opcode, self.audit_aarch64_row(opcode, hooks))
    }

    fn audit_aarch64_row(
        &self,
        opcode: AArch64Opcode,
        hooks: &AArch64AuditHooks<'_>,
    ) -> OpcodeAuditRow {
        let value_credit = hooks.value_credit;
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
                // fake-covered). This is the gate's own rule, not the function
                // verifier's: the walk credits a reconstruction only with
                // complete (Exhaustive/Formal) evidence for the instruction's
                // own operands, and reports a sampled one uncredited (E0.2).
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
                // This opcode inventory requires both width models where one
                // opcode has S/D or W/X forms. It has no concrete instruction or
                // source operands: passing model checks is not runtime evidence
                // of their applicability. In particular, FCSEL remains here as
                // diagnostic model coverage while FunctionVerifier refuses its
                // opcode-only attribution. Matching is case-insensitive.
                if let Some(queries) = aarch64_width_polymorphic_proofs(opcode) {
                    return self.check_all_queries(display, queries, MatchCase::Insensitive);
                }
                // MOVK/MOVN are polymorphic over (width, halfword shift), which
                // the opcode does not name. Demand one discharged proof per
                // legal form — exactly the per-form obligations the function
                // verifier binds — and fail closed on an incomplete table.
                if let Some(forms) = aarch64_form_polymorphic_proofs(opcode) {
                    return self.check_all_forms(display, forms);
                }
                // Register copies and scalar value forms credited by decoded-word
                // obligations: the Arm ARM semantics of the independently decoded
                // word the encoder emits, against the machine-IR intent. The hook
                // refuses unless every captured word holds and EVERY negative
                // control is refuted for its stated reason; each form's registered
                // obligation must then exist and discharge like any other query.
                // A failing hook is a REGRESSION and surfaces as
                // `ProofNotDischarged`, never as a quiet deferral.
                if let Some(forms) = crate::aarch64_value_decode_proofs::a64_value_forms(opcode) {
                    let row = self.check_a64_value_row(display, opcode, forms, value_credit);
                    if opcode == AArch64Opcode::NeonOrrV && row.finding.is_none() {
                        // ORR (vector) has two bound shapes: the register copy
                        // (its decoded-word form, above) and the three-register
                        // 16B OR, which the function verifier binds to the
                        // lanewise ORR obligation. Both must hold.
                        let query =
                            crate::aarch64_value_decode_proofs::neon_bitwise_16b_query(opcode)
                                .expect("ORR (vector) has a lanewise query");
                        return match self.discharge_one(
                            query,
                            crate::proof_database::ProofCategory::NeonLowering,
                            MatchCase::Insensitive,
                        ) {
                            Ok(note) => OpcodeAuditRow {
                                note: format!("{}; three-register 16B OR: {note}", row.note),
                                ..row
                            },
                            Err((finding, note)) => OpcodeAuditRow {
                                opcode_display: row.opcode_display,
                                class: OpcodeClass::EmittableNeedsProof,
                                finding: Some(finding),
                                note,
                            },
                        };
                    }
                    return row;
                }
                // NZCV producer/consumer rows (FCMP, CSET, CSEL, CSINC, CSNEG):
                // every per-instruction form the function verifier binds must
                // exist and discharge, and the credit hook must hold (captured
                // words decode back, every own form agrees on the boundary
                // battery, every negative control refutes). A failing hook or
                // form is a REGRESSION, reported as `ProofNotDischarged` /
                // `NoMatchingProof`, never as a quiet deferral.
                if let Some(forms) =
                    crate::aarch64_flag_consumer_proofs::flag_consumer_forms(opcode)
                {
                    return self.check_flag_consumer_row(
                        display,
                        opcode,
                        &forms,
                        &crate::aarch64_flag_consumer_proofs::flag_consumer_credit,
                    );
                }
                // SUBS #imm (L04-P1): both widths' decoded words must write
                // the operands' difference and comparison flags for every
                // register value (decided in process, bit-serial) and every
                // corruption control must refute. A failing hook is a
                // REGRESSION.
                if opcode == AArch64Opcode::SubsRI {
                    return self.check_subs_imm_row(
                        display,
                        &crate::aarch64_subs_imm_proofs::subs_imm_credit,
                    );
                }
                // CRC32/CRC32C (L04-P1): every form's decoded word must hold
                // against the reflected-CRC intent for every register value
                // (decided in process over GF(2)) and every corruption
                // control must refute. A failing hook is a REGRESSION.
                if crate::aarch64_crc32_proofs::Crc32Form::from_opcode(opcode).is_some() {
                    return self.check_crc32_row(
                        display,
                        opcode,
                        &crate::aarch64_crc32_proofs::crc32_credit,
                    );
                }
                // Conditional trap carriers (L04-P12): every modeled form's
                // expansion words must trap exactly when the carrier's
                // condition holds (decided in process), and every corruption
                // control must refute. A failing hook is a REGRESSION.
                if crate::aarch64_trap_expansion::CONDITIONAL_TRAP_OPCODES.contains(&opcode) {
                    return self.check_trap_expansion_row(display, opcode);
                }
                // Volatile accesses (X-OPCODES-P6) need two facets: the
                // preservation of every volatile access, in order, on every
                // path from source to final stream (decided per compile by the
                // pipeline, credited here through its control battery), AND
                // the plain counterpart's dereference/value or memory-effect
                // evidence. A failing preservation hook is a regression
                // (`ProofNotDischarged`); an uncredited plain row keeps the
                // volatile row a named deferral.
                if let Some(plain) = aarch64_volatile_plain_counterpart(opcode) {
                    return self.check_volatile_row(display, opcode, plain, hooks);
                }
                // Bound-memory rows (L04-P1: scalar loads/stores and the 46
                // single-instruction atomics). The opcode authenticates nothing
                // by itself, so — as for MOVK/MOVN — EVERY legal form of the
                // opcode must carry the per-instruction authority of the
                // Formal-only rule: a replayed certificate of its form theorem,
                // representative instructions credited through clauses 2-4, and
                // every machine defect refuted (`bound_memory_row_credit`). A row
                // still in the deferred table below names debt the hook would
                // report too (`scalar_rows_need_every_form_judged_and_certified`);
                // any other failing hook is a REGRESSION (`ProofNotDischarged`).
                if aarch64_deferred_value_op_reason(opcode).is_none()
                    && let Some(credit) = (hooks.bound_memory_credit)(opcode)
                {
                    return check_bound_memory_row(display, opcode, credit);
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
                // UMULH (L04-P10): the 64-bit checked-umul obligation the
                // function verifier binds AND the i128 checked-multiply idiom
                // family, whose credit hook refuses unless every negative
                // control refutes.
                if opcode == AArch64Opcode::Umulh {
                    return self.check_umulh_row(display, hooks);
                }
                // NEON AND/EOR/BIC/NOT (ORR is above): the function verifier
                // binds each to its lanewise obligation per instruction, in the
                // 16B shape only, and refuses the 8B shapes; the row needs
                // that obligation.
                if let Some(query) =
                    crate::aarch64_value_decode_proofs::neon_bitwise_16b_query(opcode)
                {
                    return self.check_query(
                        display,
                        query,
                        ProofCategory::NeonLowering,
                        MatchCase::Insensitive,
                    );
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
                // The AArch64 query mapping is matched case-insensitively
                // (`name.to_lowercase().contains(query)`), as the verifier's
                // refusal text resolves it. The verifier credits no such match
                // (E0.2); this row records only that the named theorem discharges.
                self.check_query(display, query, category, MatchCase::Insensitive)
            }
        }
    }

    /// Audit one form-polymorphic AArch64 row against an INJECTED form table.
    ///
    /// [`CoverageGate::audit`] always uses [`aarch64_form_polymorphic_proofs`].
    /// This seam lets a test hand the gate an incomplete, duplicated,
    /// illegal-form or mis-queried table and watch the row turn RED, so the
    /// fail-closed arms of the form-completeness check are exercised rather
    /// than assumed.
    #[doc(hidden)]
    pub fn audit_aarch64_form_table(
        &self,
        opcode: AArch64Opcode,
        forms: &[FormProof],
    ) -> OpcodeAuditRow {
        self.check_all_forms(format!("AArch64::{opcode:?}"), forms)
    }

    // -- x86-64 -----------------------------------------------------------

    fn audit_x86(&self, opcode: X86Opcode) -> OpcodeAuditRow {
        self.audit_x86_with(opcode, &X86AuditHooks::REAL)
    }

    /// Every x86-64 row, audited against `hooks`.
    fn audit_x86_report(&self, hooks: &X86AuditHooks<'_>) -> CoverageReport {
        CoverageReport {
            arch: GateArch::X86_64,
            rows: ALL_X86_OPCODES
                .iter()
                .map(|&op| self.audit_x86_with(op, hooks))
                .collect(),
        }
    }

    /// The x86-64 audit with the MovRI credit hook's RESULT injected.
    ///
    /// [`CoverageGate::audit`] always passes the real
    /// `x86_encoding_proofs::mov_imm_discharges_valid`. This entry point exists
    /// so a test can hand the gate a FAILING hook result and watch the whole
    /// report change: `MovRI` must leave the covered count and appear among the
    /// failures as `ProofNotDischarged`. Before this seam existed, nothing ran
    /// the hook-failure arm with a real `Err`. Rewriting that arm to report no
    /// finding would have left every test green while a failing hook still
    /// counted as coverage.
    #[doc(hidden)]
    pub fn audit_x86_with_movri_credit(
        &self,
        credit: &Result<crate::x86_encoding_proofs::MovImmCredit, String>,
    ) -> CoverageReport {
        let hook = || credit.clone();
        self.audit_x86_report(&X86AuditHooks {
            movri_credit: &hook,
            ..X86AuditHooks::REAL
        })
    }

    /// The x86-64 audit with the SSE-lane credit hook's RESULT injected.
    ///
    /// The sibling of [`CoverageGate::audit_x86_with_movri_credit`], and it
    /// exists for the same reason: a test must be able to hand the gate a
    /// FAILING hook and watch all ten rows leave the covered count and appear
    /// among the failures as `ProofNotDischarged`. Without this seam nothing
    /// would ever run the hook-failure arm with a real `Err`, and rewriting that
    /// arm to report no finding would leave every test green while a failing
    /// hook still counted as coverage.
    #[doc(hidden)]
    pub fn audit_x86_with_sse_lane_credit(
        &self,
        credit: &Result<crate::x86_sse_lane_proofs::SseLaneCredit, String>,
    ) -> CoverageReport {
        let hook = || credit.clone();
        self.audit_x86_report(&X86AuditHooks {
            sse_lane_credit: &hook,
            ..X86AuditHooks::REAL
        })
    }

    /// The x86-64 audit with the MOVSXD-SIB credit hook's RESULT injected.
    ///
    /// The sibling of [`CoverageGate::audit_x86_with_movri_credit`] and
    /// [`CoverageGate::audit_x86_with_sse_lane_credit`], and it exists for the
    /// same reason: a test must be able to hand the gate a FAILING hook and
    /// watch `MovsxdRMSib` leave the covered count and appear among the failures
    /// as `ProofNotDischarged`. Without this seam nothing would ever run the
    /// hook-failure arm with a real `Err`, and rewriting that arm to report no
    /// finding would leave every test green while a failing hook still counted
    /// as coverage.
    #[doc(hidden)]
    pub fn audit_x86_with_movsxd_sib_credit(
        &self,
        credit: &Result<crate::x86_movsxd_sib_proofs::MovsxdSibCredit, String>,
    ) -> CoverageReport {
        let hook = || credit.clone();
        self.audit_x86_report(&X86AuditHooks {
            movsxd_sib_credit: &hook,
            ..X86AuditHooks::REAL
        })
    }

    /// The x86-64 audit with the ADDRESS credit hook's RESULT injected.
    ///
    /// The sibling of the three hooks above, and it exists for the same reason
    /// they do: without this seam nothing would ever run the credit path with a
    /// real `Err`, and a failing address lane could go on counting as coverage
    /// for all 56 rows it carries while no test noticed.
    #[doc(hidden)]
    pub fn audit_x86_with_address_credit(
        &self,
        credit: &Result<crate::x86_addressing_proofs::MemMovAddressCredit, String>,
    ) -> CoverageReport {
        let hook = || match credit {
            Ok(c) => Ok(*c),
            Err(e) => Err(e.clone()),
        };
        self.audit_x86_report(&X86AuditHooks {
            address_credit: &hook,
            ..X86AuditHooks::REAL
        })
    }

    /// The x86-64 audit with the VALUE leg and the volatile BOUNDARY leg
    /// injected.
    ///
    /// `value_credit` answers, per opcode, whether its reconstruction
    /// discharges; the ADDRESS row, the COMPARE-EXCHANGE joint row and the
    /// volatile JOINT row all require it (the real one is
    /// `x86_64_function_verifier::reconstruction_discharges_valid`).
    /// `trace_credit` is the RESULT of the `x86_volatile_trace` credit hook,
    /// which only the JOINT row requires. This seam is how a test shows that
    /// each leg is load-bearing: with the address lane still discharging, a
    /// failing VALUE or BOUNDARY leg must take its rows RED as
    /// `ProofNotDischarged`. Were a volatile row to stay green here, the address
    /// lane alone would be crediting it.
    #[doc(hidden)]
    pub fn audit_x86_with_value_and_trace_credit(
        &self,
        value_credit: &dyn Fn(X86Opcode, &VerificationConfig) -> bool,
        trace_credit: &Result<crate::x86_volatile_trace::VolatileTraceCredit, String>,
    ) -> CoverageReport {
        let hook = || trace_credit.clone();
        self.audit_x86_report(&X86AuditHooks {
            value_credit,
            volatile_trace_credit: &hook,
            ..X86AuditHooks::REAL
        })
    }

    fn audit_x86_with(&self, opcode: X86Opcode, hooks: &X86AuditHooks<'_>) -> OpcodeAuditRow {
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
                // precedes EVERY credit path below, reconstruction included, so
                // a row recorded here as debt cannot be credited by any of
                // them; promotion is an explicit removal from this table.
                if let Some(reason) = x86_deferred_value_op_reason(opcode) {
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: Some(CoverageFinding::DeferredUnfaithfulModel { reason }),
                        note: format!("HONESTLY DEFERRED (RED in denominator): {reason}"),
                    };
                }
                // THE VOLATILE ROWS ARE CREDITED JOINTLY OR THEY ARE RED.
                //
                // Their former deferral reason demanded one obligation covering
                // BOTH "the complete load/store value or memory effect" AND
                // "preservation of the observable volatile access/
                // optimizer-ordering boundary", and said plainly that "a
                // byte-identical plain MOV proof alone is insufficient". It is
                // right: a volatile MOV encodes identically to its plain
                // sibling, so an address-and-value proof of the emitted
                // instruction says nothing about whether the access was
                // emitted the right number of times, in the right order.
                //
                // So the credit is a CONJUNCTION of three legs:
                //   * ADDRESS  — `x86_addressing_proofs`, decoded from the real
                //     emitted ModR/M+SIB bytes;
                //   * VALUE    — the MemLoad/MemStore reconstruction the plain
                //     siblings use, which these opcodes map to, discharging
                //     `Valid` for a representative in the ISel register class
                //     (`hooks.value_credit`);
                //   * BOUNDARY — `x86_volatile_trace`, whose hazard battery runs
                //     inside its own credit hook and whose per-compile
                //     enforcement fails the compile closed at BOTH the
                //     selection (VOL-2) and optimizer (VOL-1) boundaries.
                //
                // This RETURNS for every volatile opcode. If any leg fails, the
                // row is RED as `ProofNotDischarged` naming the failed legs; it
                // never falls through to the ADDRESS row below, which would
                // credit it on the address and value legs alone (and which
                // refuses a volatile opcode in any case). Until this returned
                // unconditionally, the VALUE leg asked
                // `X86FunctionVerifier::opcode_to_proof_query`, which has no
                // volatile arm, so the conjunction never held and all sixteen
                // rows fell through to the address row: credited, with the
                // VALUE and BOUNDARY legs gating nothing.
                if x86_opcode_is_volatile_memory(opcode) {
                    return x86_volatile_joint_audit_row(
                        &display,
                        opcode,
                        (hooks.address_credit)(),
                        (hooks.value_credit)(opcode, &self.config),
                        (hooks.volatile_trace_credit)(),
                    );
                }
                // MOV r,imm is credited by a DIFFERENT path than reconstruction,
                // because reconstruction cannot help it — `const == const` is a
                // self-equality (the retracted ledger entry). Its evidence is an
                // INDEPENDENT SDM-derived decode of the REAL emitted bytes,
                // compared as a write to the 64-bit root register against the
                // machine-IR intent, with canonicality and framing pinned. The
                // hook refuses unless every negative control refutes for its
                // stated reason, so "refuting controls" is a precondition of
                // green here rather than a property of some test elsewhere. A
                // hook that stops discharging is a REGRESSION and surfaces as
                // `ProofNotDischarged` — deliberately NOT as a
                // `DeferredUnfaithfulModel`, so the tests that require every x86
                // RED row to be named deferral debt fail loudly.
                if opcode == X86Opcode::MovRI {
                    return x86_movri_audit_row(display, (hooks.movri_credit)());
                }
                // THE SSE LANE FAMILY is credited by a DIFFERENT path than
                // reconstruction, for the same kind of reason MOV r,imm is: the
                // gate's reconstructions are per-lane same-width scalar models,
                // and a permutation, a reduction to flags or to a GPR, an
                // interleave, a saturating narrow and a whole-register copy are
                // none of those. Its evidence is an INDEPENDENT SDM-derived
                // decode of the REAL emitted bytes plus an EXACT bit-level
                // routing denotation, compared against a parametric statement of
                // the machine-IR intent. The hook refuses unless every negative
                // control refutes for its stated reason, so "refuting controls"
                // is a precondition of green here rather than a property of some
                // test elsewhere. A hook that stops discharging is a REGRESSION
                // and surfaces as `ProofNotDischarged` — deliberately NOT as a
                // `DeferredUnfaithfulModel`.
                if let Some(row) = crate::x86_sse_lane_proofs::sse_lane_op_of(opcode) {
                    return x86_sse_lane_audit_row(display, row, (hooks.sse_lane_credit)());
                }
                // THE SCALED SIGN-EXTENDING LOAD is credited by a DIFFERENT path
                // than reconstruction, and the reason is worth stating because
                // the old allowlist reason claimed the opposite. The gate's
                // SibMemAddr reconstruction builds BOTH sides of the effective
                // address from the SAME operand with the SAME `recon_base` /
                // `recon_index` symbols, so it cannot refute a wrong base, a
                // wrong index or a base/index swap, and it has no sign-extending
                // load model at all — a MemLoad reconstruction here would credit
                // the sign extension by asserting it against itself. Its
                // evidence is instead an INDEPENDENT SDM-derived decode of the
                // REAL emitted bytes over per-register leaves named from the
                // DECODED register numbers. The hook refuses unless every
                // control refutes for its stated reason, so "refuting controls"
                // is a precondition of green here rather than a property of some
                // test elsewhere. A hook that stops discharging is a REGRESSION
                // and surfaces as `ProofNotDischarged` — deliberately NOT as a
                // `DeferredUnfaithfulModel`.
                if opcode == X86Opcode::MovsxdRMSib {
                    return x86_movsxd_sib_audit_row(display, (hooks.movsxd_sib_credit)());
                }
                // ADDRESS CREDIT (ADDR-x86). Every opcode that accesses memory
                // through a ModR/M addressing operand is credited HERE, ahead of
                // the reconstruction path, because for those opcodes the
                // reconstruction cannot carry the address facet at all.
                //
                // `x86_reconstruct_effective_address` builds BOTH of its halves
                // from the SAME `X86ISelOperand` with structurally identical
                // encoders, so its obligation is `X == X` and no address error —
                // wrong base, wrong index, base/index swap, wrong scale, wrong
                // displacement — can refute. The audit
                // `report_which_credited_opcodes_have_no_address_teeth` pins that
                // by name for every reconstructable memory opcode (56: the 37
                // plain forms it found in f001a11e8, the 16 volatile forms
                // that reconstruct since 88de9e199, and the three compare-
                // exchange rows) and requires each one to be carried HERE. NO
                // reconstruction earns address teeth: the audit asks whether an
                // obligation rebuilt at a perturbed operand REFUTES, and none
                // does. (The CMPXCHG rows' neighbour and probe leaves once
                // passed a structural version of that test; they are FRAME
                // facets, not address facets.)
                //
                // `x86_addressing_proofs` supplies what was missing: the machine
                // side decoded from the REAL emitted bytes by an SDM-derived
                // decoder that shares no code with the encoder, read as
                // `base + (index << shift) + sext(disp_field)` against an intent
                // of `base + index*scale + disp`. The two are structurally
                // distinct by construction, and the comparison REFUSES a machine
                // side identical to the source side, so this credit cannot decay
                // into the shape it replaces.
                //
                // The controls are INSIDE the hook: `mem_mov_address_credit`
                // does not return `Ok` unless every intent control and every byte
                // control refutes, and unless the corpus still reaches every
                // addressing mode, every access width and both register files. A
                // battery outside the credit path cannot withhold a credit when
                // it stops refuting, which is how three earlier families here
                // came to be credited for reasons that had quietly become false.
                //
                // The COMPARE-EXCHANGE rows are credited JOINTLY: their VALUE
                // facet is a genuine per-instruction reconstruction (returns-
                // old, conditional store, ZF, frame), which the address lane
                // does not replace, so both must hold or the row is RED. The
                // VALUE leg is the same `hooks.value_credit` the ADDRESS row
                // below requires, so one injected failure reaches both.
                if x86_opcode_is_compare_exchange_memory(opcode) {
                    return x86_compare_exchange_joint_audit_row(
                        display,
                        opcode,
                        (hooks.address_credit)(),
                        (hooks.value_credit)(opcode, &self.config),
                    );
                }
                // The ADDRESS is not the whole row. The row also requires the
                // VALUE leg, the opcode's reconstruction discharging `Valid`:
                // its address half is the `X == X` above, but its value half
                // (access width and direction, extension, the operation of a
                // memory-ALU form) is rebuilt from the real opcode. Neither leg
                // alone credits the row. A VOLATILE opcode never reaches here;
                // it returned above through its joint row.
                if x86_opcode_has_address_credit(opcode) {
                    return x86_address_audit_row(
                        display,
                        opcode,
                        (hooks.address_credit)(),
                        (hooks.value_credit)(opcode, &self.config),
                    );
                }
                // PHASE-2 OPERAND RECONSTRUCTION CREDIT (task #66) — mirrors
                // `audit_aarch64` / `audit_riscv` exactly.
                //
                // If the opcode is RECONSTRUCTABLE (in the x86
                // `x86_opcode_to_source_op`) and a representative reconstructed
                // obligation discharges `Valid`, credit it COVERED here — the
                // machine side was rebuilt from the REAL opcode, so a wrong
                // OPCODE choice would have refuted, unlike the degenerate X==X
                // the static-DB "x86_64: …" proof would have matched. Note the
                // scope: for a memory opcode this says nothing about the
                // ADDRESS, whose two halves this path builds from the same
                // operand; memory opcodes are routed to the byte-level ADDRESS
                // credit above before they reach here. Routes BEFORE the width-polymorphic / DB-substring path
                // so the headline reflects reconstruction; an opcode that is NOT
                // reconstructable, or whose reconstruction does not discharge Valid,
                // falls through to the existing paths unchanged (nothing is
                // fake-covered). The gate's own rule: the function verifier credits
                // a reconstruction only with complete evidence and reports a sampled
                // one uncredited (E0.2). NOTE: the byte/word
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
                // x86 query mapping is matched case-sensitively
                // (`name.contains(query)`). The verifier credits no such match
                // (E0.2); this row records only that the named theorem discharges.
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
                // The gate's own rule: the function verifier credits a
                // reconstruction only with complete evidence and reports a
                // sampled one uncredited (E0.2).
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
                // The RISC-V query mapping names no theorem for any opcode since
                // the #62 retraction, so every opcode that reaches here reports
                // `NoProofMapping`; the per-instruction walk has no registry arm.
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
                // All RISC-V lowering proofs live under a single category and are
                // matched case-sensitively (`name.contains`). Unreachable while
                // the mapping above is empty.
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
                //
                // `copysign` additionally needs its EMITTED BODY
                // (`wasm_float_binop_proofs`): the representative reconstruction
                // assumes the magnitude operand is deeper on the stack than the
                // sign operand, and only the captured body shows that order.
                let copysign = matches!(opcode, WasmOpcode::F32Copysign | WasmOpcode::F64Copysign);
                let body_backed = !copysign
                    || crate::wasm_float_binop_proofs::float_binop_body_discharges_valid(
                        opcode.opcode_byte(),
                    );
                if body_backed && wasm_reconstruction_discharges_valid(opcode, &self.config) {
                    if copysign {
                        return OpcodeAuditRow {
                            opcode_display: display,
                            class: OpcodeClass::EmittableNeedsProof,
                            finding: None,
                            note: format!(
                                "RECONSTRUCTED from real {opcode:?} opcode byte over the operands' \
                                 IEEE-754 bit patterns (spec fcopysign vs trust-ir FCopySign \
                                 mask-and-merge; swapped operands / fabs / fneg refute) AND its \
                                 captured emitted body run against the same contract \
                                 (wasm_float_binop_proofs) [reconstruction] (default evaluator \
                                 acceptance is regression evidence, NOT a formal proof)"
                            ),
                        };
                    }
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
                // P4: the two scalar CONSTANT forms are credited by a different
                // path than reconstruction, because reconstruction cannot help
                // them — `const == const` is a self-equality. Their evidence is
                // an INDEPENDENT spec-derived signed-LEB decode of the REAL
                // emitted immediate (plus a canonical-length check, since the
                // spec admits padded encodings a decode-only check cannot see).
                if matches!(opcode, WasmOpcode::I32Const | WasmOpcode::I64Const)
                    && crate::wasm_encoding_proofs::const_immediate_discharges_valid(
                        opcode.opcode_byte(),
                    )
                {
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: None,
                        note: "RECONSTRUCTED by DECODING the real emitted signed-LEB128 \
                               immediate with an INDEPENDENT spec-derived sN decoder \
                               (wasm_encoding_proofs): every captured immediate decodes to \
                               its intended constant AT CANONICAL LENGTH, and every mutation \
                               of those bytes REFUTES. Says nothing about whether the \
                               LOWERING chose the right constant."
                            .to_string(),
                    };
                }
                // The FLOAT constants: an INDEPENDENT spec-derived decode of the
                // real emitted raw IEEE-754 payload, compared bit-exactly with
                // the pattern the trust-ir constant's binary64 carrier denotes —
                // through an independently stated roundTiesToEven narrowing for
                // `f32.const` — with every negative control refuting for its
                // stated reason inside the hook.
                if matches!(opcode, WasmOpcode::F32Const | WasmOpcode::F64Const)
                    && crate::wasm_encoding_proofs::float_const_immediate_discharges_valid(
                        opcode.opcode_byte(),
                    )
                {
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: None,
                        note: "RECONSTRUCTED by DECODING the real emitted little-endian IEEE-754 \
                               payload with an INDEPENDENT spec-derived float decoder \
                               (wasm_encoding_proofs): every captured immediate is BIT-EXACTLY the \
                               pattern its trust-ir binary64 carrier denotes (f32: an \
                               independently stated roundTiesToEven narrowing, NaNs quieted with \
                               their payload kept), and byte-swap / truncation / width-confusion / \
                               quieted-sNaN / unquieted-narrowing / sign-drop / round-toward-zero \
                               / negated-claim controls each REFUTE for their stated reason. Says \
                               nothing about whether the LOWERING chose the right carrier."
                            .to_string(),
                    };
                }
                // `f.min` / `f.max` are emitted only inside the FMin / FMax
                // sequence, so their evidence is that SEQUENCE: the captured
                // emitted function body, executed under the spec's instruction
                // semantics for every wasm NaN choice and compared with the
                // relational trust-ir contract (`wasm_float_binop_proofs`).
                if matches!(
                    opcode,
                    WasmOpcode::F32Min
                        | WasmOpcode::F64Min
                        | WasmOpcode::F32Max
                        | WasmOpcode::F64Max
                ) && crate::wasm_float_binop_proofs::float_binop_body_discharges_valid(
                    opcode.opcode_byte(),
                ) {
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: None,
                        note: format!(
                            "RECONSTRUCTED from the captured emitted FMin/FMax body containing \
                             {opcode:?} (NaN guards + select around the NaN-propagating wasm op), \
                             executed under the spec semantics for every permitted f.min/f.max \
                             NaN result and compared with the relational trust-ir contract over \
                             a bit-pattern battery: a lone NaN gives the other operand \
                             bit-exactly, two NaNs give a NaN, an ordered pair the lesser/greater, \
                             a -0/+0 tie either operand (trust-ir leaves it unpinned; pinned to \
                             the second operand the body REFUTES). Opposite-op / unguarded / \
                             inverted-guard / NaN-selecting controls refute. Battery evidence, \
                             NOT a formal proof"
                        ),
                    };
                }
                // A trust-ir `MemCopy` / `MemSet` lowers to the op inside an
                // `if (n != 0)` guard, so the evidence for that lowering is the
                // SEQUENCE: the captured emitted function body, executed under
                // the spec semantics on a concrete memory and compared with the
                // relational trust-ir contract (`wasm_bulk_memory_proofs`).
                // `memory.fill` is emitted nowhere else. `memory.copy` is ALSO
                // emitted, unguarded with a constant nonzero size, by the
                // memory-carried-value layer's aggregate / lane / sret moves
                // (`emit_copy`); the row credits the op's semantics through the
                // guarded body, and those moves' addresses and sizes rest on
                // the lane differentials, as the note says.
                let bulk_sub = match opcode {
                    WasmOpcode::MemoryCopy => Some(crate::wasm_bulk_memory_proofs::MEMORY_COPY_SUB),
                    WasmOpcode::MemoryFill => Some(crate::wasm_bulk_memory_proofs::MEMORY_FILL_SUB),
                    _ => None,
                };
                if let Some(sub) = bulk_sub
                    && crate::wasm_bulk_memory_proofs::bulk_memory_body_discharges_valid(sub)
                {
                    let scope = if opcode == WasmOpcode::MemoryCopy {
                        "memory.copy is ALSO emitted unguarded, with a constant nonzero size, \
                         by the aggregate / lane / sret moves of the memory-carried-value layer \
                         (emit_copy); this credit does NOT cover those instances, whose \
                         addresses and sizes rest on the lane differentials \
                         (wasm_g1_lane_semantics, wasm_g3_lane_frames)"
                    } else {
                        "memory.fill is emitted only by the guarded MemSet lowering"
                    };
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: None,
                        note: format!(
                            "RECONSTRUCTED from the captured emitted guarded MemCopy/MemSet body \
                             containing {opcode:?} (0xfc {sub}), executed under the spec \
                             semantics on a two-page memory (bounds check in unbounded \
                             arithmetic before the zero test, copy as if through a temporary, \
                             fill with the operand's low byte) and compared with the relational \
                             trust-ir contract over a battery reaching every input class: a \
                             zero count returns with the memory unchanged whatever the pointers, \
                             an in-memory range is copied or filled exactly, a range past the \
                             memory is UB that a trap refines. The battery observes bits 0-16 \
                             of each pointer and of the count and every bit of the fill byte \
                             (clearing any one refutes); every higher bit rests on the \
                             operand-provenance check, which requires the op's operands to be \
                             the function's parameters (the fill byte up to its u8 mask) and the \
                             guard to test the count. Unguarded / inverted-guard / \
                             guard-on-destination / swapped-operand / forward-byte-copy / \
                             truncated-count / truncated-source / cleared-destination-bit \
                             controls refute at their stated class, and every operand mask also \
                             fails the provenance check. Battery evidence plus a dataflow check \
                             of this body, NOT a formal proof. Scope: {scope}"
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

    // -- WebAssembly P3 value domain (byte-keyed) --------------------------

    /// Rows for [`GateArch::WasmValueDomain`]: the 28 P3 opcode bytes in spec
    /// order — 16 audited for credit and the 12 never-selected bytes excluded
    /// with their reason — then the 4 named deferrals.
    fn audit_wasm_value_domain_rows(&self) -> Vec<OpcodeAuditRow> {
        let mut rows: Vec<OpcodeAuditRow> = crate::wasm_value_domain::all_wasm_value_domain_bytes()
            .into_iter()
            .map(|byte| match classify_wasm_value_domain(byte) {
                Some(OpcodeClass::FailClosedAllowlisted { reason }) => {
                    let mnemonic = crate::wasm_value_domain::value_domain_mnemonic(byte)
                        .unwrap_or("<not a P3 opcode>");
                    OpcodeAuditRow {
                        opcode_display: format!("wasm::{mnemonic} (0x{byte:02x})"),
                        class: OpcodeClass::FailClosedAllowlisted { reason },
                        finding: None,
                        note: format!("fail-closed allowlist: {reason}"),
                    }
                }
                _ => self.audit_wasm_value_domain_byte(byte),
            })
            .collect();
        rows.extend(
            crate::wasm_value_domain::WASM_VALUE_DOMAIN_DEFERRALS
                .iter()
                .map(wasm_value_domain_deferral_row),
        );
        rows
    }

    /// Audit ONE P3 value-domain opcode byte.
    ///
    /// Credit is the same rule the other backends use — the machine side must be
    /// RECONSTRUCTED from the real opcode byte and discharge `Valid` — with one
    /// tightening: a P3 byte must clear EVERY obligation in its set, not one of
    /// them. A store's value obligation alone cannot see a too-wide store, so
    /// crediting on a partial set would credit exactly the slip the pair exists
    /// to catch. There is no static-DB fallback: a byte whose set does not fully
    /// discharge is reported RED, never quietly covered.
    fn audit_wasm_value_domain_byte(&self, byte: u8) -> OpcodeAuditRow {
        use crate::wasm_value_domain as vd;

        let mnemonic = vd::value_domain_mnemonic(byte).unwrap_or("<not a P3 opcode>");
        let display = format!("wasm::{mnemonic} (0x{byte:02x})");
        let obligations = vd::obligations_for_byte(byte);
        if obligations.is_empty() {
            return OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::EmittableNeedsProof,
                finding: Some(CoverageFinding::NoProofMapping),
                note: "no P3 obligation is built for this byte — uncredited debt, not silent \
                       trust"
                    .to_string(),
            };
        }
        if vd::value_domain_discharges_valid(byte, &self.config) {
            let fp_note = match crate::wasm_semantics::decode_mem_op(byte) {
                Some(op) if op.is_fp => {
                    " NOTE: an f32/f64 access is bit-identical to the same-width integer access \
                     (wasm does not canonicalize NaN on load/store), so an int/FP opcode swap is \
                     NOT value-refutable — that discriminator is the wasm TYPE, checked by module \
                     validation."
                }
                _ => "",
            };
            let offset_note = if crate::wasm_semantics::decode_mem_op(byte).is_some() {
                " The memarg offset is BOUND: in the captured module of struct field reads and \
                 writes (wasm_memarg_offset_proofs) every access with this byte at a nonzero \
                 trust-ir layout offset is decoded, its offset obligation is instantiated at the \
                 decoded skew and discharges, and shifted- and dropped-offset controls refute. \
                 Other nonzero-offset sites (enum tags, niches, nested lanes, i128 halves, sret \
                 and parameter lanes) rest on the lane differentials."
            } else {
                ""
            };
            return OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::EmittableNeedsProof,
                finding: None,
                note: format!(
                    "RECONSTRUCTED from the real 0x{byte:02x} opcode byte over a symbolic \
                     byte-addressed memory — all {} obligation(s) evaluate Valid [reconstruction] \
                     (default evaluator acceptance is regression evidence, NOT a formal \
                     proof).{fp_note}{offset_note}",
                    obligations.len()
                ),
            };
        }
        OpcodeAuditRow {
            opcode_display: display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: Some(CoverageFinding::ProofNotDischarged {
                proof_name: obligations
                    .first()
                    .map(|ob| ob.name.clone())
                    .unwrap_or_default(),
                detail: if crate::wasm_semantics::decode_mem_op(byte).is_some() {
                    format!(
                        "at least one obligation in the byte's set did not discharge Valid, or \
                         its emitted memarg offset is not bound: {:?}",
                        crate::wasm_memarg_offset_proofs::memarg_offset_credit_failures(
                            byte,
                            crate::wasm_memarg_offset_proofs::MEMARG_FIELDS_TIR,
                            crate::wasm_memarg_offset_proofs::MEMARG_FIELDS_WASM,
                            &self.config,
                        )
                    )
                } else {
                    "at least one obligation in the byte's set did not discharge Valid".to_string()
                },
            }),
            note: "P3 value-domain byte did not fully reconstruct-discharge Valid".to_string(),
        }
    }

    // -- WebAssembly P4 family 1: the CFG structural invariant -------------

    /// Rows for [`GateArch::WasmCfgStructural`], in this order: the reference
    /// module the checker must ACCEPT, the anti-tautology mutants it must
    /// REFUTE, the mutants it is measured NOT to catch, the five named
    /// deferrals, and finally the seven invariant STATEMENTS.
    ///
    /// The credit unit is deliberately the MUTANT, not the invariant. An
    /// invariant is a sentence; what makes it evidence is a wrong module it
    /// rejects, and only some of the seven have one in the family's own
    /// no-argument battery (there is no `br_table` in the hand-encoded reference
    /// module, for instance — the real corpus lives in the family's gate test,
    /// which needs the backend this crate cannot depend on). Crediting all seven
    /// off one battery would hand a statement the evidence of its neighbours, so
    /// the statements are listed as EXCLUDED rows that name the mutant rows
    /// carrying their teeth, and the mutant rows carry the credit.
    fn audit_wasm_cfg_rows(&self) -> Vec<OpcodeAuditRow> {
        use crate::wasm_cfg_proofs as cfg;

        let mut rows = Vec::new();

        // (1) The checker RUNS on a real module and accepts it. Without this row
        //     a checker that refused everything would look perfect: every mutant
        //     would be "refuted" and nothing would be credited for being right.
        let verdict = cfg::check_module_structure(&cfg::correct_merge_nest_module());
        let display = "wasm-cfg::reference module `merge_nest` HOLDS".to_string();
        rows.push(match verdict.report() {
            Some(report) => {
                let t = report.totals();
                OpcodeAuditRow {
                    opcode_display: display,
                    class: OpcodeClass::EmittableNeedsProof,
                    finding: None,
                    note: format!(
                        "the structural invariant HOLDS on the family's hand-encoded merge-nest \
                         module: {} function(s), {} instruction(s) given a typing rule, {} branch \
                         label(s) resolved against the rebuilt control stack, {} join(s) height- \
                         and type-checked, {} scope(s) matched. A NECESSARY CONDITION on the \
                         structuring — not a bisimulation (see the RED headline deferral below)",
                        t.functions,
                        t.instructions,
                        t.branch_labels_resolved,
                        t.joins_checked,
                        t.scopes_matched
                    ),
                }
            }
            None => OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::EmittableNeedsProof,
                finding: Some(CoverageFinding::ProofNotDischarged {
                    proof_name: "wasm_cfg_proofs::correct_merge_nest_module".to_string(),
                    detail: verdict.to_string(),
                }),
                note: format!(
                    "the checker did NOT accept its own reference module: {verdict}. An \
                     inconclusive verdict is debt, not credit"
                ),
            },
        });

        // (2)/(3) The anti-tautology battery, reported exactly as it ran.
        //
        // `MutantOutcome` carries the name and the verdict but not the mutant's
        // prose, and a deferral's `reason` must be `&'static`; `all_cfg_mutants`
        // is the only place that prose lives, so it is looked up BY NAME rather
        // than by position. A name with no match yields no prose instead of the
        // wrong prose.
        let descriptions: Vec<(&'static str, &'static str)> = cfg::all_cfg_mutants()
            .iter()
            .map(|m| (m.name, m.description))
            .collect();
        for outcome in cfg::run_cfg_mutants() {
            let description = descriptions
                .iter()
                .find(|(name, _)| *name == outcome.name)
                .map(|(_, d)| *d)
                .unwrap_or("(no description registered for this mutant)");
            rows.push(wasm_cfg_mutant_row(&outcome, description));
        }

        // (4) The named deferrals — RED IN the denominator, headline first.
        rows.extend(cfg::WASM_CFG_DEFERRALS.iter().map(wasm_cfg_deferral_row));

        // (5) The invariant statements, excluded with their evidence boundary.
        rows.extend(cfg::WASM_CFG_INVARIANTS.iter().map(wasm_cfg_invariant_row));

        rows
    }

    // -- WebAssembly P4 families 2/3: the memory / call ABI ----------------

    /// Rows for [`GateArch::WasmAbi`], in this order: per fixture, the frame
    /// obligations and structural checks the family states over REAL emitted
    /// bytes, then any fail-closed refusal; then the anti-tautology guards; then
    /// the nine named deferrals.
    ///
    /// Credit follows the same rule as every other family here — an SMT
    /// obligation must be `Reconstructed`-provenanced AND discharge `Valid`, a
    /// structural check must hold, a `MustRefute` guard must actually refute.
    /// A refusal earns NO credit and is a RED row: a function the family could
    /// not recognize is uncredited debt, never a silent skip.
    fn audit_wasm_abi_rows(&self) -> Vec<OpcodeAuditRow> {
        use crate::wasm_abi_proofs as abi;

        let mut rows = Vec::new();
        let report = abi::wasm_abi_family_report();

        for error in &report.errors {
            rows.push(OpcodeAuditRow {
                opcode_display: format!("wasm-abi::UNMODELED FIXTURE ({error})"),
                class: OpcodeClass::EmittableNeedsProof,
                finding: Some(CoverageFinding::NoProofMapping),
                note: "a corpus fixture could not be modeled at all, so it contributes no \
                       obligation — uncredited debt, not silent trust"
                    .to_string(),
            });
        }

        for (fixture, evidence) in &report.per_fixture {
            for ob in &evidence.obligations {
                let display = format!("wasm-abi::{fixture}::{}", ob.name);
                let reconstructed = ob.is_reconstructed();
                let result = verify_by_evaluation_with_config(ob, &self.config);
                if reconstructed && matches!(result, VerificationResult::Valid) {
                    rows.push(OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: None,
                        note: "RECONSTRUCTED from the REAL emitted frame arithmetic (the \
                               prologue/alloca/epilogue instructions decoded out of the module \
                               bytes) against the frame the trust-ir independently intends — \
                               evaluates Valid [reconstruction] (default evaluator acceptance is \
                               regression evidence, NOT a formal proof)"
                            .to_string(),
                    });
                } else {
                    rows.push(OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: Some(CoverageFinding::ProofNotDischarged {
                            proof_name: ob.name.clone(),
                            detail: if reconstructed {
                                format!("{result:?}")
                            } else {
                                "obligation is not Reconstructed-provenanced, so it cannot earn \
                                 reconstruction credit"
                                    .to_string()
                            },
                        }),
                        note: "wasm ABI frame obligation did not reconstruct-discharge Valid"
                            .to_string(),
                    });
                }
            }

            for check in &evidence.structural {
                let display = format!("wasm-abi::{fixture}::{}", check.name);
                if check.ok {
                    rows.push(OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: None,
                        note: format!(
                            "DECIDABLE structural equality between the DECODED real module and \
                             the trust-ir's independently derived intent: {}. Settled by decoding, \
                             not by a solver; its teeth are the byte-mutation guards below",
                            check.detail
                        ),
                    });
                } else {
                    rows.push(OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: Some(CoverageFinding::ProofNotDischarged {
                            proof_name: check.name.clone(),
                            detail: check.detail.clone(),
                        }),
                        note: format!(
                            "structural check FAILED on real emitted bytes: {}",
                            check.detail
                        ),
                    });
                }
            }

            for refusal in &evidence.refusals {
                rows.push(OpcodeAuditRow {
                    opcode_display: format!("wasm-abi::{fixture}::REFUSED ({refusal})"),
                    class: OpcodeClass::EmittableNeedsProof,
                    finding: Some(CoverageFinding::NoProofMapping),
                    note: "the family could not recognize this emission and built NO obligation \
                           for it — fail closed, so no credit"
                        .to_string(),
                });
            }
        }

        // The anti-tautology guards: mutate the REAL bytes and require a failure.
        for outcome in abi::all_wasm_abi_guards(&self.config) {
            rows.push(wasm_abi_guard_row(outcome));
        }

        // The nine named deferrals — RED IN the denominator.
        rows.extend(abi::WASM_ABI_DEFERRALS.iter().map(wasm_abi_deferral_row));

        rows
    }

    // -- shared proof lookup + discharge ----------------------------------

    /// Find the proof matching `query` in `category` and discharge it, with the
    /// case-matching convention each verifier's query mapping uses. The
    /// verifiers themselves no longer discharge or credit a theorem found this
    /// way (E0.2); see the module docs.
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

    /// Require one discharged proof for EVERY legal (width, shift) form of a
    /// form-polymorphic AArch64 opcode (see [`aarch64_form_polymorphic_proofs`]).
    ///
    /// The table must name exactly the forms in
    /// [`AARCH64_MOVE_WIDE_LEGAL_FORMS`], each once; a missing, duplicated or
    /// architecturally illegal form is a finding, not a skipped row. The row
    /// fails on the first form whose proof is missing, degenerate or
    /// undischarged and names that form.
    fn check_all_forms(&self, display: String, forms: &[FormProof]) -> OpcodeAuditRow {
        let fail = |display: String, query: String, note: String| OpcodeAuditRow {
            opcode_display: display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: Some(CoverageFinding::NoMatchingProof { query }),
            note,
        };
        for &(width, shift) in AARCH64_MOVE_WIDE_LEGAL_FORMS {
            let named = forms
                .iter()
                .filter(|form| form.width_bits == width && form.shift == shift)
                .count();
            if named != 1 {
                return fail(
                    display,
                    format!("form (w{width}, lsl #{shift})"),
                    format!(
                        "form-polymorphic table names the legal form (w{width}, lsl #{shift}) \
                         {named} times; exactly one discharged proof per legal form is required"
                    ),
                );
            }
        }
        if let Some(illegal) = forms
            .iter()
            .find(|form| !AARCH64_MOVE_WIDE_LEGAL_FORMS.contains(&(form.width_bits, form.shift)))
        {
            return fail(
                display,
                illegal.query.to_string(),
                format!(
                    "form-polymorphic table names the architecturally illegal form \
                     (w{}, lsl #{}); it must not be credited",
                    illegal.width_bits, illegal.shift
                ),
            );
        }
        let mut notes = Vec::with_capacity(forms.len());
        for form in forms {
            match self.discharge_one(form.query, form.category, MatchCase::Insensitive) {
                Ok(note) => notes.push(format!(
                    "(w{}, lsl #{}): {note}",
                    form.width_bits, form.shift
                )),
                Err((finding, note)) => {
                    return OpcodeAuditRow {
                        opcode_display: display,
                        class: OpcodeClass::EmittableNeedsProof,
                        finding: Some(finding),
                        note: format!("(w{}, lsl #{}): {note}", form.width_bits, form.shift),
                    };
                }
            }
        }
        OpcodeAuditRow {
            opcode_display: display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: None,
            note: format!(
                "FORM-POLYMORPHIC: every legal (width, shift) form discharged — {}",
                notes.join("; ")
            ),
        }
    }

    /// Credit a decoded-value opcode: the hook must accept (captured words,
    /// every control refuted for its stated class), then every form's
    /// registered obligation must exist, be non-degenerate and discharge.
    fn check_a64_value_row(
        &self,
        display: String,
        opcode: AArch64Opcode,
        forms: &[crate::aarch64_value_decode_proofs::A64ValueForm],
        value_credit: &dyn Fn(
            AArch64Opcode,
        )
            -> Result<crate::aarch64_value_decode_proofs::A64ValueCredit, String>,
    ) -> OpcodeAuditRow {
        let credit = match value_credit(opcode) {
            Ok(credit) => credit,
            Err(detail) => {
                let proof_name = format!("aarch64_value_decode_proofs::{opcode:?}");
                return OpcodeAuditRow {
                    opcode_display: display,
                    class: OpcodeClass::EmittableNeedsProof,
                    finding: Some(CoverageFinding::ProofNotDischarged {
                        proof_name: proof_name.clone(),
                        detail: detail.clone(),
                    }),
                    note: format!("{proof_name} REFUSED: {detail}"),
                };
            }
        };
        let mut notes = Vec::with_capacity(forms.len());
        for form in forms {
            match self.discharge_one(form.query(), form.category(), MatchCase::Insensitive) {
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
            note: format!(
                "DECODED-WORD: {} form(s) over captured encoder words, {} decided by exact bit \
                 routing (complete over register values; an in-process decision, not an \
                 independently checked certificate), {} captured word(s) checked, {} negative \
                 control(s) refuted for their stated reason — {}",
                credit.forms,
                credit.exact_forms,
                credit.captured_words,
                credit.controls_refuted,
                notes.join("; ")
            ),
        }
    }

    /// Audit one NZCV producer/consumer row: the credit hook must hold, and
    /// every demanded form's registered obligation must exist, be the very
    /// obligation the hook checked (for this module's forms), and discharge.
    /// Discharge uses the process-wide content-keyed evaluation memo, warmed in
    /// parallel, so repeated audits in one process evaluate each form once;
    /// the verdict is the same as an unmemoized evaluation.
    fn check_flag_consumer_row(
        &self,
        display: String,
        opcode: AArch64Opcode,
        forms: &[crate::aarch64_flag_consumer_proofs::FlagForm],
        credit_hook: &dyn Fn(
            AArch64Opcode,
        ) -> Result<
            crate::aarch64_flag_consumer_proofs::FlagConsumerCredit,
            String,
        >,
    ) -> OpcodeAuditRow {
        use rayon::prelude::*;
        let fail = |display: String, finding: CoverageFinding, note: String| OpcodeAuditRow {
            opcode_display: display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: Some(finding),
            note,
        };
        let credit = match credit_hook(opcode) {
            Ok(credit) => credit,
            Err(detail) => {
                let proof_name = format!("aarch64_flag_consumer_proofs::{opcode:?}");
                return fail(
                    display,
                    CoverageFinding::ProofNotDischarged {
                        proof_name: proof_name.clone(),
                        detail: detail.clone(),
                    },
                    format!("{proof_name} REFUSED: {detail}"),
                );
            }
        };
        let mut resolved = Vec::with_capacity(forms.len());
        for form in forms {
            let query = form.query.to_lowercase();
            let Some(proof) = self
                .db
                .by_category(form.category)
                .into_iter()
                .find(|p| p.obligation.name.to_lowercase().contains(&query))
            else {
                return fail(
                    display,
                    CoverageFinding::NoMatchingProof {
                        query: form.query.to_string(),
                    },
                    format!("no proof matching {:?} in {:?}", form.query, form.category),
                );
            };
            if proof.obligation.is_degenerate() {
                return fail(
                    display,
                    CoverageFinding::DegenerateProof {
                        proof_name: proof.obligation.name.clone(),
                    },
                    format!(
                        "DEGENERATE (X==X, model-consistency only, not proven): {}",
                        proof.obligation.name
                    ),
                );
            }
            if let Some(built) = &form.built
                && *built != proof.obligation
            {
                return fail(
                    display,
                    CoverageFinding::ProofNotDischarged {
                        proof_name: proof.obligation.name.clone(),
                        detail: "the registered obligation is not the one the credit hook checked"
                            .to_string(),
                    },
                    format!(
                        "{} diverges from its checked builder",
                        proof.obligation.name
                    ),
                );
            }
            resolved.push(&proof.obligation);
        }
        let verdicts: Vec<VerificationResult> = resolved
            .par_iter()
            .map(|ob| crate::lowering_proof::memoized_verify_by_evaluation(ob, &self.config))
            .collect();
        let mut statistical = 0usize;
        for (ob, verdict) in resolved.iter().zip(verdicts) {
            match verdict {
                VerificationResult::Valid => {
                    if matches!(
                        VerificationStrength::for_obligation_with_config(ob, &self.config),
                        VerificationStrength::Statistical { .. }
                    ) {
                        statistical += 1;
                    }
                }
                VerificationResult::Invalid { counterexample } => {
                    return fail(
                        display,
                        CoverageFinding::ProofNotDischarged {
                            proof_name: ob.name.clone(),
                            detail: counterexample,
                        },
                        ob.name.clone(),
                    );
                }
                VerificationResult::Unknown { reason } => {
                    return fail(
                        display,
                        CoverageFinding::ProofNotDischarged {
                            proof_name: ob.name.clone(),
                            detail: format!("Unknown: {reason}"),
                        },
                        ob.name.clone(),
                    );
                }
            }
        }
        OpcodeAuditRow {
            opcode_display: display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: None,
            note: format!(
                "NZCV PRODUCER/CONSUMER: {} form(s) discharged ({} own over captured words, {} \
                 integer-producer forms of other families; {} by sampled evaluation — accepted \
                 regression evidence, NOT a formal proof), {} boundary-battery point(s) agreed, \
                 {} captured word(s) decoded back, {} negative control(s) refuted for their \
                 stated reason",
                resolved.len(),
                credit.own_forms,
                credit.borrowed_forms,
                statistical,
                credit.battery_points,
                credit.captured_words,
                credit.controls_refuted
            ),
        }
    }

    /// The AArch64 audit of one NZCV producer/consumer opcode with the credit
    /// hook INJECTED, so a test can hand the gate a failing hook and watch the
    /// row leave the covered count as `ProofNotDischarged`.
    #[doc(hidden)]
    pub fn audit_aarch64_flag_consumer_with(
        &self,
        opcode: AArch64Opcode,
        credit_hook: &dyn Fn(
            AArch64Opcode,
        ) -> Result<
            crate::aarch64_flag_consumer_proofs::FlagConsumerCredit,
            String,
        >,
    ) -> Option<OpcodeAuditRow> {
        let forms = crate::aarch64_flag_consumer_proofs::flag_consumer_forms(opcode)?;
        Some(self.check_flag_consumer_row(
            format!("AArch64::{opcode:?}"),
            opcode,
            &forms,
            credit_hook,
        ))
    }

    fn check_volatile_row(
        &self,
        display: String,
        opcode: AArch64Opcode,
        plain: AArch64Opcode,
        hooks: &AArch64AuditHooks<'_>,
    ) -> OpcodeAuditRow {
        let credit = match (hooks.volatile_credit)() {
            Ok(credit) => credit,
            Err(detail) => {
                let proof_name = "volatile_access_preservation".to_string();
                return OpcodeAuditRow {
                    opcode_display: display,
                    class: OpcodeClass::EmittableNeedsProof,
                    finding: Some(CoverageFinding::ProofNotDischarged {
                        proof_name: proof_name.clone(),
                        detail: detail.clone(),
                    }),
                    note: format!("{proof_name} REFUSED: {detail}"),
                };
            }
        };
        let plain_row = match hooks.plain_row {
            Some(plain_row) => plain_row(plain),
            None => self.audit_aarch64_with(plain, hooks),
        };
        let preservation = format!(
            "volatile access preservation [every path's volatile accesses, in order, by direction \
             and size; decided per compile by the AArch64 pipeline; {} positive and {} refuted \
             control(s)]",
            credit.positives, credit.controls_refuted
        );
        if plain_row.finding.is_some() {
            let reason = aarch64_deferred_value_op_reason(opcode).unwrap_or(
                "volatile access row without a named deferral: its plain counterpart is RED",
            );
            return OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::EmittableNeedsProof,
                finding: Some(CoverageFinding::DeferredUnfaithfulModel { reason }),
                note: format!(
                    "HONESTLY DEFERRED (RED in denominator): {reason} — {preservation} holds; \
                     plain {plain:?} is RED: {}",
                    plain_row.note
                ),
            };
        }
        OpcodeAuditRow {
            opcode_display: display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: None,
            note: format!(
                "VOLATILE: plain {plain:?} evidence [{}] + {preservation}",
                plain_row.note
            ),
        }
    }
    /// One conditional trap carrier's row (L04-P12): the carrier must have
    /// forms in [`crate::aarch64_trap_expansion::trap_battery`], and the
    /// family's credit hook must hold (every form decides to hold, every
    /// control is refuted).
    /// The `SubsRI` row (L04-P1): covered only when its credit hook holds —
    /// both widths' re-derived words write the operands' difference and
    /// comparison flags for every register value (decided in process by the
    /// bit-serial automaton) and every corruption control is refuted for its
    /// stated reason. A failing hook is `ProofNotDischarged`.
    fn check_subs_imm_row(
        &self,
        display: String,
        credit: &dyn Fn() -> Result<crate::aarch64_subs_imm_proofs::SubsImmCredit, String>,
    ) -> OpcodeAuditRow {
        match credit() {
            Ok(credit) => OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::EmittableNeedsProof,
                finding: None,
                note: format!(
                    "SUBS #imm DECODED-WORD credit [the word's Arm ARM pseudocode writes the \
                     difference and the comparison's N, Z, C, V for every register value; {} \
                     forms hold over {} instances and {} corruption controls refute; {} — \
                     accepted regression evidence, NOT a formal proof]",
                    credit.forms,
                    credit.instances,
                    credit.controls_refuted,
                    crate::aarch64_subs_imm_proofs::METHOD_BITSERIAL
                ),
            },
            Err(detail) => OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::EmittableNeedsProof,
                finding: Some(CoverageFinding::ProofNotDischarged {
                    proof_name: "aarch64_subs_imm_proofs::SubsRI".into(),
                    detail: detail.clone(),
                }),
                note: format!("aarch64_subs_imm_proofs::SubsRI REFUSED: {detail}"),
            },
        }
    }

    /// The `SubsRI` row with its credit hook INJECTED, so a test can watch a
    /// failing hook turn the row red.
    #[doc(hidden)]
    pub fn audit_aarch64_subs_imm_with(
        &self,
        credit: &dyn Fn() -> Result<crate::aarch64_subs_imm_proofs::SubsImmCredit, String>,
    ) -> OpcodeAuditRow {
        self.check_subs_imm_row("AArch64::SubsRI".into(), credit)
    }

    /// A CRC32/CRC32C row (L04-P1): covered only when the family's credit
    /// hook holds — every form's re-derived word holds against the reflected
    /// CRC intent over the register battery, decided for every register value
    /// by GF(2)-affine evaluation in process, and every corruption control is
    /// refuted for its stated reason. A failing hook is `ProofNotDischarged`.
    fn check_crc32_row(
        &self,
        display: String,
        opcode: AArch64Opcode,
        credit: &dyn Fn() -> Result<crate::aarch64_crc32_proofs::Crc32Credit, String>,
    ) -> OpcodeAuditRow {
        use crate::aarch64_crc32_proofs as crc;
        let Some(form) = crc::Crc32Form::from_opcode(opcode) else {
            return OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::EmittableNeedsProof,
                finding: Some(CoverageFinding::NoProofMapping),
                note: format!("{opcode:?} is not a CRC32 opcode"),
            };
        };
        match credit() {
            Ok(credit) => OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::EmittableNeedsProof,
                finding: None,
                note: format!(
                    "CRC32 DECODED-WORD credit [{}: the word's Arm ARM pseudocode equals the \
                     reflected CRC intent for every register value; the family's {} forms hold \
                     over {} register assignments and {} corruption controls refute; {} — \
                     accepted regression evidence, NOT a formal proof]",
                    form.mnemonic(),
                    credit.forms,
                    credit.instances,
                    credit.controls_refuted,
                    crc::METHOD_GF2
                ),
            },
            Err(detail) => OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::EmittableNeedsProof,
                finding: Some(CoverageFinding::ProofNotDischarged {
                    proof_name: format!("aarch64_crc32_proofs::{}", form.mnemonic()),
                    detail: detail.clone(),
                }),
                note: format!(
                    "aarch64_crc32_proofs::{} REFUSED: {detail}",
                    form.mnemonic()
                ),
            },
        }
    }

    /// The CRC32 row of `opcode` with the family's credit hook INJECTED, so a
    /// test can watch a failing hook turn the row red.
    #[doc(hidden)]
    pub fn audit_aarch64_crc32_with(
        &self,
        opcode: AArch64Opcode,
        credit: &dyn Fn() -> Result<crate::aarch64_crc32_proofs::Crc32Credit, String>,
    ) -> OpcodeAuditRow {
        self.check_crc32_row(format!("AArch64::{opcode:?}"), opcode, credit)
    }

    fn check_trap_expansion_row(&self, display: String, opcode: AArch64Opcode) -> OpcodeAuditRow {
        use crate::aarch64_trap_expansion as trap;
        let fail = |detail: String| OpcodeAuditRow {
            opcode_display: display.clone(),
            class: OpcodeClass::EmittableNeedsProof,
            finding: Some(CoverageFinding::ProofNotDischarged {
                proof_name: format!("aarch64_trap_expansion::{opcode:?}"),
                detail: detail.clone(),
            }),
            note: format!("aarch64_trap_expansion::{opcode:?} REFUSED: {detail}"),
        };
        let own = trap::trap_battery()
            .into_iter()
            .filter(|carrier| carrier.opcode == opcode)
            .count();
        if own == 0 {
            return fail("no form of this carrier is in the trap battery".into());
        }
        match trap::trap_expansion_credit() {
            Ok(credit) => OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::EmittableNeedsProof,
                finding: None,
                note: format!(
                    "TRAP EXPANSION credit [{own} form(s) of this carrier; the family's {} \
                     forms trap exactly when their source condition holds and {} corruption \
                     controls refute; decided in process — accepted regression evidence, NOT a \
                     formal proof]",
                    credit.forms, credit.controls_refuted
                ),
            },
            Err(detail) => fail(detail),
        }
    }

    /// UMULH is emitted in two contexts: the 64-bit checked-umul idiom
    /// (`MUL; UMULH; CMP #0; CSET NE`, bound by the function verifier to
    /// `CheckedUmul_I64`) and the i128 low-product chain of `select_i128_mul`
    /// (`MUL; UMULH; MADD; MADD`), whose `Inst::Overflow { MulOverflow }` flag
    /// is, on AArch64, the guarded `__udivti3`/`__divti3` division identity
    /// (x86-64's adapter emits the division-free limb check instead, OD-224).
    /// The row is covered only when the I64 obligation discharges AND the i128
    /// checked-multiply family holds: its six registered obligations (both
    /// targets' flags; `checked_mul_i128_proofs`, queried by
    /// `CheckedMulI128Form::query`)
    /// exist, are non-degenerate and discharge, and the credit hook accepts —
    /// both sides of every obligation match the native `checked_mul` oracle on
    /// the boundary battery and EVERY negative control refutes. A failing hook
    /// or obligation is a REGRESSION (`ProofNotDischarged` /
    /// `NoMatchingProof`), never a quiet deferral. The default evaluator's
    /// acceptance of these 128-bit obligations is regression evidence, not a
    /// formal proof; the note says so.
    fn check_umulh_row(&self, display: String, hooks: &AArch64AuditHooks<'_>) -> OpcodeAuditRow {
        let fail = |display: String, finding: CoverageFinding, note: String| OpcodeAuditRow {
            opcode_display: display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: Some(finding),
            note,
        };
        let Some((query, category)) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Umulh)
        else {
            return fail(
                display,
                CoverageFinding::NoProofMapping,
                "no opcode_to_proof_query mapping".to_string(),
            );
        };
        let mut notes = Vec::with_capacity(5);
        match self.discharge_one(query, category, MatchCase::Insensitive) {
            Ok(note) => notes.push(note),
            Err((finding, note)) => return fail(display, finding, note),
        }
        for form in crate::checked_mul_i128_proofs::CheckedMulI128Form::ALL {
            match self.discharge_one(
                form.query(),
                ProofCategory::Arithmetic,
                MatchCase::Insensitive,
            ) {
                Ok(note) => notes.push(note),
                Err((finding, note)) => return fail(display, finding, note),
            }
        }
        match (hooks.checked_mul_i128_credit)() {
            Ok(credit) => notes.push(format!(
                "i128 checked-multiply idiom credit [{} obligations discharged, both sides equal \
                 native checked_mul at {} boundary points, {} negative control(s) refuted; \
                 accepted regression evidence, NOT a formal proof; deferred: {}]",
                credit.obligations,
                credit.battery_points,
                credit.controls_refuted,
                crate::checked_mul_i128_proofs::CHECKED_MUL_I128_DEFERRALS.len()
            )),
            Err(detail) => {
                let proof_name = "checked_mul_i128_proofs::checked_mul_i128_credit".to_string();
                return fail(
                    display,
                    CoverageFinding::ProofNotDischarged {
                        proof_name: proof_name.clone(),
                        detail: detail.clone(),
                    },
                    format!("{proof_name} REFUSED: {detail}"),
                );
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
    /// [`CoverageFinding`] plus a note. A first-substring lookup, with each
    /// verifier's case-matching convention; the verifiers no longer credit it
    /// (E0.2), so a row found here is inventory, not instruction credit.
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

/// A bound-memory row from its credit hook's verdict.
fn check_bound_memory_row(
    display: String,
    opcode: AArch64Opcode,
    credit: Result<crate::bound_memory_row_credit::BoundMemoryRowCredit, String>,
) -> OpcodeAuditRow {
    match credit {
        Ok(credit) => OpcodeAuditRow {
            opcode_display: display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: None,
            note: format!(
                "BOUND-MEMORY FORM CERTIFICATES [{} form(s) of {opcode:?}: {}; each form \
                 theorem's committed certificate replayed by the independent checker in this \
                 process (Formal); {} representative instruction(s) credited through the \
                 Formal-only rule's clauses 2-4; {} machine defect(s) refuted on the structured \
                 grid and {} word control(s) refuted in process (testing grade)]",
                credit.forms.len(),
                credit.forms.join(", "),
                credit.instructions,
                credit.defects_refuted,
                credit.word_controls_refuted
            ),
        },
        Err(detail) => {
            let proof_name = format!("bound_memory_row_credit::{opcode:?}");
            OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::EmittableNeedsProof,
                finding: Some(CoverageFinding::ProofNotDischarged {
                    proof_name: proof_name.clone(),
                    detail: detail.clone(),
                }),
                note: format!("{proof_name} REFUSED: {detail}"),
            }
        }
    }
}

impl Default for CoverageGate {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod pair_memory_runtime_model_tests {
    use super::*;

    const PAIRS: [AArch64Opcode; 6] = [
        AArch64Opcode::StpRI,
        AArch64Opcode::LdpRI,
        AArch64Opcode::StpPreIndex,
        AArch64Opcode::LdpPostIndex,
        AArch64Opcode::NeonLdpQPost,
        AArch64Opcode::NeonStpQPost,
    ];

    /// The six pair rows stay in the emitted denominator, are never credited
    /// opcode-wide by a width table or a registry model, and are covered only
    /// by the per-form bound-memory credit (L04-P1).
    #[test]
    fn pair_memory_rows_are_credited_only_by_every_form_certificate() {
        let mut wrong = Vec::new();
        for opcode in PAIRS {
            let occurrences = ALL_AARCH64_OPCODES
                .iter()
                .filter(|&&item| item == opcode)
                .count();
            if occurrences != 1
                || classify_aarch64(opcode) != OpcodeClass::EmittableNeedsProof
                || aarch64_deferred_value_op_reason(opcode).is_some()
                || aarch64_width_polymorphic_proofs(opcode).is_some()
                || FunctionVerifier::opcode_to_proof_query(opcode).is_some()
            {
                wrong.push(format!(
                    "{opcode:?}: occurrences={occurrences}, class={:?}, debt={:?}",
                    classify_aarch64(opcode),
                    aarch64_deferred_value_op_reason(opcode)
                ));
            }
        }
        assert_eq!(
            ALL_AARCH64_OPCODES
                .iter()
                .filter(|&&opcode| classify_aarch64(opcode) == OpcodeClass::EmittableNeedsProof)
                .count(),
            302,
            "pair credit must not shrink the emitted denominator (253 with the three \
             TLSDESC slots, before the 29 LL/SC atomic rows; 284 since the emitted typed \
             copies MOVWrr/MOVXrr entered it; 287 with the emitted SubsRI and \
             AddTprelHi12/Lo12; 288 since the emitted FrintnRR entered it as a deferred row; \
             296 since the eight emitted CRC32/CRC32C forms entered it as deferred rows; \
             301 since the five conditional trap carriers left the pseudo/trap bucket; \
             302 since NeonAddpScalar left the fail-closed allowlist, L04-P6)"
        );
        assert!(wrong.is_empty(), "pair rows misclassified: {wrong:#?}");
    }

    #[test]
    fn pair_memory_coverage_audit_cannot_borrow_unbound_static_models() {
        let gate = CoverageGate::with_config(VerificationConfig::with_sample_count(16));
        let report = gate.audit_aarch64_with_bound_memory_credit(&|opcode| {
            crate::bound_memory_row_credit::pair_row_credit(opcode)
                .map(|_| Err("INJECTED: no form certificate".to_string()))
        });
        let qualified = crate::bound_memory_authority::bound_memory_checker_qualification();
        let mut wrong = Vec::new();
        for opcode in PAIRS {
            let display = format!("AArch64::{opcode:?}");
            // Without the per-form credit nothing else covers a pair row.
            let injected = report
                .rows
                .iter()
                .find(|row| row.opcode_display == display)
                .expect("pair row audited");
            if !matches!(
                injected.finding,
                Some(CoverageFinding::ProofNotDischarged { .. })
            ) {
                wrong.push(injected.clone());
            }
            // With it, the row is covered by exactly that credit (on a host
            // whose checker the bound-memory manifest qualifies).
            let row = gate.audit_aarch64(opcode);
            match &qualified {
                Ok(()) => {
                    if row.finding.is_some()
                        || !row.note.starts_with("BOUND-MEMORY FORM CERTIFICATES")
                    {
                        wrong.push(row);
                    }
                }
                Err(_) => {
                    if row.finding.is_none() {
                        wrong.push(row);
                    }
                }
            }
        }
        assert!(
            wrong.is_empty(),
            "{} pair audit rows borrowed unrelated authority: {wrong:#?}",
            wrong.len()
        );
    }
}

#[cfg(test)]
mod fcmp_runtime_model_tests {
    use super::*;

    #[test]
    fn fcmp_cset_rows_are_credited_only_by_the_flag_consumer_family() {
        let gate = CoverageGate::with_config(VerificationConfig::with_sample_count(16));
        // The full registry also contains x86 UCOMIS models with the same
        // `Fcmp_` prefix. Enumerate the AArch64 builders and compare complete
        // obligations instead of accidentally counting that unrelated family.
        let fp_models = crate::lowering_proof::all_fp_lowering_proofs()
            .into_iter()
            .filter(|model| model.name.starts_with("Fcmp_"))
            .collect::<Vec<_>>();
        assert_eq!(fp_models.len(), 28);
        for model in fp_models {
            assert!(
                gate.db.all().iter().any(|cp| cp.obligation == model),
                "missing diagnostic model {}",
                model.name
            );
        }
        let integer_models = crate::lowering_proof::all_comparison_proofs_i32()
            .into_iter()
            .chain(crate::lowering_proof::all_comparison_proofs_i64());
        let mut integer_count = 0;
        for model in integer_models {
            assert!(
                gate.db.all().iter().any(|cp| cp.obligation == model),
                "missing diagnostic model {}",
                model.name
            );
            integer_count += 1;
        }
        assert_eq!(integer_count, 20);
        // Registry presence of the static templates is not what credits the
        // rows: FCMP and CSET are covered only through the NZCV
        // producer/consumer family, and a failing credit hook turns them RED.
        for opcode in [AArch64Opcode::Fcmp, AArch64Opcode::CSet] {
            let row = gate.audit_aarch64(opcode);
            assert_eq!(row.class, OpcodeClass::EmittableNeedsProof);
            assert!(aarch64_width_polymorphic_proofs(opcode).is_none());
            assert!(FunctionVerifier::opcode_to_proof_query(opcode).is_none());
            assert!(row.finding.is_none(), "{row:?}");
            assert!(row.note.contains("NZCV PRODUCER/CONSUMER"), "{}", row.note);
            assert!(row.note.contains("NOT a formal proof"), "{}", row.note);
            let refused = gate
                .audit_aarch64_flag_consumer_with(opcode, &|_| Err("injected refusal".into()))
                .expect("flag-consumer opcode");
            assert!(
                matches!(
                    refused.finding,
                    Some(CoverageFinding::ProofNotDischarged { .. })
                ),
                "{refused:?}"
            );
        }
    }
}

#[cfg(test)]
mod neon_orr_and_tprel_row_tests {
    use super::*;

    /// L04-P11 second review: the ORR (vector) row needs BOTH its register
    /// copy's decoded-word credit and the lanewise obligation the
    /// three-register 16B OR binds; the TLSLE TPREL adds are named deferred
    /// rows with no opcode-wide query.
    #[test]
    fn neon_orr_row_needs_both_bound_shapes_and_tprel_rows_are_deferred() {
        let gate = CoverageGate::with_config(VerificationConfig::with_sample_count(16));
        let row = gate.audit_aarch64(AArch64Opcode::NeonOrrV);
        assert!(row.finding.is_none(), "{row:?}");
        assert!(row.note.starts_with("DECODED-WORD"), "{}", row.note);
        assert!(row.note.contains("three-register 16B OR"), "{}", row.note);

        let without_or = CoverageGate {
            db: ProofDatabase::from_proofs(
                gate.db
                    .all()
                    .iter()
                    .filter(|proof| {
                        !proof
                            .obligation
                            .name
                            .to_lowercase()
                            .contains("orrv.16b lanewise-intent")
                    })
                    .cloned()
                    .collect(),
            ),
            config: VerificationConfig::with_sample_count(16),
        };
        assert!(without_or.db.all().len() < gate.db.all().len());
        let row = without_or.audit_aarch64(AArch64Opcode::NeonOrrV);
        assert_eq!(row.class, OpcodeClass::EmittableNeedsProof);
        assert!(
            row.finding.is_some(),
            "the copy form alone must not credit ORR (vector): {row:?}"
        );

        for opcode in [AArch64Opcode::AddTprelHi12, AArch64Opcode::AddTprelLo12] {
            let row = gate.audit_aarch64(opcode);
            assert!(
                matches!(
                    row.finding,
                    Some(CoverageFinding::DeferredUnfaithfulModel { .. })
                ),
                "{row:?}"
            );
            assert!(FunctionVerifier::opcode_to_proof_query(opcode).is_none());
        }
    }
}

#[cfg(test)]
mod fcsel_runtime_model_tests {
    use super::*;
    use crate::lowering_proof::{all_fcsel_proofs, fcsel_wrong_controls};

    #[test]
    fn fcsel_runtime_denial_preserves_the_diagnostic_model_inventory() {
        // This is finite model evaluation, not formal discharge or evidence
        // that a concrete source/FCSEL pair satisfies a template's premises.
        let config = VerificationConfig::with_sample_count(16);
        let models = all_fcsel_proofs();
        assert_eq!(models.len(), 12);
        for model in &models {
            assert!(!model.is_degenerate(), "{}", model.name);
            assert!(matches!(
                VerificationStrength::for_obligation_with_config(model, &config),
                VerificationStrength::Statistical { sample_count: 16 }
            ));
            assert!(matches!(
                verify_by_evaluation_with_config(model, &config),
                VerificationResult::Valid
            ));
        }
        let mutants = fcsel_wrong_controls();
        assert_eq!(mutants.len(), 8);
        for mutant in &mutants {
            assert!(matches!(
                verify_by_evaluation_with_config(mutant, &config),
                VerificationResult::Invalid { .. }
            ));
        }

        let queries = aarch64_width_polymorphic_proofs(AArch64Opcode::FcselRR).unwrap();
        assert_eq!(queries.len(), 2);
        assert_eq!(queries[0].query, "fcsel_f32");
        assert_eq!(queries[0].encoded_width_bits, 32);
        assert_eq!(queries[1].query, "fcsel_f64");
        assert_eq!(queries[1].encoded_width_bits, 64);
        let row = CoverageGate::with_config(config).audit_aarch64(AArch64Opcode::FcselRR);
        assert_eq!(row.class, OpcodeClass::EmittableNeedsProof);
        assert!(row.finding.is_none(), "{row:?}");
        assert!(row.note.contains("NOT a formal proof"), "{}", row.note);
        assert!(FunctionVerifier::opcode_to_proof_query(AArch64Opcode::FcselRR).is_none());
        eprintln!(
            "FCSEL diagnostic models: 12 finite positives, 8 refuted mutants, 2 width rows; \
             runtime opcode attribution denied"
        );
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

    // Pseudo forms and unconditional traps carry no value obligation; keep
    // this list in sync with `AArch64Opcode::is_pseudo` and the verifier's
    // trap rows (`aarch64_trap_expansion`). Classified in the single exhaustive WILDCARD-FREE
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
        // Unconditional traps: the single word BRK #imm16 (#1 unless a Brk
        // names its immediate), with no condition and no value. The function
        // verifier decides that word exactly (`aarch64_trap_expansion`) and
        // ENC-5 checks it per compile; there is nothing else to prove.
        O::Brk
        | O::TrapOverflow
        | O::TrapBoundsCheck
        | O::TrapNull
        | O::TrapDivZero
        | O::TrapShiftRange => PseudoOrTrap,
        // Conditional trap carriers (L04-P12): each expands late to a compare,
        // a conditional branch over the trap and BRK #1, which must trap
        // exactly when the carrier's source condition (null, zero divisor,
        // bounds, shift range, overflow) holds. Credited by the trap-expansion
        // family's hook (`aarch64_trap_expansion::trap_expansion_credit`).
        O::TrapBoundsCheckExact
        | O::TrapNullIfZero
        | O::TrapDivZeroIfZero
        | O::TrapShiftRangeIfOOB
        | O::TrapOverflowExact => EmittableNeedsProof,

        // ---- Emitted value/effect surface: MUST carry accepted evidence or RED ----
        O::AddRR | O::AddRI | O::SubRR | O::SubRI | O::MulRR | O::Madd | O::Msub | O::Neg => {
            EmittableNeedsProof
        }
        O::SDiv | O::UDiv => EmittableNeedsProof,
        O::CmpRR | O::CmpRI | O::CMPWrr | O::CMPXrr | O::CMPWri | O::CMPXri => EmittableNeedsProof,
        O::Tst => EmittableNeedsProof,
        // CSET stays in the required denominator. It is credited through
        // `aarch64_flag_consumer_proofs`: every producer/width/condition form
        // it binds to per instruction (integer CMP/TST/checked idioms and the
        // decoded FCMP -> CSET family) must discharge, its captured words must
        // decode back, and its controls must refute.
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
        // FMOV (FPR<-FPR scalar copy): the retracted "CopyProp: COPY(x) == x"
        // ledger entry (X==X) still credits nothing. Coverage comes from the
        // decoded-word obligations (`aarch64_value_decode_proofs`, S and D
        // forms): the captured FMOV word's Arm ARM semantics over the whole
        // 128-bit destination register, decided exactly against the copy intent.
        O::FmovFprFpr => EmittableNeedsProof,
        O::FcvtzsRR | O::FcvtzuRR | O::ScvtfRR | O::UcvtfRR | O::FcvtSD | O::FcvtDS => {
            EmittableNeedsProof
        }
        O::Sxtb | O::Sxth | O::Sxtw | O::Uxtb | O::Uxth | O::Uxtw => EmittableNeedsProof,
        // GPR register copy (MOV): the retracted "CopyProp: COPY(x) == x" ledger
        // entry (X==X) still credits nothing. Coverage comes from the
        // decoded-word obligations (`aarch64_value_decode_proofs`: the ORR
        // W/X aliases and the ADD Xd, SP, #0 alias), decided exactly over the
        // full 64-bit destination so a W copy must clear Xd[63:32].
        O::MovR => EmittableNeedsProof,
        // The typed copies are EMITTED: `pipeline::lower_copies` turns every
        // post-allocation GPR `Copy` into MOVWrr/MOVXrr (the opcode fixes the
        // width). They were allowlisted here as "never selected" until L04-P11,
        // which took them out of the denominator while every function with a
        // post-RA copy carried them. Coverage comes from their own decoded-word
        // forms (`aarch64_value_decode_proofs`, MovWrr/MovXrr).
        O::MOVWrr | O::MOVXrr => EmittableNeedsProof,
        // MOVN/MOVK are genuinely emittable, so they stay in the denominator
        // and are never eligible for the never-selected fail-closed allowlist.
        // Their opcode-wide credit comes only from the form-polymorphic gate
        // (`aarch64_form_polymorphic_proofs`): one discharged per-form proof for
        // EVERY legal (width, shift) pair, a missing form leaving the row RED.
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
        // The jump-table BR is bound per compile by `aarch64_switch_binding`
        // (every AArch64 encode): its register is the ADD of the dispatch's
        // ADR base and LDRSW-loaded entry, every table entry lands on its
        // recorded successor and the CMP/B.HI bounds check covers the table.
        O::Br | O::Blr | O::BLR => FailClosedAllowlisted {
            reason: "indirect branch/call target — covered elsewhere (BR: the jump-table \
                     register chain, table entries and bounds check are bound per compile by \
                     aarch64_switch_binding; BLR: register target established by the call \
                     lowering; transfer architecturally fixed)",
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
        //       UMULH is ALSO the high-half step of the i128 low-product chain
        //       (`select_i128_mul`: MUL; UMULH; MADD; MADD), whose checked
        //       multiply is, on AArch64, the guarded __udivti3/__divti3
        //       division identity (OD-224 keeps it there). Its row therefore
        //       additionally requires the i128 checked-multiply family
        //       (`checked_mul_i128_proofs`) through `check_umulh_row`: six
        //       registered obligations (both targets' flags) discharging
        //       and every negative control refuted, or the row is
        //       ProofNotDischarged (L04-P10).
        O::Smulh | O::Umulh => EmittableNeedsProof,

        // (b.1) ADDS #imm has NO lowering emission path (only the RR forms are
        //       selected; its other reference is a scheduler-cost match) and no
        //       AddsRI-specific proof exists. Fail-closed as never-selected rather
        //       than silently binding it to the RR-form proof.
        O::AddsRI => FailClosedAllowlisted {
            reason: "flag-setting immediate form (ADDS #imm) never selected by the lowerer — \
                     fail-closed (no AddsRI emission path; only the RR forms are emitted)",
        },
        // SUBS #imm IS emitted: frame lowering's looped stack probe decrements
        // its counter with `SUBS X16, X16, #1` and branches on it (`B.NE`) for
        // any frame of five or more 4 KiB pages (`frame.rs`). It was listed
        // here as never selected until L04-P11; it is emitted value/flag debt
        // and stays in the denominator as a named deferred (RED) row. The
        // function verifier has no mapping for it, so it blocks promotion.
        O::SubsRI => EmittableNeedsProof,

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
        // Flag-SETTING carry-chain (ADCS/SBCS): emitted by the checked-i128
        // add/sub selection (ADDS lo; ADCS hi; CSET / SUBS lo; SBCS hi; CSET).
        // Covered by the FAITHFUL checked whole-chain obligations
        // (checked_overflow_proofs::all_checked_i128_carry_chain_proofs):
        // the final-NZCV overflow bit rebuilt from limb arithmetic, proven
        // against the native 128-bit overflow definition (the chain VALUE is
        // covered by the iadd/isub whole-chain composition proofs). Width-polymorphic-style dual
        // binding (aarch64_width_polymorphic_proofs) requires BOTH the signed
        // and unsigned chain theorems before the opcode earns coverage.
        O::Adcs | O::Sbcs => EmittableNeedsProof,
        // UMULL: proof_umull_rr. SMULL: its own sign-extending decoded-word
        // obligation (`aarch64_value_decode_proofs`), never UMULL's.
        O::Smull | O::Umull => EmittableNeedsProof,

        // HONESTY (task #61): the old IfConversion ledger entries for CSEL/CSINC/
        // CSNEG are X==X self-equalities and credit nothing. The rows are
        // credited by `aarch64_flag_consumer_proofs` instead: one obligation per
        // (operation, W/X width, reaching CMP/TST/FCMP producer and width,
        // condition), whose machine side executes the independently decoded
        // captured word over the producer's NZCV. (CSINV stays allowlisted — it
        // is never selected by lowering and has no registered proof.)
        O::Csel | O::Csinc | O::Csneg => EmittableNeedsProof,
        O::Csinv => FailClosedAllowlisted {
            reason: "CSINV is encoder-supported but never selected by lowering; emitted \
                     CSEL/CSINC/CSNEG remain RED in the value/effect denominator",
        },
        // FCSEL is emitted by FP Select and stays in the required denominator.
        // Its two-width diagnostic row evaluates representative independent
        // CMP-W-selector,#0 + raw-FPR-bit-mux models from all_fcsel_proofs, with
        // inverted-condition/operand-swap controls. The terms preserve payload
        // bits without FP arithmetic. Finite model acceptance is NOT formal
        // proof and does not establish that an actual FCSEL has the modeled
        // source arms, condition, width, or reaching flags. FunctionVerifier
        // therefore denies opcode-only runtime attribution despite this model
        // inventory; checked source/instruction applicability is still required.
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
        // BFM (bitfield INSERT — read-modify-write) and scalar RBIT are credited
        // by decoded-word obligations (`aarch64_value_decode_proofs`): BFM over
        // every (lsb, width) of the bitfield-insert family at W and X, RBIT
        // against the SWAR butterfly the bit-reverse recognizer matches.
        // ROR-immediate is credited by the per-instruction EXTR-alias
        // reconstruction lane, including its baked immediate and register
        // width; malformed shapes and the #0 move alias fail closed.
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
        O::FrintnRR | O::FrintmRR | O::FrintpRR | O::FrintzRR => EmittableNeedsProof,
        // FEAT_CRC32 checksum steps, selected only inside a function whose
        // admission includes `crc`: value-bearing and emitted, so they stay
        // in the denominator; they are credited by the CRC32 decoded-word
        // family (`aarch64_crc32_proofs`, L04-P1), decided in process.
        O::Crc32B
        | O::Crc32H
        | O::Crc32W
        | O::Crc32X
        | O::Crc32Cb
        | O::Crc32Ch
        | O::Crc32Cw
        | O::Crc32Cx => EmittableNeedsProof,

        // FCMP stays in the required denominator. The 14-condition x 2-width
        // static Boolean models remain diagnostic: a representative comparison
        // cannot certify a raw instruction's operands, width or full NZCV. The
        // row is credited by the per-width packed-NZCV obligations of
        // `aarch64_flag_consumer_proofs` (decoded FCMP word, integer-only
        // FPCompare, all four flags), which the function verifier binds per
        // instruction by operand width.
        O::Fcmp => EmittableNeedsProof,
        // Scalar FMOV-immediate: credited per-instruction via OPERAND
        // RECONSTRUCTION — the machine side is the hardware VFPExpandImm DECODE
        // (a structural bit-assembly, `encode_fmov_imm_bits`) of the 8-bit field
        // the codegen encoder picks, proven to round-trip to the named constant's
        // IEEE bits. A wrong field/placement REFUTES (not `const == const`).
        O::FmovImm => EmittableNeedsProof,

        // GPR<->FPR FMOV is a material bit-preserving value transfer. The shared
        // bitvector-domain identity would be degenerate X==X; coverage comes from
        // the decoded-word obligations (`aarch64_value_decode_proofs`, W<->S and
        // X<->D), whose decoder refuses the unallocated W<->D and X<->S rows.
        O::FmovFprGpr | O::FmovGprFpr => EmittableNeedsProof,

        // (a) Half-precision FCVT genuinely changes the IEEE format (exact widen,
        //     rounded narrow). Coverage comes from the per-direction decoded-word
        //     obligations (`aarch64_value_decode_proofs`, Arm FPConvert vs IEEE
        //     convertFormat), never from a same-expression FPToFP identity.
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
        // above. In the production Certified object inventory the emitted TLS
        // rows promote through the same fail-closed composition as the ordinary
        // eight: the aarch64_elf_tls_reloc_proofs value lane (the ABI range
        // constraints ride inside the obligations as preconditions, each with a
        // paired drop-refutes negative control) plus the exact per-object ELF
        // reparse binding.
        O::LdrGottprel => EmittableNeedsProof,
        // ELF general-dynamic TLS through a TLS descriptor. `TlsDescCall` is
        // the pre-expansion call form: frame lowering replaces it with the
        // four emitted slots (ADRP, LdrTlsdesc, AddTlsdescLo12, BlrTlsdesc)
        // and the encoder rejects an unexpanded one, so it never reaches an
        // object. The emitted slots carry NO value proof: no obligation models
        // the R_AARCH64_TLSDESC_* relocations or the static linker's GD->IE/LE
        // rewrite of these slots. They stay in the required denominator, RED,
        // so proof-required output containing TLSDESC fails closed.
        O::TlsDescCall => FailClosedAllowlisted {
            reason: "pre-expansion TLSDESC call form: expanded by frame lowering into the \
                     emitted LdrTlsdesc/AddTlsdescLo12/BlrTlsdesc slots (which remain RED); \
                     the encoder rejects an unexpanded TlsDescCall, so it never reaches bytes",
        },
        O::LdrTlsdesc | O::AddTlsdescLo12 | O::BlrTlsdesc => EmittableNeedsProof,
        // LDRSW Xt,[Xn,Xm,LSL#2] (the jump-table scaled table-entry load) is
        // credited to the FAITHFUL scaled-EFFECTIVE-ADDRESS proof
        // proof_ldrsw_ro_scaled_addr (AddressMode): `base + (index<<2) ==
        // base + 4*index` (bvshl vs bvmul; a wrong scale REFUTES). HONEST SCOPE:
        // the address-mode credit only — strictly stronger than the degenerate
        // `("load", Memory)` query, NOT a full memory-load proof (the dereference +
        // i32->i64 sext loaded VALUE remains the shared Ldr* unfaithful-load debt).
        O::LdrswRO => EmittableNeedsProof,
        // MovI is accepted through the non-degenerate hw0 MOVZ obligation;
        // AddRIShift12 through the decoded-word obligation over every imm12
        // (`aarch64_value_decode_proofs`). LdrLiteral is never selected.
        O::MovI | O::AddRIShift12 => EmittableNeedsProof,
        O::LdrLiteral => FailClosedAllowlisted {
            reason: "PC-relative literal-load form is encoder-supported but never selected by lowering",
        },
        // ELF local-exec TLS TPREL adds, emitted by ISel for local-exec TLS
        // references (`MRS; ADD ..., LSL #12; ADD`). They are in the
        // denominator as named deferred (RED) rows (L04-P11 second review):
        // the registered TLSLE obligations are relocation-arithmetic
        // identities over TP/S/A that bind no register, word or relocation
        // site, so neither the gate nor the function verifier credits them.
        // ENC-5 decodes their words since L10-P6 (emission redundancy, not
        // an obligation for the instruction).
        O::AddTprelHi12 | O::AddTprelLo12 => EmittableNeedsProof,

        // (a) Writeback memory, system-register, and active atomic families are
        //     emitted effects/values and stay in the denominator. Partial
        //     Memory/Atomic queries do not earn complete-opcode credit.
        O::LdrPreIndex | O::StrPreIndex | O::LdrPostIndex | O::StrPostIndex => EmittableNeedsProof,
        // MRS: credited for the TPIDR_EL0 read only (`aarch64_value_decode_proofs`:
        // system-register selection over a modeled register file). That
        // TPIDR_EL0 holds the thread pointer is the ELF TLS ABI, trust base.
        O::Mrs => EmittableNeedsProof,
        // The `Fence_* -> DMB {ISH,ISHLD,ISHST}` family this entry USED to cite
        // was RETRACTED in #62 as degenerate const==const barrier-code
        // tautologies (`atomic_proofs::aarch64_atomic_proofs` strips them by
        // name), so half of the old justification named evidence that no longer
        // exists. What remains true is the dataflow half, and that is all this
        // reason may claim.
        //
        // DMB carries no value and no proof binds its ORDERING semantics: that is
        // an architectural fact, delegated exactly as LDAR's ordering is. The
        // That gap is now CLOSED for load-load ordering: `atomic_proofs`
        // carries an interleaving observer model (two loads at distinct
        // locations, each with its own observed-state selector) whose controls
        // refute both a missing barrier and a store-only barrier. What remains
        // delegated is the architectural guarantee itself, carried as an explicit
        // hypothesis exactly as FEAT_LSE2 alignment is in the single-copy proof.
        // DMB still has no VALUE to check, so it stays an allowlist row.
        O::Dmb => FailClosedAllowlisted {
            reason: "non-value fence: load-load ordering IS bound, by the interleaving \
                     obligations DMB_ISH / DMB_ISHLD (operand-sensitive on CRm, so \
                     ISHST earns no load-load credit and fails closed); the barrier's \
                     own architectural guarantee stays a delegation, carried as an \
                     explicit hypothesis, and dataflow_integrity keeps Fence \
                     side-effecting so no pass reorders across it",
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
        // Baseline (non-LSE) LL/SC atomics. The opaque pseudos appear in every
        // pre-allocation stream the function verifier sees; the exclusives and
        // CLREX are the post-RA expansion's emitted words. All are value/effect
        // opcodes with no faithful obligation: explicit RED denominator rows.
        O::Ldaxr
        | O::Stlxr
        | O::Ldxr
        | O::Ldxrb
        | O::Ldxrh
        | O::Ldaxrb
        | O::Ldaxrh
        | O::Stxr
        | O::Stxrb
        | O::Stxrh
        | O::Stlxrb
        | O::Stlxrh
        | O::Clrex
        | O::LlscRmw8
        | O::LlscRmw16
        | O::LlscRmw32
        | O::LlscRmw64
        | O::LlscCmpSwap8
        | O::LlscCmpSwap16
        | O::LlscCmpSwap32
        | O::LlscCmpSwap64
        | O::Ldxp
        | O::Ldaxp
        | O::Stxp
        | O::Stlxp
        | O::LlscLoad128
        | O::LlscStore128
        | O::LlscRmw128
        | O::LlscCmpSwap128 => EmittableNeedsProof,
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
        // bitwise ops are lane-width-INDEPENDENT over the register, but the
        // obligation states the 16B arrangement: the function verifier binds it
        // per instruction to the 16B shape only
        // (`aarch64_value_decode_proofs::neon_bitwise_16b_bound_query`), whose
        // word ENC-5 decodes, and refuses the 8B (V64, Q = 0) shapes. ORR's
        // register copy binds a decoded-word form instead, and its row needs
        // both (`audit_aarch64_with`).
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
        // (see `neon_popcount_wrong_encoding_controls`). CNT uses its single
        // opcode query; UADDLP requires both emitted arrangements through
        // `aarch64_width_polymorphic_proofs`, while concrete instructions bind
        // arrangement-sensitively in the function verifier.
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
        // `neon_saddlp_wrong_encoding_controls`). The opcode audit requires both
        // arrangements and concrete instructions bind to the exact one.
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
        // NEON horizontal reduces and permutes are CREDITED by their faithful
        // obligations (neon_lowering_proofs), each bound by
        // `opcode_to_proof_query` and, where the opcode is emitted at several
        // forms, demanded form by form through
        // `aarch64_width_polymorphic_proofs`:
        //   * Horizontal reduces: UMAXV.4S (all_neon_umaxv_proofs, a balanced
        //     bvuge tree against the linear bvugt fold) and ADDP Dd, Vn.2D
        //     (all_neon_addp_proofs, L04-P6: the doubleword sum sliced from the
        //     raw D-halves against `encode_neon_addp_scalar_2d`; `.2D` is the
        //     only architectural form of scalar ADDP). ADDP left the
        //     fail-closed allowlist when its model, obligation and controls
        //     landed; the codegen encoder and ENC-5 already admitted only
        //     `.2D` into a `D` destination. No lowering selects ADDP yet, so
        //     this is the one emittable-class row with no emitter today;
        //     LIMITATIONS.md and ARCHITECTURE.md disclose it beside the
        //     emitted-row counts.
        //   * Permutes and lane moves: DUP (element: all_neon_dup_elem_proofs;
        //     general: all_neon_dup_gen_proofs), INS (general:
        //     all_neon_ins_gen_proofs), MOVI (all_neon_movi_proofs, symbolic
        //     imm8), REV32 (all_neon_rev32_proofs), REV64/RBIT/UMOV (above).
        //   * Every model these obligations' machine sides use is checked
        //     against this CPU, over every encoder-admitted form, by the live
        //     silicon differential (tests/aarch64_neon_silicon_differential.rs,
        //     testing evidence).
        //   * Post-index load/store (NeonLd1Post/St1Post/LdpQPost/StpQPost):
        //     each emitted transfer is stated by the word-bound memory-effect
        //     decomposition (aarch64_memory_effect: fields, writeback, every
        //     loaded register half and stored window), decided in process per
        //     compile and checked against silicon; under the Formal-only
        //     bound-memory rule that is never credit by itself. The four rows
        //     are credited by their form theorems' replayed certificates (the
        //     Q-pair forms of `aarch64_pair_memory_forms`, the LD1/ST1 forms
        //     of `aarch64_neon_structure_forms`, L04-P1), with that
        //     decomposition as clause 2.
        O::NeonDupGen
        | O::NeonDupElem
        | O::NeonInsGen
        | O::NeonMovi
        | O::NeonUmaxv
        | O::NeonAddpScalar
        | O::NeonRev32V => EmittableNeedsProof,
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
        // Variable-count rotate (ROL r/m64, CL — RMW-Stage-1-style admission:
        // nothing emits it yet). Covered by Phase-2 reconstruction credit: the
        // `X86SourceOp::RotlVar` obligation pits the bridge's masked
        // shl/shr/or rotate idiom (the exact expansion the Stage-2 peephole
        // will delete) against the independent hardware-masked
        // `encode_rol_rcl_masked` — TOTAL (no count<width precondition; both
        // sides mask mod width), with the machine half keyed off the real
        // opcode. ROR-for-ROL, a dropped wrap half, an unmasked machine
        // count, a wrong mask width, and SHL-for-ROL all REFUTE (rotl_var
        // controls in reconstruction_x86.rs). The Stage-2 variable-rotate
        // peephole is admission-gated on this very reconstruction
        // discharging Valid.
        O::RolRCl => EmittableNeedsProof,
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
        // immediate constant) once mapped ONLY to the degenerate "x86_64: MOV r,imm
        // materializes constant" ledger entry (X==X — const==const, no independent
        // model). That entry stays RETRACTED and credits nothing. The row is now
        // credited by `x86_encoding_proofs`: an independent SDM-derived decode of
        // the REAL emitted bytes compared, as a 64-bit register write, against
        // the machine-IR intent — see `audit_x86`. It stays EmittableNeedsProof,
        // IN the denominator, and says nothing about whether the lowering chose
        // the right constant.
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

        // Plain LEA (base+disp32) and SIB LEA (base+index*scale+disp32) carry
        // their address on the BYTE-LEVEL credit in `x86_addressing_proofs`,
        // which decodes the real emitted ModR/M+SIB. The older claim here —
        // that `reconstruct_x86_lea` rebuilds the machine side INDEPENDENTLY —
        // was false: it builds both sides from the same `recon_base`/
        // `recon_index` leaves with the same encoders, so it is X==X and
        // refutes no wrong base, index, scale or displacement. LEA is the
        // cleanest member of the family, because it accesses no memory and the
        // address IS the value.
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
        // the proof_x86_learip_symbol_riprel / proof_x86_movriprel_got_eff_addr
        // rows of x86_64_lowering_proofs::all_x86_64_proofs).
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
        // Scaled-index 64-bit memory MOV `[base+index*scale+disp]` (SIB).
        // The ADDRESS facet is carried by `x86_addressing_proofs`
        // (`x86_opcode_has_address_credit`), which decodes the REAL emitted
        // bytes. It is NOT carried by `x86_reconstruct_effective_address`: that
        // helper builds both halves from the SAME operand with identical
        // encoders, so it is `X == X` and no wrong base/index/scale/disp can
        // refute through it. The VALUE facet is still the reconstruction's,
        // mapped by `opcode_to_proof_query` (MemLoad/MemStore, 64-bit).
        O::MovRMSib | O::MovMRSib => EmittableNeedsProof,
        // 32-bit SIB siblings (X10): the same byte-level ADDRESS credit at
        // 32-bit load/store width as MovRM32/MovMR32.
        O::MovRM32Sib | O::MovMR32Sib => EmittableNeedsProof,
        // 8-bit SIB siblings: the SAME shared EA reconstruction at 8-bit
        // load/store width as MovRM8/MovMR8. Closes the gap that kept EVERY
        // byte-indexed access (`&[u8]`, `Vec<u8>`, `[u8; N]`) out of indexed
        // addressing, since the SIB opcode set was 64/32-bit and float only.
        // Nothing new is trusted: a wrong base/index/scale/disp REFUTES through
        // the byte-level ADDRESS credit (never through
        // `x86_reconstruct_effective_address`, which is X==X), and the access
        // WIDTH is fixed by the opcode (8) exactly as it is for MovRM8/MovMR8.
        O::MovRM8Sib | O::MovMR8Sib => EmittableNeedsProof,
        // Memory-destination RMW ALU (XOR/ADD [mem], r64, base+disp and SIB
        // forms). Covered by Phase-2 reconstruction credit: the
        // `X86SourceOp::MemRmw` obligation composes the MemStore shape
        // (address half + stored-value half) with the MemAlu shape (the real
        // machine ALU encoder over a load of the same EA), on the shared
        // `x86_reconstruct_effective_address`. A wrong ALU op, a dropped/wrong
        // source and a degenerate plain store REFUTE through that
        // reconstruction, whose machine half IS keyed off the real opcode. A
        // wrong base/index/scale/disp does NOT refute through it — that half is
        // X==X — and is carried instead by the byte-level ADDRESS credit. Nothing emits these opcodes yet (Stage 1: proofs +
        // plumbing only; the Stage-2 fusion peephole is admission-gated on
        // this very reconstruction discharging Valid).
        O::XorMR | O::AddMR | O::XorMRSib | O::AddMRSib => EmittableNeedsProof,
        // Scalar-FP SIB loads: the COMPOSITION of the two proofs directly above.
        // The effective address is carried by the byte-level ADDRESS credit
        // (SOURCE = the machine-IR intent, MACHINE = an INDEPENDENT SDM decode
        // of the emitted bytes), and the loaded value is the same
        // Load_F64/Load_F32 memory proof that already covers MovsdRM/MovssRM.
        // A wrong base/index/scale/disp REFUTES via the address credit; a wrong
        // access width or lane REFUTES via the FP-load half. It is NOT the
        // `x86_reconstruct_effective_address` half that carries the address —
        // that one is X==X and refutes nothing. Mapped by `opcode_to_proof_query`
        // (MemLoad, width fixed by the opcode: 8 bytes for sd, 4 for ss).
        O::MovsdRMSib | O::MovssRMSib => EmittableNeedsProof,
        // MOVSXD r64, [base+index*scale+disp] (SIB) — the scaled SIGN-EXTENDING
        // load. It was introduced for the original 4-byte jump-table design and
        // NOTHING EMITS IT: the active path uses 8-byte deltas through the
        // already-credited MovRMSib. It was allowlisted OUT of the denominator
        // with a reason that asked for "a genuine scaled-sext-load proof
        // (aarch64 LdrswRO analogue) before default-ON", and that is now what
        // covers it, so the row is back IN the denominator where emitted
        // value/effect debt belongs — the same posture as the unemitted
        // XorMR/AddMR RMW quartet and RolRCl, which are proven before anything
        // may select them.
        //
        // The credit is NOT the `x86_reconstruct_effective_address` family the
        // old reason named. That family builds BOTH sides of a SibMemAddr from
        // the same operand with the same `recon_base`/`recon_index` symbols, so
        // it cannot refute a wrong base, a wrong index or a base/index swap, and
        // it has no sign-extending load model at all. `x86_movsxd_sib_proofs`
        // supplies the missing shape: an INDEPENDENT SDM-derived decode of the
        // REAL emitted bytes, denoted as a write to the 64-bit destination root
        // over per-register leaves NAMED FROM THE DECODED REGISTER NUMBERS,
        // against a parametric statement of the machine-IR intent. The two sides
        // are structurally distinct on purpose — a SHIFT by the raw SIB scale
        // field against a MULTIPLY by the entry size, and an explicit
        // sign-extend of a zero-filling load against a signed load — and the
        // comparison REFUSES a machine side identical to the source side, so
        // this cannot decay into the X==X the retracted memory proofs were. The
        // address facet is EXACT for every 64-bit base and index (`base +
        // index*s == base + (index << ss)` iff `s == 1 << ss`); the value facet
        // is decided over a witness family required to exercise BOTH sign cases.
        O::MovsxdRMSib => EmittableNeedsProof,
        // The ZERO-EXTENDING loads `movzx r32, m8/m16` (`0F B6`/`0F B7`, plain
        // `[base + disp]`, byte SIB, and the volatile twins): the selector's
        // load for every byte and word. Credited by the byte-level ADDRESS
        // lane, which for these rows also carries the DESTINATION facet (the
        // decoded production's SDM register write against the zero-extended
        // access value, over dirty old registers and set top bits, with the
        // merging-MOV, sign-extending and other-width models refuting through
        // the same comparison), AND the MemLoad VALUE reconstruction. The
        // volatile twins additionally need the VOL-x86 trace leg, exactly as
        // the merging volatile forms do.
        O::MovzxRM8 | O::MovzxRM16 | O::MovzxRM8Sib | O::VolatileMovzxRM8 | O::VolatileMovzxRM16 => {
            EmittableNeedsProof
        }

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
        // vector value. RECONSTRUCTED as TWO 64-bit halves at effective
        // addresses `ea` (low) and `ea+8` (high), little-endian. A swapped half,
        // a wrong half offset and a wrong access width read different bytes ⇒
        // REFUTE: those are one-sided structural differences in the two-half
        // model. A wrong base/index/scale/disp does NOT refute there — the
        // scalar `x86_reconstruct_effective_address` builds both of its address
        // halves from the SAME operand with identical encoders, so that half is
        // X==X. The ADDRESS facet is carried by the byte-level credit in
        // `x86_addressing_proofs`, which decodes the real emitted bytes. MOVDQA carries the HONEST `ea % 16 == 0`
        // precondition (SSE MOVDQA #GP-faults on a non-16-aligned address); MOVDQU
        // does not. Credited COVERED via reconstruction in `audit_x86` before any
        // DB lookup (see `reconstruct_x86_v128_mem_{load,store}` +
        // tests/reconstruction_x86.rs packed-move positives/refutations). The
        // reg-reg form MOVDQA{RR} stays separate explicit copy debt.
        O::MovdquRM | O::MovdquMR | O::MovdqaRM | O::MovdqaMR
        // Volatile V128 loads/stores require the same two-facet coverage.
        | O::VolatileMovdquRM | O::VolatileMovdquMR | O::VolatileMovdqaRM
        | O::VolatileMovdqaMR => EmittableNeedsProof,
        // Scaled-index 128-bit MOVDQU load/store: the SAME reconstruction as the
        // plain-MemAddr forms directly above, differing ONLY in the
        // effective-address shape — and the EA is the one half
        // `x86_reconstruct_effective_address` does NOT carry: it builds both of
        // its address halves from the SAME operand with identical encoders, so
        // that half is X==X and refutes no address error. The ADDRESS comes
        // from the byte-level credit in `x86_addressing_proofs`, which decodes
        // the real emitted ModR/M+SIB bytes; a swapped / dropped / wrong-width
        // value half REFUTES via the value half, exactly as for
        // MovdquRM/MovdquMR. Nothing new is trusted; no allowlist.
        //
        // Only the UNALIGNED form gains a SIB sibling. MOVDQA's proof carries the
        // honest `ea % 16 == 0` precondition, and re-forming the address as
        // base+index*scale is precisely the rewrite that could break it.
        O::MovdquRMSib | O::MovdquMRSib => EmittableNeedsProof,

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
        //      honesty, same footing as slices 1-3). Weak spurious failure and
        //      invalid failure orderings stay fail-closed upstream. The NARROW
        //      i8/i16 forms are a SEPARATE mechanism — see directly below; they
        //      do NOT inherit these i32/i64 theorems.
        O::Cmpxchg => EmittableNeedsProof,
        // NARROW i8/i16 LOCK CMPXCHG (`F0 0F B0` / `F0 66 0F B1`), actively
        // selected for AtomicU8/U16 `compare_exchange`. GENUINELY RECONSTRUCTED
        // (not X==X, and NOT the i32/i64 `Cmpxchg_I{32,64}` theorems) via
        // `X86SourceOp::CmpxchgNarrow`: SOURCE = `encode_trust_ir_cmpxchg`, a
        // transcription of the pinned trust-ir interpreter's `Inst::CmpXchg` arm
        // over three w-bit VALUE leaves; MACHINE = `encode_lock_cmpxchg_narrow`,
        // an SDM transcription over the FULL 64-bit RAX, the FULL 32-bit source
        // carrier and a byte-addressable memory array. ONE `64 + 2w + 9`-bit
        // joint obligation carries six facets: RAX[63:w] PRESERVED (the partial
        // AL/AX write), returns-old, the conditional store, the ADJACENT cell
        // untouched (which pins the store WIDTH), a WINDOWED FRAME PROBE byte
        // anywhere in [EA-128, EA+127] untouched, and ZF == success.
        // Non-degeneracy is a PRECONDITION of this credit, not a property of a
        // test elsewhere: `reconstruct_x86_cmpxchg_narrow` returns None (=> RED)
        // if its two sides are the same expression, because the shared
        // reconstruction credit rule asks only for `is_reconstructed() && Valid`.
        //
        // The two effective addresses (`encode_lea_base_disp` and the trust_ir
        // `Iadd` chain) are NOT an independence pillar and are never compared:
        // for the `[base+disp]` form this row covers they are the SAME SmtExpr
        // node. What they buy is a FRAME — every read-back is taken at the
        // SOURCE address, so a machine model at a different address refutes.
        // They buy NO address teeth: an obligation rebuilt at a perturbed
        // operand is exactly as Valid (the teeth audit measured this
        // semantically; a structural version of it had credited these two rows
        // with address teeth). The ADDRESS is the byte-level
        // `x86_addressing_proofs` lane's, and the gate credits these rows only
        // when BOTH that lane and this reconstruction discharge
        // (`x86_compare_exchange_joint_audit_row`).
        //
        // The width lives ONLY in the opcode — `reg_class_for_type` maps BOTH i8
        // and i16 to a Gpr32 carrier — so binding these to the i32 proofs would
        // be the degenerate-green trap. `narrow_cmpxchg_never_binds_the_wide_
        // cmpxchg_proofs` and the `cmpxchg_narrow_class_trap_32_bit_model_
        // refutes` control exist to make that route fail. Controls: a
        // zero-extending or 32-bit-write RAX merge, either wrong machine width,
        // the Gpr32 class trap, an unconditional store, a suppressed store, a
        // returns-desired variant, a missing failure load, a backwards /
        // wide-compare / wrong-bit flag, swapped roles, the wrong source byte, a
        // store whose byte order disagrees with the model's load order, a wrong
        // EA, a neighbour clobber, a rogue store elsewhere in the +/-128-byte
        // window and a clean-carrier SOURCE claim ALL REFUTE
        // (tests/reconstruction_x86.rs `cmpxchg_narrow`, a target of
        // `scripts/soundness_check.sh` TRUST_CG_GATES).
        //
        // NOT CLAIMED: atomicity / LOCK serialization / ordering (the same
        // Intel-SDM axiom the atomic load/store/RMW and MFENCE rows rest on);
        // the opcode->BYTES link, which THIS obligation does not state (ENC-3's
        // `decode_check.rs` now COVERS these two opcodes — it allowlisted them
        // under `NARROW_CMPXCHG` until this repair — and derives the width, the
        // LOCK prefix and the byte-register identity from the emitted bytes);
        // memory byte ORDER (the crate-wide little-endian primitives are shared
        // by both sides and are trust base); the memory frame BEYOND the
        // +/-128-byte probe window; the identity of the accumulator with the
        // surrounding MOVs (fresh leaves, as in the Idiv/Div reconstruction);
        // and the tie from `w` to the LIR type (the gate has only an opcode).
        // See `reconstruct_x86_cmpxchg_narrow`'s doc comment for the full list.
        O::Cmpxchg8 | O::Cmpxchg16 => EmittableNeedsProof,
        // The 128-bit atomic-load PSEUDO (`XOR EAX,EAX; XOR EDX,EDX;
        // XOR EBX,EBX; XOR ECX,ECX; LOCK CMPXCHG16B m128`), selected for the
        // 128-bit atomic LOAD (`AtomicU128/AtomicI128::load`; core's
        // `atomic_load::<u128/i128>`). Credited JOINTLY (like the narrow
        // forms): ADDRESS from the byte-level `x86_addressing_proofs` lane over
        // captured `F0 REX.W 0F C7 /1` encodings; VALUE GENUINELY
        // RECONSTRUCTED via `X86SourceOp::AtomicLoadCmpxchg16b`: MACHINE =
        // `encode_atomic_load_cmpxchg16b`, the four SDM XOR transcriptions
        // feeding the SDM CMPXCHG16B transcription over the INCOMING
        // RAX/RDX/RBX/RCX and a byte-addressable memory array, so the zeroing
        // the load depends on is part of the modeled instruction; SOURCE = the
        // trust-ir `AtomicLoad`, plus the pinned trust-ir `CmpXchg` at 128 bits
        // against the bare CMPXCHG16B transcription at general inputs. Eleven
        // facet equalities (the evaluator stops at 128 bits). A facet with
        // identical sides fails the reconstruction closed. NOT CLAIMED:
        // atomicity/LOCK/ordering (the SDM axiom), bytes (ENC-3 decodes all
        // five instructions), alignment #GP and CX16 availability (the type's
        // alignment; the function's `cmpxchg16b` claim, checked by the adapter
        // floor), the read-back copies' binding to RAX/RDX. Controls:
        // tests/reconstruction_x86.rs `cmpxchg16b`.
        O::AtomicLoadCmpxchg16b => EmittableNeedsProof,
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
        // PUNPCKLQDQ. CORRECTION (this comment previously claimed the row had
        // been "PROMOTED OUT of the red-debt block ... Do NOT re-add"): that
        // promotion NEVER TOOK EFFECT and the claim was wrong. 0cb31507
        // (2026-08-25) only moved `O::Punpcklqdq` between two `classify_x86`
        // arms — BOTH of which return `EmittableNeedsProof`, so nothing changed
        // — and never touched `x86_deferred_value_op_reason`, which `audit_x86`
        // consults BEFORE any credit path, nor `expected_red`. The RED row from
        // e5238cc1 (2026-07-23) has been in force the whole time.
        //
        // IT IS NOW CLOSED, and by the route that correction named. The row's
        // deferral reason demanded a faithful cross-lane shuffle obligation "for
        // the opcode's exact element width and low/high half", and the two
        // controls it said were missing — the WRONG HALF (PUNPCKHQDQ) and the
        // WRONG ELEMENT WIDTH (PUNPCKLDQ) — are both in
        // `x86_sse_lane_proofs::sse_model_controls`, where each must REFUTE
        // before the credit is given. It was NOT promoted by deleting a table
        // entry: the `X86SourceOp::PackLowQwords` reconstruction is still the
        // character-for-character `X == X` it always was and still credits
        // nothing here. The credit comes from the SSE lane family's bit-level
        // routing denotation, which is a different obligation entirely.
        | O::Punpcklqdq
        | O::Andpd
        | O::Andps => EmittableNeedsProof,

        // THE SSE LANE FAMILY. These nine (with `Punpcklqdq` in the arm above,
        // ten) were RED for one stated reason: every reconstruction the gate had
        // was a per-lane same-width scalar model, and none of these is one — a
        // permutation, a hidden third operand, a reduction to RFLAGS, a
        // reduction to a GPR, an interleave, a saturating narrow, a whole-register
        // copy. `x86_sse_lane_proofs` supplies the missing shape: an EXACT
        // bit-level ROUTING denotation. What each of these instructions produces
        // is a rearrangement of the bits of its operands, so its meaning is a
        // total function from result-bit index to "which bit of which operand",
        // and two such functions denote the same instruction iff their tables are
        // equal — a DECISION, not a sampled equivalence, and not the per-lane
        // shape that never fitted.
        //
        // The machine side of that denotation is the SDM Operation text keyed by
        // an INDEPENDENTLY DECODED opcode byte; the source side is a parametric
        // statement of the machine-IR intent that never sees a byte. They are
        // credited in `audit_x86_with` through
        // `x86_sse_lane_proofs::sse_lane_discharges_valid`, which withholds the
        // credit unless every wrong-half, wrong-width, wrong-granularity,
        // dropped-implicit-register and byte-framing control REFUTES.
        //
        // Both this arm and the one above return `EmittableNeedsProof`, so which
        // arm an opcode sits in has never affected the gate — that is exactly how
        // the earlier `Punpcklqdq` "promotion" managed to change nothing. The
        // authority is `x86_deferred_value_op_reason` plus the credit path, not
        // this grouping.
        //
        // NOTE: the MEMORY forms MOVDQA{RM,MR} (and MOVDQU{RM,MR}) left this list
        // earlier — they are GENUINELY RECONSTRUCTED as two 64-bit halves at
        // ea/ea+8 (see the arm above). Do NOT re-add the RM/MR forms here.
        // PMULUDQ likewise: its even-dword widening multiply is exactly a
        // same-width i64x2 lane op on the qword lanes' low dwords. PINSR*/PEXTR*
        // are split out below because the current pipeline never selects them.
        O::Pshufd
        | O::Pmovmskb
        | O::MovdqaRR
        | O::Punpckldq
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
///   * Emitted scalar constants are value materialization and stay IN the
///     denominator. `i32.const`/`i64.const` are credited by the INDEPENDENT
///     spec-derived signed-LEB decode of the real emitted immediate;
///     `f32.const`/`f64.const` by an INDEPENDENT spec-derived decode of their
///     raw IEEE-754 payload, compared bit-exactly with the pattern the trust-ir
///     carrier denotes. Reserved, never-selected `v128.const` remains
///     explicitly excluded.
///   * Float/int conversions, reinterpret bitcasts, and popcnt are reconstructed
///     value ops and remain in the denominator.
///   * `f*.min`/`f*.max` are emitted only inside the FMin/FMax lowering, so they
///     are credited by that emitted SEQUENCE (`wasm_float_binop_proofs`), not
///     by a per-opcode reconstruction; `copysign` by a reconstruction arm plus
///     its emitted body. `memory.copy`/`memory.fill` are credited by the
///     guarded MemCopy/MemSet SEQUENCE a trust-ir `MemCopy`/`MemSet` lowers
///     to (`wasm_bulk_memory_proofs`). `memory.fill` is emitted only there;
///     `memory.copy` is also emitted, with a constant nonzero size, by the
///     aggregate / lane / sret moves (`emit_copy`), which that credit does
///     not cover and which rest on the lane differentials.
///   * NOTHING in the lowerer selects a v128 value: its `ValType` has no v128,
///     `layout::carrier_of` refuses `Ty::Vector`, and every function declaring
///     a target feature (simd128 among them) is refused. The four lane-wise
///     SIMD value ops and the v128 load/store/const forms are therefore
///     excluded as never selected; the gates that pin this ratio scan a
///     live-compiled corpus for their `0xfd` prefix
///     (`wasm_value_domain::never_selected_opcodes_in`). The lane-wise reconstruction of the four
///     value ops stays built and tested (`reconstruction_wasm`), so they
///     re-enter this denominator unchanged when selection lands.
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
        // clz/ctz, rotl/rotr, eqz and copysign are RECONSTRUCTED from their
        // real bytes (a byte of the other count, direction or width refutes or
        // fails closed; copysign over the operands' bit patterns, with its
        // emitted body fixing the operand order).
        O::I32Clz
        | O::I64Clz
        | O::I32Ctz
        | O::I64Ctz
        | O::I32Rotl
        | O::I64Rotl
        | O::I32Rotr
        | O::I64Rotr
        | O::I32Eqz
        | O::I64Eqz
        | O::F32Copysign
        | O::F64Copysign => EmittableNeedsProof,
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

        // ---- f*.min / f*.max: emitted inside the FMin/FMax lowering, credited
        // by that emitted sequence ----
        O::F32Min | O::F64Min | O::F32Max | O::F64Max => EmittableNeedsProof,
        // `select` chooses a value (RECONSTRUCTED: swapped values or an inverted
        // condition refute); `memory.copy`/`memory.fill` are credited by the
        // captured guarded MemCopy/MemSet bodies (`wasm_bulk_memory_proofs`),
        // which do not cover `emit_copy`'s constant-size aggregate moves.
        // All are emitted and owe evidence.
        O::Select | O::MemoryCopy | O::MemoryFill => EmittableNeedsProof,

        // Scalar constants are actively emitted value materialization, credited
        // only by an INDEPENDENT decode of the real immediate (const==const
        // would be degenerate): the signed-LEB decoder for the integer forms.
        O::I32Const | O::I64Const => EmittableNeedsProof,
        // The FLOAT constants are emitted by the same `Const` lowering arm
        // (`lower.rs` pushes 0x43/0x44 followed by the raw little-endian IEEE-754
        // payload), so they belong IN this denominator too; their credit is the
        // independent float-payload decoder and the stated f32 narrowing.
        O::F32Const | O::F64Const => EmittableNeedsProof,
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
            reason: "linear-memory load/store — covered elsewhere: the wasm memory-model family \
                         (byte-addressed little-endian array theory, wasm_memory_proofs) plus the \
                         per-opcode P3 value-domain inventory (GateArch::WasmValueDomain, which \
                         audits opcode bytes 0x28/0x29/0x36/0x37 among the full 0x28..=0x3e \
                         block), not a per-instruction dataflow value equivalence",
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

        // ---- SIMD / v128 LANE-WISE value ops: NEVER SELECTED ----
        // The lane-wise reconstruction exists (the machine side is rebuilt from
        // the REAL 0xfd sub-opcode, and a wrong sub-opcode or lane width
        // refutes in `reconstruction_wasm`), but the lowerer cannot emit these:
        // there is no v128 carrier and simd128 is refused. Crediting them would
        // count evidence for code that is never emitted, so they are excluded
        // for the same reason v128.load/store/const are, and return to the
        // denominator the moment selection lands.
        O::I32x4Add | O::I32x4Mul | O::F32x4Add | O::F32x4Mul => FailClosedAllowlisted {
            reason: "v128 lane-wise value op, never selected by the current wasm lowerer: its \
                     ValType has no v128, layout::carrier_of refuses Ty::Vector, and every \
                     function declaring a target feature (simd128 among them) is refused; not in \
                     the emitted set. The lane-wise reconstruction stays built and refutable \
                     (reconstruction_wasm) so the row re-enters the denominator unchanged when \
                     selection lands",
        },
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
///
/// `MovRI` LEFT THIS TABLE. It was deferred for exactly one reason — "no
/// independent immediate decode/value obligation is registered; the former
/// const==const model was a degenerate X==X". `x86_encoding_proofs` now carries
/// a decoder for the MOV-immediate family written from the Intel SDM's
/// instruction format (legacy prefixes, REX, the one-byte opcode map, ModR/M
/// for group 11, the operand-size attribute) rather than by inverting the
/// encoder — it models `C6 /0`, `C7 /0`, AH..BH and the sign-extending
/// `REX.W C7 /0 id`, none of which the encoder emits. The obligation decodes
/// the REAL emitted bytes, applies the SDM's register-write rules (64-bit as
/// is, 32-bit ZERO-extended, 8/16-bit preserving the upper bits), and compares
/// the resulting write to the 64-bit root register against the write the
/// machine-IR intent (register NAME, i64 immediate) means — an exact decision
/// over every prior register value. It also pins CANONICALITY (every prefix
/// byte and REX bit present must be load-bearing; the x86 analogue of wasm's
/// padded-LEB pin) and exact framing. `audit_x86` credits the row only through
/// `x86_encoding_proofs::mov_imm_discharges_valid`, which refuses unless every
/// captured encoding holds, all 11 emitted physical form classes are present,
/// and EVERY negative control — wrong register, flipped REX.B, sign-for-zero
/// extension in both directions, truncated imm64, wrong-width form, wrong
/// opcode, every single-byte immediate corruption, dropped forced REX,
/// redundant prefixes, bad framing, every source-side re-claim — refutes FOR
/// ITS STATED REASON CLASS. If that hook ever stops discharging, the row
/// returns RED as `ProofNotDischarged`, not as a quiet deferral.
///
/// What crediting it does NOT say, so the row cannot be over-read: nothing
/// about whether the LOWERING chose the right constant or register (a wrong one
/// encodes and decodes perfectly); nothing about whether an out-of-width
/// immediate was intended (the source semantics is `imm mod 2^w`, the
/// optimizer's own model); nothing about the form being the shortest; nothing
/// about placement or dataflow; nothing about the hand-assembled raw-byte
/// movabs in the JIT profile-counter trampolines (not `MovRI`, not in this
/// inventory); nothing COMPARED about RFLAGS, the other registers or memory —
/// the obligation's denotation is the destination root register alone, "MOV
/// writes no flags" is SDM trust base for the four accepted productions, and
/// what is enforced is CLOSURE over them (a flag-clobbering `XOR r,r` zeroing
/// idiom refutes); and the ISA rules themselves are TRANSCRIBED from the SDM
/// with no silicon differential. `x86_encoding_proofs::X86_MOV_IMM_DEFERRALS`
/// carries the full list as data. Nothing in that design reaches the rows
/// below: they are value/effect SEMANTICS questions, not immediate-decode ones.
pub fn x86_deferred_value_op_reason(opcode: X86Opcode) -> Option<&'static str> {
    // THE TABLE IS EMPTY. Every x86 emitted value/effect opcode that was once
    // deferred has since been given the obligation its reason named — the ten
    // SSE lane rows, MovRI, the narrow CMPXCHG pair, MovsxdRMSib, and finally
    // the sixteen volatile rows. The function is retained rather than deleted
    // because it is the mechanism by which a FUTURE opcode is recorded as
    // honest debt, and because `audit_x86` consults it before any credit path:
    // a new row with no obligation belongs here, named, not quietly credited.
    let _ = opcode;
    // THE TEN SSE LANE ROWS LEFT THIS TABLE. Each was deferred for a reason
    // that named exactly what was missing, and `x86_sse_lane_proofs` now
    // supplies it — an INDEPENDENT SDM-derived decode of the real emitted
    // bytes, and an EXACT bit-level routing denotation compared against a
    // parametric statement of the machine-IR intent:
    //
    //   * PSHUFD wanted "an independently decoded imm8-controlled
    //     lane-permutation obligation". The machine side now derives the
    //     permutation from the DECODED imm8 by the SDM's ORDER-field
    //     convention while the source side states the intended permutation
    //     independently, so the `_MM_SHUFFLE` argument-order bug refutes.
    //   * PMOVMSKB wanted "a faithful cross-lane sign-bit reduction to GPR".
    //     Its denotation is 64 bits wide, so the bit index (7, not 0), the
    //     lane order, and the 32-bit destination's ZERO-EXTENSION are all
    //     compared facets.
    //   * MOVDQA{RR} wanted "an independently decoded 128-bit
    //     bit-preservation obligation". It has one — and only that: the
    //     credit is a decode of the real bytes to the full-width copy with
    //     the intended direction and registers. It does NOT claim MOVDQA
    //     differs from MOVDQU in VALUE (it does not); that separation is the
    //     mnemonic-identity conjunct.
    //   * PUNPCK{LBW,HBW,LDQ,LQDQ} wanted "a faithful cross-lane shuffle
    //     obligation for the opcode's exact element width and low/high
    //     half". The WRONG HALF and WRONG ELEMENT WIDTH controls are both
    //     registered and both must refute before the credit is given.
    //   * PTEST wanted "a faithful whole-vector reduction to the complete
    //     observable RFLAGS effect". All six status flags are modelled; ZF
    //     and CF are anchored against native silicon in the gate test.
    //   * PBLENDVB wanted "a faithful three-input value obligation including
    //     its implicit XMM0 mask register". XMM0 is named by register
    //     NUMBER, so aliasing with an explicit operand is modelled exactly,
    //     and the dropped-implicit-register control refutes.
    //   * PACKUSWB wanted "a faithful signed-saturating narrow plus
    //     lane-pack obligation". The lane pack is in the bit table; the
    //     narrow is settled EXHAUSTIVELY over all 65536 inputs.
    //
    // They are credited in `audit_x86_with`, and the credit is WITHHELD
    // unless every negative control refutes. A hook that stops discharging
    // surfaces as `ProofNotDischarged`, deliberately NOT as a
    // `DeferredUnfaithfulModel`, so the tests that require every x86 RED row
    // to be named deferral debt fail loudly rather than absorbing it.
    // THE SIXTEEN VOLATILE ROWS LEFT THIS TABLE. Their reason asked for one
    // obligation covering BOTH "the complete load/store value or memory
    // effect" AND "preservation of the observable volatile access/
    // optimizer-ordering boundary", and said that "a byte-identical plain
    // MOV proof alone is insufficient". Every clause of that is now met,
    // and by a CONJUNCTION rather than by any single proof:
    //
    //   VALUE    — these opcodes now map to the same MemLoad/MemStore
    //              reconstruction their byte-identical plain siblings use,
    //              and that reconstruction must discharge `Valid`.
    //   ADDRESS  — `x86_addressing_proofs` decodes the real emitted
    //              ModR/M+SIB bytes; the encoder emits volatile and plain
    //              through one arm, so the same decoder reads both.
    //   BOUNDARY — `x86_volatile_trace`. Its hazard battery (elide,
    //              duplicate, widen, narrow, redirect, reclass, reorder)
    //              runs INSIDE its credit hook, and a benign block-layout
    //              permutation is required NOT to refute. It is ENFORCED
    //              per compile and fails closed at BOTH the selection
    //              boundary (VOL-2: the LIR's VolatileLoad/Store against
    //              the opcode ISel chose) and the optimizer boundary
    //              (VOL-1: before against after the passes).
    //
    // `x86_volatile_joint_audit_row` requires all three. If any one stops
    // discharging, the row is RED as `ProofNotDischarged` naming that leg
    // (a regression, not debt); it does not fall back to this table or to
    // the ADDRESS row, so the credit cannot decay into the "byte-identical
    // plain MOV proof" this reason rejected. This table is consulted BEFORE
    // the joint row, so re-adding a volatile row here makes it deferral
    // debt again.
    None
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
/// DEFERRED (cannot be faithfully credited yet), return the TRUE auditable
/// reason it is left RED. Returns `None` for the credited value ops and for
/// every non-`EmittableNeedsProof` opcode.
///
/// HONESTY: these opcodes are value-bearing and stay IN the value-equivalence
/// denominator (RED), NOT allowlisted-out. THE TABLE IS EMPTY; the function is
/// kept because it is the mechanism by which a FUTURE emitted op without an
/// obligation is recorded as honest debt, and `audit_wasm` consults it before
/// reporting a wiring gap.
///
/// What left it, and on what evidence (each credit is pinned by
/// `tests/coverage_gate_tests.rs`, with its negative controls asserted to
/// refute in the target that carries the evidence):
///
///   * `i32.const`/`i64.const` — an INDEPENDENT spec-derived signed-LEB decode
///     of the real emitted immediate at canonical length
///     (`wasm_encoding_proofs::const_immediate_discharges_valid`).
///   * `f32.const`/`f64.const` — an INDEPENDENT spec-derived decode of the real
///     emitted little-endian IEEE-754 payload, compared BIT-EXACTLY with the
///     pattern the trust-ir binary64 carrier denotes; for `f32.const` through a
///     roundTiesToEven narrowing stated from the format definitions, so a
///     rounding bug refutes (`wasm_encoding_proofs::float_const_immediate_discharges_valid`).
///   * `copysign` — a reconstruction arm over the operands' bit patterns
///     (`wasm_function_verifier`), plus the captured emitted body, which fixes
///     the operand order the arm assumes.
///   * `f.min`/`f.max` — the captured emitted FMin/FMax BODY executed under the
///     spec semantics against the relational trust-ir contract
///     (`wasm_float_binop_proofs`); the `-0.0`/`+0.0` tie is credited under
///     trust-ir's unpinned reading, and a control shows a pinned reading
///     refutes.
///   * `memory.copy`/`memory.fill` — they were RED because the lowering trapped
///     on a zero-byte range past the memory, which trust-ir defines as a no-op.
///     The lowering now guards the op with `if (n != 0)`, and the captured
///     guarded MemCopy/MemSet BODIES are executed under the spec semantics
///     against the relational trust-ir contract (`wasm_bulk_memory_proofs`);
///     the unguarded body is a negative control that refutes at exactly that
///     zero-byte out-of-memory class.
///
/// What crediting the constants does NOT say, so the rows cannot be over-read:
/// nothing about whether the LOWERING chose the right constant — a wrong value
/// encodes and decodes perfectly — and nothing about stack discipline.
pub fn wasm_deferred_value_op_reason(opcode: WasmOpcode) -> Option<&'static str> {
    // Every emitted value op is credited above (reconstruction, the LEB and
    // float-payload decoders, the FMin/FMax body or the guarded bulk-memory
    // body) or is not `EmittableNeedsProof`.
    let _ = opcode;
    None
}

/// Classify a P3 value-domain opcode byte. `None` for a byte that is NOT on the
/// P3 surface at all — the caller enumerates the surface, so `None` here means
/// the enumeration and the classifier disagree (a wiring bug), never a silently
/// skipped opcode.
///
/// A P3 byte the lowerer emits is `EmittableNeedsProof`: the credited ones
/// because they carry discharging reconstructions, the deferred ones because
/// their debt stays IN the denominator as a named
/// [`CoverageFinding::DeferredUnfaithfulModel`] row — `br_table`,
/// `memory.size`, `memory.grow` and data segments are emitted (or about to be)
/// and owe evidence. The ONLY exclusion is the allowlist's case (a): the 12
/// bytes the lowerer never selects
/// ([`crate::wasm_value_domain::WASM_VALUE_DOMAIN_UNSELECTED`]), whose
/// obligations stay built so they re-enter unchanged when selection lands.
pub fn classify_wasm_value_domain(byte: u8) -> Option<OpcodeClass> {
    if let Some(reason) = crate::wasm_value_domain::value_domain_unselected(byte) {
        return Some(OpcodeClass::FailClosedAllowlisted { reason });
    }
    if crate::wasm_semantics::decode_mem_op(byte).is_some()
        || crate::wasm_semantics::decode_sign_extend(byte).is_some()
        || crate::wasm_value_domain::value_domain_deferral(byte).is_some()
    {
        return Some(OpcodeClass::EmittableNeedsProof);
    }
    None
}

/// The audit row for one NAMED P3 deferral.
///
/// Deliberately `EmittableNeedsProof` + [`CoverageFinding::DeferredUnfaithfulModel`]:
/// RED, IN the denominator, carrying the deferral's own reason. These are NOT
/// `FailClosedAllowlisted` — that variant requires "covered elsewhere" to be
/// TRUE, and for `br_table` the relooper argument has not been extended to the
/// n-way edge, while `memory.size`/`memory.grow` and data segments have no gate
/// at all yet. Saying "covered elsewhere" would be a claim the repo cannot back.
fn wasm_value_domain_deferral_row(
    deferral: &'static crate::wasm_value_domain::WasmValueDomainDeferral,
) -> OpcodeAuditRow {
    OpcodeAuditRow {
        opcode_display: format!("wasm::{}", deferral.name),
        class: OpcodeClass::EmittableNeedsProof,
        finding: Some(CoverageFinding::DeferredUnfaithfulModel {
            reason: deferral.reason,
        }),
        note: format!(
            "HONESTLY DEFERRED (RED in denominator); owed by: {} — {}",
            deferral.family, deferral.reason
        ),
    }
}

// ---------------------------------------------------------------------------
// WebAssembly P4 family 1 (CFG structural) — row builders
// ---------------------------------------------------------------------------

/// The audit row for one CFG anti-tautology mutant.
///
/// A `MustBeRefuted` mutant is the family's TEETH: it is credited only when the
/// checker actually refuted it, and a mutant that slips through is a
/// [`CoverageFinding::ProofNotDischarged`] RED row, because an invariant a wrong
/// module satisfies proves nothing.
///
/// A `KnownBlindSpot` mutant is NEVER credit. It is the executable measurement
/// of a named deferral, so it is RED with the mutant's own description as its
/// reason. That leaves the same gap counted twice — once here as a measurement,
/// once below as the named property — which understates coverage rather than
/// overstating it, the only direction this gate is allowed to err in.
fn wasm_cfg_mutant_row(
    outcome: &crate::wasm_cfg_proofs::MutantOutcome,
    description: &'static str,
) -> OpcodeAuditRow {
    use crate::wasm_cfg_proofs::MutantExpectation;

    let display = format!("wasm-cfg::mutant `{}`", outcome.name);
    match outcome.expectation {
        MutantExpectation::MustBeRefuted if outcome.as_expected => OpcodeAuditRow {
            opcode_display: display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: None,
            note: format!(
                "REFUTED by the structural checker over the mutated module's own bytes — {}. \
                 The refutation is the evidence the matching invariant is not vacuous: {}",
                description, outcome.verdict
            ),
        },
        MutantExpectation::MustBeRefuted => OpcodeAuditRow {
            opcode_display: display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: Some(CoverageFinding::ProofNotDischarged {
                proof_name: outcome.name.to_string(),
                detail: format!(
                    "the checker did NOT refute a module it must reject: {}",
                    outcome.verdict
                ),
            }),
            note: format!(
                "VACUOUS: {description}. An invariant a deliberately-wrong module still satisfies \
                 is not evidence"
            ),
        },
        MutantExpectation::KnownBlindSpot => OpcodeAuditRow {
            opcode_display: display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: Some(CoverageFinding::DeferredUnfaithfulModel {
                reason: description,
            }),
            note: format!(
                "HONESTLY DEFERRED (RED in denominator): a DECLARED BLIND SPOT, run and reported \
                 rather than omitted. Observed: {} (declared outcome {}). It is the executable \
                 measurement of a named deferral listed separately below, so this gap is counted \
                 twice — understating coverage, never overstating it",
                outcome.verdict,
                if outcome.as_expected {
                    "matched"
                } else {
                    "DRIFTED — the family's own gate test owns that failure"
                }
            ),
        },
    }
}

/// The audit row for one NAMED CFG deferral.
///
/// Deliberately `EmittableNeedsProof` plus [`CoverageFinding::DeferredUnfaithfulModel`]:
/// RED, IN the denominator. The first entry is the family's own headline —
/// relooper BISIMULATION — kept RED on purpose, so nothing in this audit can be
/// read as proving the relooper correct.
fn wasm_cfg_deferral_row(
    deferral: &'static crate::wasm_cfg_proofs::WasmCfgDeferral,
) -> OpcodeAuditRow {
    OpcodeAuditRow {
        opcode_display: format!("wasm-cfg::{}", deferral.name),
        class: OpcodeClass::EmittableNeedsProof,
        finding: Some(CoverageFinding::DeferredUnfaithfulModel {
            reason: deferral.reason,
        }),
        note: format!(
            "HONESTLY DEFERRED (RED in denominator); owed by: {} — {}",
            deferral.family, deferral.reason
        ),
    }
}

/// The audit row for one CFG invariant STATEMENT.
///
/// Excluded from the denominator on purpose, under the variant's case (b): the
/// statement's evidence is the mutant rows in this same audit, and counting the
/// sentence as well as the refutation that gives it teeth would credit one piece
/// of evidence twice. The row exists so the statement — and, load-bearingly, its
/// own `does_not_cover` clause — is visible in the audit log rather than only in
/// the source.
fn wasm_cfg_invariant_row(
    invariant: &'static crate::wasm_cfg_proofs::CfgInvariantRow,
) -> OpcodeAuditRow {
    OpcodeAuditRow {
        opcode_display: format!("wasm-cfg::{}", invariant.id),
        class: OpcodeClass::FailClosedAllowlisted {
            reason: "invariant STATEMENT — covered elsewhere IN THIS SAME AUDIT: its evidence is \
                     the anti-tautology mutant rows above, which are what make it non-vacuous. \
                     Counting the sentence as well as the refutation would credit one piece of \
                     evidence twice, and the family's no-argument battery does not exercise every \
                     statement (there is no br_table in the reference module), so a blanket credit \
                     would hand one statement its neighbours' teeth",
        },
        finding: None,
        note: format!(
            "STATEMENT: {} | REFUTES: {} | DOES NOT COVER: {}",
            invariant.statement, invariant.refutes, invariant.does_not_cover
        ),
    }
}

// ---------------------------------------------------------------------------
// WebAssembly P4 families 2/3 (memory / call ABI) — row builders
// ---------------------------------------------------------------------------

/// The audit row for one ABI anti-tautology guard.
///
/// Same contract as the CFG mutants: a `MustRefute` guard earns credit only by
/// actually refuting, and a `KnownBlind` one is RED with the reason taken from
/// the [`crate::wasm_abi_proofs::WASM_ABI_DEFERRALS`] entry that owns it.
fn wasm_abi_guard_row(
    outcome: Result<crate::wasm_abi_proofs::GuardOutcome, String>,
) -> OpcodeAuditRow {
    use crate::wasm_abi_proofs::{GuardExpectation, WASM_ABI_DEFERRALS};

    let outcome = match outcome {
        Ok(o) => o,
        Err(why) => {
            return OpcodeAuditRow {
                opcode_display: "wasm-abi::guard COULD NOT RUN".to_string(),
                class: OpcodeClass::EmittableNeedsProof,
                finding: Some(CoverageFinding::ProofNotDischarged {
                    proof_name: "wasm ABI anti-tautology guard".to_string(),
                    detail: why.clone(),
                }),
                note: format!("a guard could not be applied at all, so it proves nothing: {why}"),
            };
        }
    };

    let display = format!("wasm-abi::guard `{}`", outcome.name);
    match outcome.expectation {
        GuardExpectation::MustRefute if outcome.refuted => OpcodeAuditRow {
            opcode_display: display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: None,
            note: format!(
                "REFUTED: the mutation of the fixture's REAL emitted bytes was caught — {}. This \
                 is what makes the matching obligations and structural checks non-vacuous",
                outcome.detail
            ),
        },
        GuardExpectation::MustRefute => OpcodeAuditRow {
            opcode_display: display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: Some(CoverageFinding::ProofNotDischarged {
                proof_name: outcome.name.to_string(),
                detail: format!("the mutation was NOT caught: {}", outcome.detail),
            }),
            note: "VACUOUS: a byte mutation the family must catch went through unrefuted"
                .to_string(),
        },
        GuardExpectation::KnownBlind { deferral } => {
            let reason = WASM_ABI_DEFERRALS
                .iter()
                .find(|d| d.name == deferral)
                .map(|d| d.reason)
                .unwrap_or(
                    "a declared blind spot whose owning deferral is not in WASM_ABI_DEFERRALS — a \
                     wiring gap in the family's own bookkeeping, reported RED rather than hidden",
                );
            OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::EmittableNeedsProof,
                finding: Some(CoverageFinding::DeferredUnfaithfulModel { reason }),
                note: format!(
                    "HONESTLY DEFERRED (RED in denominator): a DECLARED BLIND SPOT owned by the \
                     `{deferral}` deferral, run and reported as NOT refuted rather than omitted. \
                     Observed: {}. Counted here AND as its named deferral below — the same gap \
                     twice, which understates coverage rather than overstating it",
                    outcome.detail
                ),
            }
        }
    }
}

/// The audit row for one NAMED memory / call-ABI deferral.
///
/// `EmittableNeedsProof` plus [`CoverageFinding::DeferredUnfaithfulModel`]: RED,
/// IN the denominator. Five of the nine are the HOST's under
/// `crates/trust-cg-codegen/src/wasm/OWNERSHIP.md`; being someone else's
/// obligation is a reason to name an owner, not a reason to leave the row out.
fn wasm_abi_deferral_row(
    deferral: &'static crate::wasm_abi_proofs::WasmAbiDeferral,
) -> OpcodeAuditRow {
    OpcodeAuditRow {
        opcode_display: format!("wasm-abi::{}", deferral.name),
        class: OpcodeClass::EmittableNeedsProof,
        finding: Some(CoverageFinding::DeferredUnfaithfulModel {
            reason: deferral.reason,
        }),
        note: format!(
            "HONESTLY DEFERRED (RED in denominator); owed by: {} ({}) — {}",
            deferral.owner, deferral.citation, deferral.reason
        ),
    }
}

/// Append ledger `L04-P3`'s named IEEE 754 testing evidence
/// ([`crate::fp_ieee_evidence::gate_note`]) to a scalar FP row's note.
///
/// A pure note append: the row's class and finding are returned unchanged, so
/// the evidence can never move a row into or out of the accepted count. An
/// opcode the evidence does not name is returned as is.
pub fn with_named_fp_ieee_evidence(opcode: AArch64Opcode, row: OpcodeAuditRow) -> OpcodeAuditRow {
    match crate::fp_ieee_evidence::gate_note(opcode) {
        Some(note) => OpcodeAuditRow {
            note: format!("{}; {note}", row.note),
            ..row
        },
        None => row,
    }
}

/// Evidence hooks of the AArch64 audit. [`CoverageGate::audit`] uses the real
/// ones; the `#[doc(hidden)]` seams inject failing or anticipated ones.
struct AArch64AuditHooks<'a> {
    value_credit: &'a dyn Fn(
        AArch64Opcode,
    )
        -> Result<crate::aarch64_value_decode_proofs::A64ValueCredit, String>,
    volatile_credit: &'a dyn Fn() -> Result<
        crate::volatile_access_preservation::VolatilePreservationCredit,
        String,
    >,
    /// Replaces the audit of a volatile row's plain counterpart.
    plain_row: Option<&'a dyn Fn(AArch64Opcode) -> OpcodeAuditRow>,
    /// The i128 checked-multiply idiom credit the `Umulh` row also requires
    /// (`checked_mul_i128_proofs::checked_mul_i128_credit`).
    checked_mul_i128_credit:
        &'a dyn Fn() -> Result<crate::checked_mul_i128_proofs::CheckedMulI128Credit, String>,
    /// The opcode-level credit of a bound-memory row (scalar or atomic):
    /// `None` for any other opcode (`bound_memory_row_credit`).
    bound_memory_credit: &'a BoundMemoryCreditHook,
}

/// The bound-memory row credit hook's type.
type BoundMemoryCreditHook =
    dyn Fn(
        AArch64Opcode,
    ) -> Option<Result<crate::bound_memory_row_credit::BoundMemoryRowCredit, String>>;

/// The real bound-memory row credit: the atomic, scalar and pair rows.
fn real_bound_memory_credit(
    opcode: AArch64Opcode,
) -> Option<Result<crate::bound_memory_row_credit::BoundMemoryRowCredit, String>> {
    crate::bound_memory_row_credit::atomic_row_credit(opcode)
        .or_else(|| crate::bound_memory_row_credit::scalar_row_credit(opcode))
        .or_else(|| crate::bound_memory_row_credit::pair_row_credit(opcode))
        .or_else(|| crate::bound_memory_row_credit::neon_row_credit(opcode))
}

/// Evidence hooks of the x86-64 audit. [`CoverageGate::audit`] uses
/// [`X86AuditHooks::REAL`]; each `#[doc(hidden)]` `audit_x86_with_*` seam
/// replaces the hooks it names and keeps the rest real.
struct X86AuditHooks<'a> {
    movri_credit: &'a dyn Fn() -> Result<crate::x86_encoding_proofs::MovImmCredit, String>,
    sse_lane_credit: &'a dyn Fn() -> Result<crate::x86_sse_lane_proofs::SseLaneCredit, String>,
    movsxd_sib_credit:
        &'a dyn Fn() -> Result<crate::x86_movsxd_sib_proofs::MovsxdSibCredit, String>,
    /// The ADDRESS leg of the ADDRESS row, the COMPARE-EXCHANGE joint row and
    /// the volatile JOINT row.
    address_credit:
        &'a dyn Fn() -> Result<crate::x86_addressing_proofs::MemMovAddressCredit, String>,
    /// The VALUE leg of the same three rows: whether the opcode's
    /// reconstruction discharges `Valid` under the gate's config.
    value_credit: &'a dyn Fn(X86Opcode, &VerificationConfig) -> bool,
    /// The BOUNDARY leg, which only the volatile JOINT row requires.
    volatile_trace_credit:
        &'a dyn Fn() -> Result<crate::x86_volatile_trace::VolatileTraceCredit, String>,
}

impl X86AuditHooks<'static> {
    const REAL: Self = Self {
        movri_credit: &crate::x86_encoding_proofs::mov_imm_discharges_valid,
        sse_lane_credit: &crate::x86_sse_lane_proofs::sse_lane_discharges_valid,
        movsxd_sib_credit: &crate::x86_movsxd_sib_proofs::movsxd_sib_discharges_valid,
        address_credit: &crate::x86_addressing_proofs::mem_mov_address_credit,
        value_credit: &x86_reconstruction_discharges_valid,
        volatile_trace_credit: &crate::x86_volatile_trace::volatile_trace_credit,
    };
}

/// The plain load/store whose dereference/value or memory-effect evidence a
/// volatile AArch64 access row must also carry (X-OPCODES-P6). The volatile
/// forms are byte-identical to these.
pub fn aarch64_volatile_plain_counterpart(opcode: AArch64Opcode) -> Option<AArch64Opcode> {
    use AArch64Opcode as O;
    Some(match opcode {
        O::VolatileLdrRI => O::LdrRI,
        O::VolatileLdrbRI => O::LdrbRI,
        O::VolatileLdrhRI => O::LdrhRI,
        O::VolatileStrRI => O::StrRI,
        O::VolatileStrbRI => O::StrbRI,
        O::VolatileStrhRI => O::StrhRI,
        _ => return None,
    })
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
        O::FrintnRR => Some(
            "emitted FRINTN lacks decoded-word f32/f64 nearest-even value, NaN, FPCR and FPSR \
             obligations; native hardware comparisons do not establish formal correctness",
        ),
        // The eight CRC32/CRC32C rows LEFT this table (L04-P1) when
        // `aarch64_crc32_proofs` supplied the decoded-word polynomial-division
        // value obligation the reason named: per form, the Arm ARM pseudocode
        // of the independently decoded word (BitReverse, Poly32Mod2 with
        // 0x04C11DB7 / 0x1EDC6F41, BitReverse; Xd[63:32] cleared) against the
        // reflected LSB-first shift register of the intrinsic (literal
        // 0xEDB88320 / 0x82F63B78), decided for every register value by
        // GF(2)-affine evaluation in process (`gf2_affine_decide`, testing
        // grade), with word, width, polynomial, operand, bit- and byte-order
        // controls refuted and a silicon differential on this CPU. The gate
        // credits them as accepted regression evidence, not a formal proof.
        // TST LEFT this table when its COMPLETE opcode-wide authority landed.
        //
        // The per-CONDITION standalone NZCV obligations (one per width and
        // N/Z-derived or composite-C condition) are CONSUMER VIEWS: the
        // function verifier binds each concrete TST to the obligation of the
        // consuming instruction's condition code. On their own they could NOT
        // clear this row -- for exactly the reason MOVK needed a form-polymorphic
        // gate, crediting one condition's theorem opcode-wide would be the
        // unfaithful inheritance #62 retracted.
        //
        // What promotes TST is the WHOLE-INSTRUCTION packed-NZCV theorem
        // (`cmp_combine_proofs::proof_tst_packed_nzcv`), which pins all four
        // flags at once and is registered at BOTH emitted widths. This gate
        // demands both of them through `aarch64_width_polymorphic_proofs`
        // above, so a single-width or partial-flag model still fails closed
        // here; nothing is credited from a single condition-code observation.
        // Every scalar memory row LEFT this table (L04-P1) when the gate learned
        // to demand, for EVERY legal form of the opcode, what the Formal-only
        // rule credits per instruction: a replayed committed certificate of the
        // form theorem, representative instructions credited through clauses
        // 2-4 (the instruction-derived lane for W/X forms, the exact word-bound
        // memory-effect decomposition for H/S/D/Q forms), and every machine
        // defect refuted (`bound_memory_row_credit`). The six volatile rows are
        // audited by `check_volatile_row` BEFORE this table: their preservation
        // facet (X-OPCODES-P6) is decided per compile and credited through its
        // control battery, and each is credited with its plain counterpart.
        // The four pair rows (StpRI, LdpRI, StpPreIndex, LdpPostIndex) and the
        // NEON Q-pair post-index rows LEFT this table under the same per-form
        // rule (clause 2: the pair lane's concrete-word check); the static frame
        // alignment, slot non-overlap, single-slot restore and representative
        // memory models stay diagnostic and credit nothing.
        // MovR, FmovFprFpr, FmovFprGpr, FmovGprFpr (X-OPCODES-P8) and Smull,
        // Bfm, Rbit, AddRIShift12, Mrs (X-OPCODES-P9) LEFT this table when
        // `aarch64_value_decode_proofs` supplied what each reason named as
        // missing: an independent decode of the encoder's word, given its Arm
        // ARM semantics over the whole destination register (W-write and
        // scalar-FP zeroing included) and compared with the machine-IR intent,
        // with refuting controls for the named hazards — SMULL's sign
        // extension (the UMULL word and the zero-extending claim both refute),
        // BFM's read-modify-write (UBFM/SBFM and a wrong `immr` formula
        // refute), RBIT's bit order (REV/REV16 refute), the dropped LSL #12,
        // TPIDR_EL0's selection (TPIDRRO_EL0/TPIDR_EL1/MSR refute) and the
        // cross-class FMOV widths (the unallocated W<->D and X<->S rows).
        // UMULL left earlier through lowering_proof::proof_umull_rr; SMULL has
        // its own sign-extending obligation and inherits nothing from it.
        // MOVWrr and MOVXrr (L04-P11) were never in this table: they sat in
        // the fail-closed allowlist as "never selected" although post-RA copy
        // lowering emits them. They entered the denominator with their own
        // typed decoded-word forms, whose controls include the width the
        // opcode (not the operand view) fixes.
        // Csel, Csinc and Csneg (X-OPCODES-P5) LEFT this table when
        // `aarch64_flag_consumer_proofs` supplied the independent instruction
        // model the reason named as missing: per-(operation, width, reaching
        // producer, condition) obligations over the independently decoded
        // captured word, with wrong-condition, swapped-arm, wrong-width,
        // stale-flag and arm-transform controls refuted.
        // FcvtHS, FcvtHD, FcvtSH and FcvtDH (X-OPCODES-P7) LEFT this table when
        // `aarch64_value_decode_proofs` gave each direction and width its own
        // decoded-word obligation: the Arm ARM FPConvert transcription of the
        // emitted FCVT word against an independently written IEEE 754
        // convertFormat intent (`aarch64_fcvt_half`), bit-exact over the whole
        // destination register, exhaustive for the binary16-source forms and
        // battery-plus-sampled for the rounded ones, with wrong-direction,
        // wrong-rounding, wrong-format, default-NaN and denormal-flush controls
        // refuted. Both sides assume the default FPCR.
        O::AddTprelHi12 | O::AddTprelLo12 => Some(
            "emitted ELF local-exec TLS TPREL add (`ADD Xd, Xn, #:tprel_hi12:S, LSL #12` / \
             `ADD Xd, Xn, #:tprel_lo12_nc:S`) has no obligation bound to the instruction or its \
             bytes: the registered TLSLE identities are bit-slice arithmetic over TP/S/A naming \
             no register, word or relocation site (the LO12 one a two-instruction composite); \
             ENC-5 decodes the words (class, LSL #12, registers, zero imm12, relocation hole) \
             since L10-P6, which is emission redundancy and binds no obligation",
        ),
        // SubsRI LEFT this table (L04-P1) when `aarch64_subs_imm_proofs`
        // supplied the obligation the reason named: for each width, every
        // location the independently decoded word writes (the destination,
        // W writes clearing bits 63:32, and N, Z, C, V from Arm's
        // `AddWithCarry(Rn, NOT(imm), 1)`) against the comparison the
        // operands name, each decided for every register value by the
        // bit-serial automaton in process (testing grade), with ADDS, SUB,
        // width, shifted-immediate, off-by-one, register and flag-meaning
        // controls refuted and a silicon differential reading NZCV on this
        // CPU. Accepted regression evidence, not a formal proof.
        O::LdrTlsdesc | O::AddTlsdescLo12 | O::BlrTlsdesc => Some(
            "emitted ELF TLS-descriptor (TLSDESC) slot has no faithful obligation: the \
             R_AARCH64_TLSDESC_* relocation values, the resolver's returned TP-relative offset \
             and the static linker's in-place GD->IE/LE rewrite of the four fixed-register slots \
             are not modeled; the encode-time shape check, independent decode check and \
             object/link tests are regression evidence, not proof",
        ),
        // The 46 single-instruction atomic rows (LDAR/STLR x3, CAS x4, SWP x4,
        // LD<op> x32; X-OPCODES-P2) LEFT this table when each emitted width of
        // each operation got a faithful form theorem stating the returned old
        // value AND the memory effect (`aarch64_atomic_forms`, 48 forms, every
        // one with a committed, independently replayed certificate), a
        // word-bound decomposition decided exactly in process
        // (`aarch64_atomic_effect`), ENC-5 binding and a silicon differential;
        // the gate demands every form's authority (`bound_memory_row_credit`).
        // Ordering is the L03-P3 table's (`aarch64_memory_order`).
        O::Ldxr | O::Ldxrb | O::Ldxrh | O::Ldaxr | O::Ldaxrb | O::Ldaxrh => Some(
            "emitted load-exclusive (LL/SC retry-loop head) lacks a faithful returned-value, \
             exclusive-monitor and acquire-ordering obligation; encoder/decoder agreement and \
             native C11 differential runs are tests, not a value or monitor proof",
        ),
        O::Stxr | O::Stxrb | O::Stxrh | O::Stlxr | O::Stlxrb | O::Stlxrh => Some(
            "emitted store-exclusive lacks a faithful conditional memory-effect, status-result, \
             exclusive-monitor and release-ordering obligation; status/overlap encoding checks and \
             native contention runs do not establish linearizability or progress",
        ),
        O::Ldxp | O::Ldaxp | O::Stxp | O::Stlxp => Some(
            "emitted 128-bit pair exclusive lacks a faithful paired returned-value, conditional \
             memory-effect, single-copy-atomicity (write-back) and ordering obligation; encoder, \
             decoder and native C11 differential agreement is testing evidence only",
        ),
        O::LlscLoad128 | O::LlscStore128 | O::LlscRmw128 | O::LlscCmpSwap128 => Some(
            "opaque 128-bit LL/SC pseudo has no faithful paired atomic value, memory-effect, \
             write-back or ordering obligation; its post-RA LDXP/STXP expansion is decode- and \
             natively tested only",
        ),
        O::Clrex => Some(
            "emitted CLREX (LL/SC compare-failure exit) has no exclusive-monitor state model or \
             obligation; its word is decode-checked but its monitor effect is unproven",
        ),
        O::LlscRmw8 | O::LlscRmw16 | O::LlscRmw32 | O::LlscRmw64 => Some(
            "opaque LL/SC read-modify-write pseudo has no faithful atomic returned-old-value, \
             memory-update, ordering or retry-loop obligation; its post-RA LDXR/op/STXR/CBNZ \
             expansion is decode- and natively tested only",
        ),
        O::LlscCmpSwap8 | O::LlscCmpSwap16 | O::LlscCmpSwap32 | O::LlscCmpSwap64 => Some(
            "opaque LL/SC compare-and-swap pseudo has no faithful success predicate, returned-old \
             value, conditional memory effect, ordering or retry-loop obligation; its post-RA \
             expansion is decode- and natively tested only",
        ),
        // The NEON LD1/ST1 post-index rows LEFT this table (L04-P1) when the
        // form theorem their reason named landed
        // (`aarch64_neon_structure_forms`: LD1/ST1 x the seven arrangements,
        // the element loop of the encoded fields against the operands'
        // LDR/STR Dt|Qt intent, every register byte or every memory byte and
        // the writeback), each with a committed certificate in its own set
        // (`verdict_db/neon_memory_certs/`) that the vendored `drat-trim`
        // replays. The walk credits an instruction under the Formal-only rule
        // (clause 2: the word-bound memory-effect decomposition of L04-P6,
        // held exactly; clause 3: the judged word decodes to the bound form),
        // and the gate demands every arrangement's authority
        // (`bound_memory_row_credit::neon_row_credit`).
        // MOVN and MOVK LEFT this table when the AArch64 form-polymorphic gate
        // mechanism landed (`aarch64_form_polymorphic_proofs`). Both already had
        // faithful per-FORM obligations bound per instruction by the function
        // verifier — one per architecturally legal (width, shift) pair, the W
        // MOVN forms pinning the 32-bit complement plus zero-extension — but no
        // single opcode-wide theorem, and crediting one form for all would be
        // the unfaithful inheritance #62 retracted. The gate now demands every
        // legal form's obligation instead of one opcode-wide query.
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
        // `Cmpxchg` opcode is emitted at BOTH i32 and i64 (the source-register
        // class picks the width; `select_cmpxchg` routes i8/i16 to the SEPARATE
        // `Cmpxchg8`/`Cmpxchg16` opcodes, which are credited by reconstruction and
        // must NEVER appear in this table — see
        // `narrow_cmpxchg_never_binds_the_wide_cmpxchg_proofs`). The gate has only
        // the opcode, so it requires the THREE CORE conditional-data-flow obligations
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
    use ProofCategory::Arithmetic as AR;
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
        // The flag-setting checked-i128 high limbs share one opcode across the
        // SIGNED (CSET VS) and UNSIGNED (CSET HS / CSET LO) chains. Both
        // overflow-bit obligations (the final NZCV rebuilt from limb
        // arithmetic vs the native 128-bit overflow definition; the chain's
        // VALUE is the iadd/isub whole-chain proofs' half) must discharge
        // before the opcode earns coverage — one chain's proof says nothing
        // about the other's condition read.
        AArch64Opcode::Adcs => {
            const PS: &[WidthProof] = &[
                p(AR, "checkedsadd_i128 overflow bit", 64),
                p(AR, "checkeduadd_i128 overflow bit", 64),
            ];
            Some(PS)
        }
        AArch64Opcode::Sbcs => {
            const PS: &[WidthProof] = &[
                p(AR, "checkedssub_i128 overflow bit", 64),
                p(AR, "checkedusub_i128 overflow bit", 64),
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
        // Standalone ROR-immediate (the rotate recognizer's unfused form) is
        // emitted at BOTH register widths under one opcode; both widths'
        // rotate obligations must discharge. Bound to `all_ror_immediate_proofs`
        // (SOURCE = frontend rotate blend, MACHINE = ROR shifted operand,
        // structurally distinct / provably equal; wrong-amount / ROR-vs-LSR /
        // rotate-direction controls refute). The function verifier additionally
        // binds each concrete instruction per destination width and rejects
        // out-of-range amounts.
        AArch64Opcode::RorRI => {
            const PS: &[WidthProof] = &[p(BWS, "rorri_i32", 32), p(BWS, "rorri_i64", 64)];
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
        // FCSEL's finite MODEL inventory retains both S/D templates from
        // `all_fcsel_proofs`: SOURCE = ite(trust_ir icmp, a, b), MACHINE =
        // ite(eval_condition(cc, encode_cmp(sel,0)), a, b), over raw FPR bits.
        // These queries select one representative condition per width, NOT all
        // twelve templates, much less every emitted condition/flag producer.
        // Model discharge does not bind actual source/FCSEL operands or reaching
        // NZCV. FunctionVerifier intentionally has no runtime opcode query until
        // that correspondence is implemented; this row grants no such authority.
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
        AArch64Opcode::NeonUaddlpV => {
            // Both widening stages are emitted in one fold. Requiring only the
            // historical `.16B->.8H` representative would let the subsequent
            // `.8H->.4S` instruction ship without its exact arrangement proof.
            const PS: &[WidthProof] = &[
                p(NL, "uaddlpv.16b->.8h lanewise-intent", 8),
                p(NL, "uaddlpv.8h->.4s lanewise-intent", 16),
            ];
            Some(PS)
        }
        AArch64Opcode::NeonSaddlpV => {
            // Signed widening reductions use the identical two-stage shape and
            // need the same arrangement-complete binding.
            const PS: &[WidthProof] = &[
                p(NL, "saddlpv.16b->.8h lanewise-intent", 8),
                p(NL, "saddlpv.8h->.4s lanewise-intent", 16),
            ];
            Some(PS)
        }
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

/// One required proof for a FORM-polymorphic AArch64 opcode: an opcode whose
/// emitted instances differ by an architectural (width, shift) pair that the
/// opcode alone does not name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FormProof {
    /// Category the proof is registered under.
    pub category: ProofCategory,
    /// Lower-case name substring (the AArch64 verifier matches
    /// case-insensitively), identical to the query the function verifier
    /// binds for a concrete instruction of this form.
    pub query: &'static str,
    /// Destination register width in bits (32 = W form, 64 = X form).
    pub width_bits: u32,
    /// Halfword shift (`LSL #shift`) this form encodes.
    pub shift: u32,
}

/// Every architecturally legal move-wide (width, halfword shift) pair: the X
/// form admits `LSL #0/#16/#32/#48`, the W form only `#0/#16` (Arm ARM MOVK /
/// MOVN: `hw<1>` must be 0 when `sf == 0`). The form-polymorphic gate demands
/// exactly one discharged proof per pair.
pub const AARCH64_MOVE_WIDE_LEGAL_FORMS: &[(u32, u32)] =
    &[(64, 0), (64, 16), (64, 32), (64, 48), (32, 0), (32, 16)];

/// Form-polymorphic AArch64 opcodes whose opcode-wide coverage demands one
/// discharged proof for EVERY legal (width, shift) form. Returns `None` for
/// every other opcode.
///
/// SOUNDNESS: MOVK and MOVN carry a halfword shift and a register width that
/// change their value semantics (MOVK splices a different halfword; MOVN
/// forces a different field to ones and, in the W form, complements 32 bits
/// and zero-extends). One slot's theorem credited to the whole opcode would be
/// the unfaithful inheritance #62 retracted. The coverage gate sees only the
/// opcode, so it requires a proof for EACH legal form and fails closed if this
/// table names any form set other than [`AARCH64_MOVE_WIDE_LEGAL_FORMS`]. Each
/// query is the exact per-form query `function_verifier` binds for a concrete
/// instruction (`const_materialize_proofs::{movk,movn}_halfword_query`), so the
/// gate credits precisely the obligations the per-instruction walk discharges;
/// `coverage_gate_tests` pins that equality and the refusal of the illegal
/// W-form `#32`/`#48` shifts. The per-form obligations are evaluator-backed
/// evidence by default, not formal proofs.
pub fn aarch64_form_polymorphic_proofs(opcode: AArch64Opcode) -> Option<&'static [FormProof]> {
    use ProofCategory::ConstantMaterialization as CM;
    /// Compact constructor for a `FormProof` table entry.
    const fn f(query: &'static str, width_bits: u32, shift: u32) -> FormProof {
        FormProof {
            category: CM,
            query,
            width_bits,
            shift,
        }
    }
    match opcode {
        // MOVK: `ConstMat: MOVK {Xd,Wd} #imm16, LSL #hw splices halfword
        // (preserves other bits)` — an independent concat/extract splice
        // against the encoder's shift/mask semantics, one per form.
        AArch64Opcode::Movk => {
            const PS: &[FormProof] = &[
                f("movk xd #imm16, lsl #0 splices halfword", 64, 0),
                f("movk xd #imm16, lsl #16 splices halfword", 64, 16),
                f("movk xd #imm16, lsl #32 splices halfword", 64, 32),
                f("movk xd #imm16, lsl #48 splices halfword", 64, 48),
                f("movk wd #imm16, lsl #0 splices halfword", 32, 0),
                f("movk wd #imm16, lsl #16 splices halfword", 32, 16),
            ];
            Some(PS)
        }
        // MOVN: `ConstMat: MOVN {Xd,Wd} #imm16, LSL #hw inverts halfword field`
        // — an independent concat/XOR inverted-field specification against the
        // encoder's zext/shift/NOT semantics; the W forms pin the 32-bit
        // complement followed by zero-extension (upper 32 bits zero).
        AArch64Opcode::Movn => {
            const PS: &[FormProof] = &[
                f("movn xd #imm16, lsl #0 inverts halfword", 64, 0),
                f("movn xd #imm16, lsl #16 inverts halfword", 64, 16),
                f("movn xd #imm16, lsl #32 inverts halfword", 64, 32),
                f("movn xd #imm16, lsl #48 inverts halfword", 64, 48),
                f("movn wd #imm16, lsl #0 inverts halfword", 32, 0),
                f("movn wd #imm16, lsl #16 inverts halfword", 32, 16),
            ];
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
        Adcs,
        Sbcs,
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
        FrintnRR,
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
        // Baseline (non-LSE) LL/SC exclusives, CLREX and the opaque LL/SC
        // pseudos that the post-RA expansion turns into retry loops.
        Ldxr,
        Ldxrb,
        Ldxrh,
        Ldaxrb,
        Ldaxrh,
        Stxr,
        Stxrb,
        Stxrh,
        Stlxrb,
        Stlxrh,
        Clrex,
        LlscRmw8,
        LlscRmw16,
        LlscRmw32,
        LlscRmw64,
        LlscCmpSwap8,
        LlscCmpSwap16,
        LlscCmpSwap32,
        LlscCmpSwap64,
        // 128-bit pair exclusives and the 128-bit LL/SC pseudos.
        Ldxp,
        Ldaxp,
        Stxp,
        Stlxp,
        LlscLoad128,
        LlscStore128,
        LlscRmw128,
        LlscCmpSwap128,
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
        // vectorizers' LOAD-PATH rework); EmittableNeedsProof with explicit
        // DeferredUnfaithfulModel debt, not an allowlisted or runtime credit.
        NeonLdpQPost,
        // STP Q-pair post-index store (emitted by the NEON map/stencil/fmap
        // vectorizers' STORE-PATH pairing rework); likewise EmittableNeedsProof
        // with explicit DeferredUnfaithfulModel debt and no runtime credit.
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
        // ELF TLSDESC: the pre-expansion call form (FailClosedAllowlisted) and
        // the three emitted relocation slots (EmittableNeedsProof, RED).
        TlsDescCall,
        LdrTlsdesc,
        AddTlsdescLo12,
        BlrTlsdesc,
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
        // FEAT_CRC32 checksum steps (per-function `crc` admission).
        Crc32B,
        Crc32H,
        Crc32W,
        Crc32X,
        Crc32Cb,
        Crc32Ch,
        Crc32Cw,
        Crc32Cx,
    ]
};

/// Whether `opcode` is one of the sixteen x86 VOLATILE memory accesses.
#[must_use]
pub fn x86_opcode_is_volatile_memory(opcode: X86Opcode) -> bool {
    crate::x86_volatile_trace::volatile_access_of_opcode(opcode).is_some()
}

/// The legs of the x86 memory-row conjunctions, as a RED row's
/// `ProofNotDischarged::proof_name` names them.
const X86_ADDRESS_LEG: &str = "ADDR-x86";
const X86_VALUE_LEG: &str = "VALUE-x86";
const X86_VOLATILE_TRACE_LEG: &str = "VOL-x86-trace";

/// Why the VALUE leg failed, for a row that requires it.
fn x86_value_leg_failure(opcode: X86Opcode) -> String {
    format!(
        "the reconstruction of a representative {opcode:?} instance did not discharge Valid \
         (x86_64_function_verifier::reconstruction_discharges_valid)"
    )
}

/// The RED row of an x86 memory-row conjunction whose `failed` legs (name,
/// reason) did not discharge. `prefix` names the conjunction for a volatile
/// row; the ADDRESS row passes `""`, so a plain row whose address alone fails
/// is `ADDR-x86 (<opcode>)` exactly as it has always been.
fn x86_conjunction_red_row(
    display: String,
    opcode: X86Opcode,
    prefix: &str,
    failed: &[(&str, String)],
    what: &str,
) -> OpcodeAuditRow {
    let legs = failed
        .iter()
        .map(|(leg, _)| *leg)
        .collect::<Vec<_>>()
        .join(" + ");
    OpcodeAuditRow {
        opcode_display: display,
        class: OpcodeClass::EmittableNeedsProof,
        finding: Some(CoverageFinding::ProofNotDischarged {
            proof_name: format!("{prefix}{legs} ({opcode:?})"),
            detail: failed
                .iter()
                .map(|(leg, why)| format!("{leg}: {why}"))
                .collect::<Vec<_>>()
                .join("; "),
        }),
        note: format!(
            "{opcode:?}: {what}; failed leg(s): {legs}. The row is RED, and no remaining leg \
             credits it on its own"
        ),
    }
}

/// The audit row for a volatile memory access: credited JOINTLY, or RED.
///
/// The row is covered only when all three legs hold: the ADDRESS credit
/// (`x86_addressing_proofs`, from the real emitted bytes), the VALUE leg
/// (`value_discharged`: the opcode's memory load/store reconstruction, the one
/// its byte-identical plain sibling uses, discharges `Valid`), and the
/// BOUNDARY credit (`x86_volatile_trace`). Otherwise it is RED as
/// `ProofNotDischarged` naming every failed leg — a leg that stopped
/// discharging is a regression, not acknowledged debt — and nothing else in
/// the gate credits it: [`x86_address_audit_row`] refuses a volatile opcode.
#[must_use]
pub fn x86_volatile_joint_audit_row(
    display: &str,
    opcode: X86Opcode,
    address: Result<crate::x86_addressing_proofs::MemMovAddressCredit, String>,
    value_discharged: bool,
    trace: Result<crate::x86_volatile_trace::VolatileTraceCredit, String>,
) -> OpcodeAuditRow {
    let (address, trace) = match (address, value_discharged, trace) {
        (Ok(address), true, Ok(trace)) => (address, trace),
        (address, value_discharged, trace) => {
            let mut failed: Vec<(&str, String)> = Vec::new();
            if let Err(why) = address {
                failed.push((X86_ADDRESS_LEG, why));
            }
            if !value_discharged {
                failed.push((X86_VALUE_LEG, x86_value_leg_failure(opcode)));
            }
            if let Err(why) = trace {
                failed.push((X86_VOLATILE_TRACE_LEG, why));
            }
            return x86_conjunction_red_row(
                display.to_string(),
                opcode,
                "VOL-x86 joint: ",
                &failed,
                "VOLATILE, credited only JOINTLY (ADDRESS + VALUE + BOUNDARY)",
            );
        }
    };

    OpcodeAuditRow {
        opcode_display: display.to_string(),
        class: OpcodeClass::EmittableNeedsProof,
        finding: None,
        note: format!(
            "VOLATILE, credited JOINTLY — no part of this stands alone. ADDRESS decoded from the \
             REAL emitted ModR/M+SIB bytes ({} captured encodings, {} intent and {} byte \
             controls); VALUE: the memory load/store reconstruction the byte-identical plain \
             sibling uses, from a representative {opcode:?} instance in its ISel register \
             class, evaluates Valid (default evaluator acceptance is regression evidence, NOT a \
             formal proof; its address half is the shared X == X, so it carries the value \
             facet only); BOUNDARY from x86_volatile_trace, whose {} hazard controls (elide, \
             duplicate, widen, narrow, redirect, reclass, reorder) refute INSIDE its credit hook \
             over {} recognised opcodes, while a benign block-layout permutation is accepted. \
             That boundary is ENFORCED per compile and fails closed at BOTH the selection \
             (VOL-2, LIR VolatileLoad/Store vs the selected opcode) and optimizer (VOL-1, \
             before vs after the passes) boundaries. A byte-identical plain MOV proof alone \
             would NOT credit this row, which is what its deferral reason said",
            address.entries,
            address.intent_controls_refuted,
            address.byte_controls_refuted,
            trace.hazards_refuted,
            trace.opcodes
        ),
    }
}

/// Whether `opcode` accesses memory through an addressing operand that
/// [`crate::x86_addressing_proofs`] proves.
///
/// These are exactly the opcodes whose ADDRESS facet the shared
/// `x86_reconstruct_effective_address` cannot carry — it builds both halves
/// from the same operand, so no address error refutes. `Lea`/`LeaSib` are
/// included (since f74b4561c): they perform no access, but they encode
/// through the same ModR/M+SIB machinery, so the address this lane decodes IS
/// their value. The sixteen volatile forms are included for their ADDRESS;
/// what makes them volatile is not this lane's obligation. The in-crate teeth
/// audit (`report_which_credited_opcodes_have_no_address_teeth`) fails if a
/// credited memory opcode without address teeth is missing from this list or
/// has no captured encoding in the lane's corpus.
#[must_use]
pub fn x86_opcode_has_address_credit(opcode: X86Opcode) -> bool {
    use X86Opcode as O;
    matches!(
        opcode,
        // integer MOV, every width, plain and SIB
        O::MovRM
            | O::MovRM32
            | O::MovRM16
            | O::MovRM8
            | O::MovMR
            | O::MovMR32
            | O::MovMR16
            | O::MovMR8
            | O::MovRMSib
            | O::MovRM32Sib
            | O::MovRM8Sib
            | O::MovMRSib
            | O::MovMR32Sib
            | O::MovMR8Sib
            // zero-extending loads: the ADDRESS and, through the same decode,
            // the DESTINATION-WRITE facet (`x86_addressing_proofs`)
            | O::MovzxRM8
            | O::MovzxRM16
            | O::MovzxRM8Sib
            // SSE scalar
            | O::MovssRM
            | O::MovsdRM
            | O::MovssMR
            | O::MovsdMR
            | O::MovssRMSib
            | O::MovsdRMSib
            // packed 128-bit
            | O::MovdqaRM
            | O::MovdquRM
            | O::MovdqaMR
            | O::MovdquMR
            | O::MovdquRMSib
            | O::MovdquMRSib
            // memory ALU
            | O::AddRM
            | O::SubRM
            | O::CmpRM
            | O::ImulRM
            | O::XorMR
            | O::AddMR
            | O::ImulRMSib
            | O::XorMRSib
            | O::AddMRSib
            // LEA computes an address rather than accessing memory, which
            // makes it the cleanest member of the family: the address IS the
            // value, so there is no access width or direction to get wrong and
            // the obligation reduces to exactly the question this lane answers.
            | O::Lea
            | O::LeaSib
            // The VOLATILE forms. Byte-identical to their plain siblings, so
            // their ADDRESS is the same question and this lane answers it the
            // same way. What makes them volatile — that the access is emitted
            // exactly once, at that width, in that order — is NOT this
            // obligation's business and is carried by `x86_volatile_trace`,
            // enforced per compile at both the selection (VOL-2) and optimizer
            // (VOL-1) boundaries. This lane is their ADDRESS leg only: the gate
            // credits them through `x86_volatile_joint_audit_row`, which also
            // requires the VALUE reconstruction and that trace credit, and
            // `x86_address_audit_row` refuses them. Pinned by
            // `coverage_gate_tests::x86_volatile_joint_row_withholds_credit_when_any_leg_fails`.
            | O::VolatileMovRM8
            | O::VolatileMovRM16
            | O::VolatileMovRM32
            | O::VolatileMovRM
            | O::VolatileMovMR8
            | O::VolatileMovMR16
            | O::VolatileMovMR32
            | O::VolatileMovMR
            | O::VolatileMovssRM
            | O::VolatileMovsdRM
            | O::VolatileMovssMR
            | O::VolatileMovsdMR
            | O::VolatileMovdquRM
            | O::VolatileMovdqaRM
            | O::VolatileMovdquMR
            | O::VolatileMovdqaMR
            | O::VolatileMovzxRM8
            | O::VolatileMovzxRM16
            // The COMPARE-EXCHANGE forms (`LOCK CMPXCHG r/m8, r8`,
            // `LOCK CMPXCHG r/m16, r16`, and the 128-bit atomic-load pseudo's
            // `LOCK CMPXCHG16B m128`). Their reconstructions build both
            // addresses from the emitted operand like every other row, so the
            // ADDRESS is this lane's; their VALUE stays the reconstruction's,
            // and `x86_compare_exchange_joint_audit_row` requires both.
            | O::Cmpxchg8
            | O::Cmpxchg16
            | O::AtomicLoadCmpxchg16b
    )
}

/// Whether `opcode` is one of the memory COMPARE-EXCHANGE rows credited
/// jointly by the address lane and their own value reconstruction.
#[must_use]
pub fn x86_opcode_is_compare_exchange_memory(opcode: X86Opcode) -> bool {
    matches!(
        opcode,
        X86Opcode::Cmpxchg8 | X86Opcode::Cmpxchg16 | X86Opcode::AtomicLoadCmpxchg16b
    )
}

/// The audit row for a memory COMPARE-EXCHANGE, credited JOINTLY: ADDRESS from
/// the byte-level lane, VALUE from the per-instruction reconstruction. RED as
/// `ProofNotDischarged` when either part fails — neither stands in for the
/// other.
#[must_use]
pub fn x86_compare_exchange_joint_audit_row(
    display: String,
    opcode: X86Opcode,
    address: Result<crate::x86_addressing_proofs::MemMovAddressCredit, String>,
    value_reconstruction_discharges: bool,
) -> OpcodeAuditRow {
    match (address, value_reconstruction_discharges) {
        (Ok(c), true) => OpcodeAuditRow {
            opcode_display: display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: None,
            note: format!(
                "COMPARE-EXCHANGE, credited JOINTLY. ADDRESS decoded from the REAL emitted \
                 bytes by the INDEPENDENT SDM decoder ({} captured encodings, {} intent and {} \
                 byte controls refuting inside the hook); VALUE from the per-instruction \
                 reconstruction of {opcode:?}, whose representative obligation evaluates Valid \
                 (default evaluator acceptance is regression evidence, NOT a formal proof). The \
                 reconstruction alone refutes no address error — both of its addresses derive \
                 from the emitted operand — and NOTHING here establishes that instruction \
                 selection chose the right address",
                c.entries, c.intent_controls_refuted, c.byte_controls_refuted
            ),
        },
        (address, value_ok) => {
            let detail = match (&address, value_ok) {
                (Err(reason), true) => format!("ADDRESS: {reason}"),
                (Ok(_), false) => "VALUE: the reconstruction did not discharge Valid".to_string(),
                (Err(reason), false) => {
                    format!("ADDRESS: {reason}; VALUE: the reconstruction did not discharge Valid")
                }
                (Ok(_), true) => unreachable!("handled above"),
            };
            OpcodeAuditRow {
                opcode_display: display,
                class: OpcodeClass::EmittableNeedsProof,
                finding: Some(CoverageFinding::ProofNotDischarged {
                    proof_name: format!("ADDR-x86 + reconstruction ({opcode:?})"),
                    detail: detail.clone(),
                }),
                note: format!(
                    "{opcode:?}: the joint address + value credit did not discharge ({detail}); \
                     the row is RED"
                ),
            }
        }
    }
}

/// The audit row for an opcode credited by the ADDRESS lane.
///
/// The row is a CONJUNCTION of two legs: the ADDRESS credit (`credit`, decoded
/// from the real emitted bytes) and the VALUE leg (`value_discharged`: the
/// opcode's reconstruction discharges `Valid`). The reconstruction's own
/// address half is `X == X` and proves nothing about the address, which is why
/// this lane exists; its value half is what the note credits the value facet
/// to, so it must actually hold. A failing leg makes the row RED as
/// `ProofNotDischarged` naming it — deliberately NOT a
/// `DeferredUnfaithfulModel`, because a lane that stopped refuting is a broken
/// proof, not acknowledged debt.
///
/// A VOLATILE opcode is refused even when both legs hold: those two legs are
/// the byte-identical plain MOV proof its deferral reason called insufficient,
/// and it is credited only by [`x86_volatile_joint_audit_row`].
#[must_use]
pub fn x86_address_audit_row(
    display: String,
    opcode: X86Opcode,
    credit: Result<crate::x86_addressing_proofs::MemMovAddressCredit, String>,
    value_discharged: bool,
) -> OpcodeAuditRow {
    if x86_opcode_is_volatile_memory(opcode) {
        return OpcodeAuditRow {
            opcode_display: display,
            class: OpcodeClass::EmittableNeedsProof,
            finding: Some(CoverageFinding::ProofNotDischarged {
                proof_name: format!("VOL-x86 joint: not attempted ({opcode:?})"),
                detail: "a volatile row is credited only by x86_volatile_joint_audit_row; the \
                         ADDRESS row's address and value legs are the byte-identical plain MOV \
                         proof its deferral reason rejected"
                    .to_string(),
            }),
            note: format!(
                "{opcode:?} is VOLATILE: the ADDRESS row does not credit it, whatever its legs \
                 say"
            ),
        };
    }
    let c = match (credit, value_discharged) {
        (Ok(c), true) => c,
        (credit, value_discharged) => {
            let mut failed: Vec<(&str, String)> = Vec::new();
            if let Err(why) = credit {
                failed.push((X86_ADDRESS_LEG, why));
            }
            if !value_discharged {
                failed.push((X86_VALUE_LEG, x86_value_leg_failure(opcode)));
            }
            return x86_conjunction_red_row(
                display,
                opcode,
                "",
                &failed,
                "credited only on its ADDRESS and its VALUE together",
            );
        }
    };
    OpcodeAuditRow {
        opcode_display: display,
        class: OpcodeClass::EmittableNeedsProof,
        finding: None,
        note: format!(
            "ADDRESS decoded from the REAL emitted bytes by an INDEPENDENT SDM decoder \
             ({} captured encodings, {} addressing modes, {} access widths) and compared \
             against the machine-IR intent as `base + (index << shift) + sext(disp)` vs \
             `base + index*scale + disp` — structurally distinct, with a source-equals-\
             machine pairing REFUSED. {} intent controls and {} byte controls refute INSIDE \
             the credit hook. VALUE: RECONSTRUCTED from real {opcode:?} operands — the \
             representative obligation evaluates Valid (default evaluator acceptance is \
             regression evidence, NOT a formal proof); its address half is the shared X == X, \
             so it carries the value facet only. Both legs are required. NOTHING here \
             establishes that instruction selection chose the right address",
            c.entries, c.modes, c.widths, c.intent_controls_refuted, c.byte_controls_refuted
        ),
    }
}

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
        MovzxRM8,
        MovzxRM16,
        MovzxRM8Sib,
        VolatileMovzxRM8,
        VolatileMovzxRM16,
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
        MovdquRMSib,
        MovdquMRSib,
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
        AtomicLoadCmpxchg16b,
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
        // Memory-destination RMW ALU (appended with the enum, kept last to
        // mirror discriminant order)
        XorMR,
        AddMR,
        XorMRSib,
        AddMRSib,
        // Variable-count rotate (appended with the enum)
        RolRCl,
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
        I32Clz,
        I64Clz,
        I32Ctz,
        I64Ctz,
        I32Rotl,
        I64Rotl,
        I32Rotr,
        I64Rotr,
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
        I32Eqz,
        I64Eqz,
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
        F32Copysign,
        F64Copysign,
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
        F32Const,
        F64Const,
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
        MemoryCopy,
        MemoryFill,
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
        Select,
        // Calls
        Call,
        CallIndirect,
        // SIMD / v128 (never selected by the lowerer)
        V128Load,
        V128Store,
        V128Const,
        I32x4Add,
        I32x4Mul,
        F32x4Add,
        F32x4Mul,
    ]
};
