// trust-cg-verify/function_verifier.rs - Function-level verification pipeline
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Provides verify_function(): given a MachFunction, walk every instruction,
// discharge the obligations built from that instruction (source-bound frame and
// arithmetic replay, operand reconstruction), and produce a
// FunctionVerificationReport with per-instruction results and coverage metrics.
//
// Reference: crates/trust-cg-verify/src/proof_database.rs

//! Function-level verification pipeline.
//!
//! [`verify_function`] inspects every instruction in a [`MachFunction`] and
//! credits it only with evidence about that instruction: a source-bound
//! obligation replayed formally, or an obligation reconstructed from the
//! emitted opcode and operands and discharged completely. A registry theorem
//! selected by name ([`FunctionVerifier::opcode_to_proof_query`]) is about a
//! representative form, so it is reported but never credited, and a sampled
//! discharge is reported but never credited. The report carries per-instruction
//! results and a coverage percentage.
//!
//! # Example
//!
//! ```rust,no_run
//! use trust_cg_ir::{MachFunction, Signature};
//! use trust_cg_verify::function_verifier::verify_function;
//!
//! let func = MachFunction::new("example".to_string(), Signature::new(vec![], vec![]));
//! let report = verify_function(&func);
//! println!("Coverage: {:.1}%", report.coverage_percent());
//! ```

use std::sync::Arc;
use trust_cg_ir::aarch64_regs::{SP, W16, W17, WSP, WZR, X16, X17, X29, XZR, preg_class};
use trust_cg_ir::cc::OperandSize;
use trust_cg_ir::{
    AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, PReg, SpecialReg, X86Opcode,
};

use crate::lowering_proof::{
    MachineSideProvenance, ProofObligation, VerificationConfig, memoized_verify_by_evaluation,
};
use crate::proof_database::{ProofCategory, ProofDatabase};
use crate::provenance_xcheck::{
    self, AARCH64_PROVENANCE_XCHECK_DEFAULT, LirSourceIndex, LirSourceInst, OpClass,
    ProvenanceXCheckMode,
};
use crate::smt::SmtExpr;
use crate::verify::{VerificationResult, VerificationStrength};

// ---------------------------------------------------------------------------
// InstructionVerificationResult
// ---------------------------------------------------------------------------

/// Result of verifying a single instruction within a function.
#[derive(Debug, Clone)]
pub enum InstructionVerificationResult {
    /// Instruction was verified against a proof obligation (the proof matched and
    /// DISCHARGED). This records the lowering-proof BINDING for the cert-chain /
    /// compile-provenance pipeline. Whether it counts toward the genuinely-proven
    /// TALLY depends on `degenerate` (STRICT proven-honesty, task #61).
    Verified {
        /// Name of the proof obligation that was matched.
        proof_name: String,
        /// Category of the proof.
        category: ProofCategory,
        /// Verification strength achieved.
        strength: VerificationStrength,
        /// STRICT (task #61): true iff the bound obligation is structurally
        /// DEGENERATE (`trust_ir_expr == aarch64_expr`, an X==X self-equality).
        /// A degenerate proof discharges trivially and proves NOTHING about the
        /// lowering — it is recorded as a binding but credited ZERO in every
        /// proven/covered/verified tally (`genuinely_verified_count`,
        /// `coverage_percent`, `all_verified`). Purely structural, no name ledger.
        degenerate: bool,
    },

    /// Instruction has no corresponding proof obligation in the database.
    Unverified {
        /// Reason verification was not possible.
        reason: String,
    },

    /// Instruction was skipped (pseudo-op with no hardware semantics).
    Skipped {
        /// Why the instruction was skipped.
        reason: String,
    },

    /// Instruction had a matching proof but verification failed.
    Failed {
        /// Name of the proof that failed.
        proof_name: String,
        /// Detail of the failure.
        detail: String,
    },
}

impl InstructionVerificationResult {
    /// Compact one-token rendering for the per-row provenance trace
    /// (`TCG_TRACE_PROVENANCE=rows`). Diagnostic only: never parsed by a gate.
    pub fn trace_label(&self) -> String {
        match self {
            Self::Verified {
                strength,
                degenerate,
                ..
            } => format!(
                "verified:{strength:?}{}",
                if *degenerate { ":degenerate" } else { "" }
            ),
            Self::Unverified { .. } => "unverified".to_string(),
            Self::Skipped { .. } => "skipped".to_string(),
            Self::Failed { .. } => "failed".to_string(),
        }
    }

    /// Returns true if the instruction was successfully verified (its bound proof
    /// discharged). NOTE: this includes degenerate-backed bindings; for the STRICT
    /// proven-honesty headline use [`Self::is_genuinely_verified`].
    pub fn is_verified(&self) -> bool {
        matches!(self, Self::Verified { .. })
    }

    /// STRICT proven-honesty (task #61): true iff the instruction was verified AND
    /// the bound obligation is NON-DEGENERATE (`trust_ir_expr != aarch64_expr`).
    /// A degenerate X==X binding discharges trivially and proves nothing, so it is
    /// NOT genuinely verified — it contributes ZERO to the proven/covered tally.
    pub fn is_genuinely_verified(&self) -> bool {
        matches!(
            self,
            Self::Verified {
                degenerate: false,
                ..
            }
        )
    }

    /// STRICT (task #61): true iff this is a `Verified` result whose bound
    /// obligation is structurally DEGENERATE (X==X) — a recorded binding that
    /// proves nothing and is excluded from every proven/covered tally.
    pub fn is_degenerate_verified(&self) -> bool {
        matches!(
            self,
            Self::Verified {
                degenerate: true,
                ..
            }
        )
    }

    /// Returns true if the instruction was skipped (pseudo-op).
    pub fn is_skipped(&self) -> bool {
        matches!(self, Self::Skipped { .. })
    }

    /// Returns true if no proof was available.
    pub fn is_unverified(&self) -> bool {
        matches!(self, Self::Unverified { .. })
    }

    /// Returns true if verification was attempted but failed.
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed { .. })
    }

    /// Map one discharged, instruction-specific obligation to a result.
    ///
    /// Every function verifier routes its instruction-built obligations through
    /// here, so there is one place that decides what a verdict is worth.
    /// Sampling is reported, never credited: a `Valid` verdict at
    /// [`VerificationStrength::Statistical`] says only that the sampled inputs
    /// found no counterexample, so the instruction stays `Unverified` and the
    /// reason carries the sample count. `Exhaustive` (complete for the
    /// represented input domain) and `Formal` evidence may credit.
    pub(crate) fn from_discharge(
        proof_name: &str,
        category: ProofCategory,
        verdict: VerificationResult,
        strength: VerificationStrength,
        degenerate: bool,
    ) -> Self {
        match verdict {
            VerificationResult::Valid => match strength {
                VerificationStrength::Statistical { sample_count } => Self::Unverified {
                    reason: format!(
                        "{STATISTICAL_EVIDENCE_IS_NOT_CREDIT}: `{proof_name}` found no \
                         counterexample in {sample_count} sampled inputs"
                    ),
                },
                strength @ (VerificationStrength::Exhaustive | VerificationStrength::Formal) => {
                    Self::Verified {
                        proof_name: proof_name.to_owned(),
                        category,
                        strength,
                        degenerate,
                    }
                }
            },
            VerificationResult::Invalid { counterexample } => Self::Failed {
                proof_name: proof_name.to_owned(),
                detail: counterexample,
            },
            VerificationResult::Unknown { reason } => Self::Failed {
                proof_name: proof_name.to_owned(),
                detail: format!("Unknown: {reason}"),
            },
        }
    }

    /// The result for an instruction whose only candidate evidence is a
    /// registry theorem selected by name.
    ///
    /// A query such as `"load"` or `"Iadd_I"` returns the first registered
    /// obligation whose name contains it. That theorem is about its own
    /// representative operands, width and form, not about this instruction, so
    /// it is never per-instruction credit on any ISA. Nothing is discharged:
    /// the reason names the query only so a reader can see which retired
    /// mapping the instruction reached.
    pub(crate) fn withdrawn_registry_credit(query: &str, category: ProofCategory) -> Self {
        Self::Unverified {
            reason: format!(
                "{REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT}: query `{query}` in {} selects a theorem \
                 by name, not an obligation built from this instruction",
                category.name()
            ),
        }
    }
}

/// The owner's Formal-only rule for AArch64 bound-memory rows (2026-09-29;
/// [`crate::bound_memory_authority`]), applied to a row whose in-process
/// checks have already run.
///
/// A refuted (`Failed`) or `Skipped` row is returned unchanged, and so is any
/// row that is not a pair or scalar memory opcode. Otherwise the row is
/// `Verified` at `Formal`, citing its form theorem, exactly when `refutation`
/// shows that the row's in-process refutation check ran and held, the bound
/// form is the form of the word that check judged, and a committed
/// certificate of that form theorem replays; in every other case it is
/// `Unverified` with its previous reason plus the bound-memory note. A call
/// site where no refutation check ran passes `None`, and a bound row there is
/// never credited
/// ([`crate::bound_memory_authority::BOUND_MEMORY_REFUTATION_NOT_RUN`]). A
/// row `Verified` by anything other than that certificate (a sampled or
/// exhaustive evaluation) is DOWNGRADED: no other evidence credits these rows.
///
/// Certificates are replayed only under the compiler's proof-promotion policy
/// ([`VerificationConfig::for_proof_promotion`], `SourceBoundReplay`): replay
/// costs an independent checker run per form per process (up to ~24 s for
/// the largest form, measured under load), which an evaluation-only census
/// walk does not pay. Under `EvaluationOnly` a bound row is never credited.
pub(crate) fn apply_bound_memory_rule(
    inst: &MachInst,
    checked: InstructionVerificationResult,
    refutation: Option<crate::bound_memory_authority::BoundMemoryRefutation>,
    config: &VerificationConfig,
    request: Option<&crate::function_request::FunctionVerificationRequest>,
) -> InstructionVerificationResult {
    use crate::bound_memory_authority::BoundMemoryCredit;
    if matches!(
        checked,
        InstructionVerificationResult::Failed { .. }
            | InstructionVerificationResult::Skipped { .. }
    ) {
        return checked;
    }
    let Some(credit) = crate::bound_memory_authority::bound_memory_credit_in(
        inst,
        refutation.as_ref(),
        config.replays_source_bound_obligations(),
        request,
    ) else {
        return checked;
    };
    if let BoundMemoryCredit::Certified { proof_name } = credit {
        return InstructionVerificationResult::Verified {
            proof_name,
            category: ProofCategory::Memory,
            strength: VerificationStrength::Formal,
            degenerate: false,
        };
    }
    let note = credit
        .uncredited_note()
        .expect("an uncertified bound-memory verdict carries a note");
    match checked {
        InstructionVerificationResult::Unverified { reason } => {
            InstructionVerificationResult::Unverified {
                reason: format!("{reason}; {note}"),
            }
        }
        InstructionVerificationResult::Verified {
            proof_name,
            strength,
            ..
        } => InstructionVerificationResult::Unverified {
            reason: format!(
                "{note}; `{proof_name}` held at {strength:?} strength, which is not a replayed \
                 certificate"
            ),
        },
        InstructionVerificationResult::Failed { .. }
        | InstructionVerificationResult::Skipped { .. } => unreachable!("returned above"),
    }
}

/// Reason prefix of an instruction whose only candidate evidence was a registry
/// theorem found by name (substring or representative credit, withdrawn on every
/// ISA).
pub const REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT: &str =
    "no operand-exact evidence: registry name lookup is not proof credit";

/// Reason prefix of an instruction whose obligation discharged only by sampling.
pub const STATISTICAL_EVIDENCE_IS_NOT_CREDIT: &str =
    "no complete evidence: statistical sampling is not proof credit";

/// Reason prefix of a single-instruction atomic whose word-bound
/// decomposition ([`crate::aarch64_atomic_effect`]) held in process but whose
/// atomic form theorem has no replayed certificate here: an in-process
/// decision is testing-grade evidence, never credit.
pub const ATOMIC_EFFECT_IS_NOT_CREDIT: &str = "no checked certificate: an in-process atomic value/memory-effect decision is not proof \
     credit";

/// Reason prefix of an instruction whose only evidence is its instruction-
/// derived obligation ([`crate::aarch64_instruction_word_proofs`]): the
/// obligation holds, but it binds the re-derived word to this instruction's
/// operands, not to a source instruction, and no independently checked
/// certificate discharges it.
pub const INSTRUCTION_DERIVED_IS_NOT_CREDIT: &str =
    "no checked certificate: an instruction-derived obligation is not proof credit";

/// Clause an UNCREDITED scalar or pair memory row carries after its previous
/// reason when the word-bound memory-effect decomposition of its word
/// ([`crate::aarch64_memory_effect`]) judged it
/// ([`FunctionVerifier::with_memory_effect`]): every part held (or one was
/// undecided) in process, and the clause then says how many parts have a
/// Clean-checked certificate of their exact query (every part, or `k of n`
/// and the first part without one).
///
/// The decomposition is a second refutation check and a diagnostic. It never
/// credits: the Formal-only bound-memory rule (owner ruling 2026-09-29,
/// [`crate::bound_memory_authority`]) names the only evidence that credits a
/// bound-memory row, a committed certificate of the row's FORM theorem that
/// the independent checker replays, and a Clean-checked certificate of a part
/// is not that evidence, and it is not admitted for an unbound row (OD-39 in
/// docs/decision-record.md). The clause
/// follows the previous reason, so every reason-prefix counter
/// (`sampled_uncredited_count`, `instruction_derived_count`) keeps its
/// meaning. A row a source-bound owner binds takes the source-bound route
/// instead (`FunctionVerifier::frame_record_row`,
/// `FunctionVerifier::leaf_access_row`), where Clean-checked parts DO credit
/// it, and only together with that binding.
pub const MEMORY_EFFECT_IS_NOT_CREDIT: &str =
    "word-bound memory effect (a refutation check; its certificates are recorded, never credit)";

/// The source-bound route's evidence for a memory row bound to a source-bound
/// owner ([`FunctionVerifier::frame_record_row`],
/// [`FunctionVerifier::leaf_access_row`]).
enum BoundMemoryEvidence {
    /// Every part has a Clean-checked certificate of its exact query.
    Credited,
    /// A part was refuted, in process or by the solver.
    Refuted { proof_name: String, detail: String },
    /// Not credit; the clause says how far the parts got.
    Uncredited(String),
}

/// The phrase a [`MEMORY_EFFECT_IS_NOT_CREDIT`] clause carries when every
/// part of the decomposition has a Clean-checked certificate.
pub const MEMORY_EFFECT_EVERY_PART_CHECKED: &str = "every part has a Clean-checked certificate";

/// Why a [`MEMORY_EFFECT_IS_NOT_CREDIT`] clause under a replaying policy
/// names no checked part: the live replay is a diagnostic
/// ([`crate::diag::memory_effect_replay_enabled`]), off by default because
/// its verdict is recorded, never credited.
pub const MEMORY_EFFECT_REPLAY_NOT_REQUESTED: &str =
    "live replay not requested: the diagnostic `memory-effect-replay` knob is off";

/// Clause an UNCREDITED NEON horizontal-reduction or permute row carries
/// after its previous reason when the word-bound lane-effect decomposition of
/// its word ([`crate::aarch64_neon_lane_effect`], ledger L04-P6) judged it
/// ([`FunctionVerifier::with_neon_lane_effect`]): every part held (or one was
/// undecided) in process. A refuted part fails the row instead. The parts are
/// never proof credit and have no live replay lane, so the clause records
/// that none has a Clean-checked certificate. It follows the previous reason,
/// so every reason-prefix counter keeps its meaning.
pub const NEON_LANE_EFFECT_IS_NOT_CREDIT: &str =
    "word-bound NEON lane effect (a refutation check, never credit)";

/// Tag of the opcode-inventory census lines
/// ([`EmittedOpcodeInventoryReport::census_lines`]), printed to stderr by the
/// codegen certificate builder when `TCG_TRACE_OPCODE_INVENTORY=1`.
pub const OPCODE_INVENTORY_TRACE_TAG: &str = "[TCG-OPCODE-INVENTORY]";

// ---------------------------------------------------------------------------
// InstructionOpcode: target-typed report opcode
// ---------------------------------------------------------------------------

/// Target-specific machine opcode captured in an instruction verification report.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstructionOpcode {
    /// AArch64 machine opcode.
    AArch64(AArch64Opcode),
    /// x86-64 machine opcode.
    X86_64(X86Opcode),
    /// RISC-V (RV64) machine opcode.
    RiscV(trust_cg_ir::RiscVOpcode),
}

impl std::fmt::Display for InstructionOpcode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AArch64(opcode) => write!(f, "AArch64::{opcode:?}"),
            Self::X86_64(opcode) => write!(f, "x86_64::{opcode:?}"),
            Self::RiscV(opcode) => write!(f, "riscv::{opcode:?}"),
        }
    }
}

// ---------------------------------------------------------------------------
// InstructionReport: per-instruction entry
// ---------------------------------------------------------------------------

/// Per-instruction verification entry in the report.
#[derive(Debug, Clone)]
pub struct InstructionReport {
    /// Index of the instruction in `MachFunction::insts`.
    pub inst_index: usize,
    /// The target-specific machine opcode.
    pub opcode: InstructionOpcode,
    /// Verification result for this instruction.
    pub result: InstructionVerificationResult,
}

/// Verification status used by the emitted-opcode inventory.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpcodeInventoryStatus {
    /// The emitted non-pseudo opcode has verified proof coverage.
    Verified,
    /// The instruction is pseudo/trap-only and has no hardware semantic proof obligation.
    Skipped,
    /// The emitted non-pseudo opcode is an indirect call/branch target (x86-64
    /// `CallR`/`CallM`, AArch64 `Blr`) that has NO per-instruction value-proof —
    /// the only candidate would be the `target == target` tautology. Its
    /// correctness is established by the SURROUNDING proofs (the target-address
    /// computation is verified instruction-by-instruction; the CALL/BLR control
    /// transfer is architecturally fixed), which is exactly why the formal
    /// `coverage_gate` allowlists this opcode family. Promotable: it would
    /// otherwise reject the universal `lang_start → FnOnce::call_once` entry path
    /// (whose indirect `CallR` calls `main`), turning `call_once` into a trapping
    /// `ud2` stub → SIGILL. This is NOT a blanket allowlist: opcodes the gate
    /// allowlists merely "pending a proof" (e.g. AArch64 `CSINV`/bitfield) are
    /// real gaps and keep status `Unverified` (non-promotable).
    CoveredElsewhere,
    /// The emitted non-pseudo opcode has no matching proof.
    Unverified,
    /// A proof was selected for the emitted opcode, but verification failed.
    Failed,
}

impl OpcodeInventoryStatus {
    /// Returns true when this inventory row is safe for proof-required promotion.
    ///
    /// `FailClosedAllowlisted` is promotable so the per-compile promotion gate
    /// agrees with the formal `coverage_gate` (which already allowlists the same
    /// opcodes). Without this the two gates disagree and any function containing
    /// an allowlisted opcode (e.g. the `FnOnce::call_once`/`lang_start` entry
    /// path's indirect `CallR`) is wrongly rejected — see the call_once trap-stub
    /// regression.
    pub fn is_promotable(self) -> bool {
        matches!(
            self,
            Self::Verified | Self::Skipped | Self::CoveredElsewhere
        )
    }
}

impl std::fmt::Display for OpcodeInventoryStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Verified => f.write_str("verified"),
            Self::Skipped => f.write_str("skipped"),
            Self::CoveredElsewhere => f.write_str("covered-elsewhere"),
            Self::Unverified => f.write_str("unverified"),
            Self::Failed => f.write_str("failed"),
        }
    }
}

/// One line per NZCV-consumer binding REFUSAL, when `TCG_TRACE_NZCV_BINDING=1`.
///
/// The refusals are the product of the source-condition binding, so they must be
/// readable: a first-failure count over them is the only way to size which
/// `CSet`/`Csel` blame is a missing theorem and which is a source disagreement.
/// Off by default and never a verdict input.
fn nzcv_binding_trace(inst: &MachInst, source: &LirSourceInst, cc: i64, why: &str) {
    if matches!(
        std::env::var("TCG_TRACE_NZCV_BINDING").as_deref(),
        Ok("1") | Ok("true") | Ok("on")
    ) {
        eprintln!(
            "[TCG-NZCV-BINDING-REFUSED] opcode={:?} cc={cc} source={} class={:?} why={why}",
            inst.opcode, source.opcode_debug, source.class
        );
    }
}

/// Exempted AArch64 opcodes that BOTH this list and the coverage gate name a
/// deferral: structurally covered by another family, but with an obligation
/// the gate's allowlist reason states as still pending. The reconciliation
/// test requires the two lists to agree in both directions.
pub const COVERED_ELSEWHERE_NAMED_DEFERRALS: &[AArch64Opcode] = &[AArch64Opcode::Ret];

/// True for opcodes whose correctness is established by the SURROUNDING/structural
/// proofs rather than by a per-instruction value-equivalence theorem (which, for
/// these forms, would only ever be the `X == X` tautology that #62 retracted).
///
/// This is a deliberately CLOSED, opcode-identity list — NOT the broad
/// `coverage_gate` FailClosedAllowlisted set. The FailClosedAllowlisted set also
/// catalogues genuine "PENDING A PROOF" gaps (e.g. AArch64 `CSINV`, bitfield ops,
/// the unmapped FP cmp/half-cvt forms) which are NOT covered elsewhere and MUST
/// keep blocking proof-promotion. Only the structural forms enumerated here are
/// safe to promote without their own value-proof:
///
///   * Indirect call/branch targets (CallR/CallM/Blr) — REQUIRED: every program
///     reaches `main` through `lang_start → FnOnce::call_once`, an indirect
///     `CallR`; rejecting it makes `call_once` a trapping `ud2` (SIGILL at start).
///     For the AArch64 jump-table `BR`, "elsewhere" is now per compile:
///     `aarch64_switch_binding` (run on every AArch64 encode) re-derives from
///     the final bytes that the BR register is the ADD of this dispatch's ADR
///     base and its LDRSW-loaded entry, that every table entry lands on its
///     recorded successor, and that the CMP/B.HI bounds check covers exactly
///     the table. `BLR`'s register target is the call lowering's obligation.
///     The coverage gate allowlists all three as "covered elsewhere".
///
///   * #62 covered-elsewhere structural forms (their ONLY mapped proof WAS a
///     degenerate X==X, now RETRACTED — but the form is genuinely covered by a
///     structural argument, NOT pending a missing value theorem):
///       - Register copies are NOT on this list (L04-P11). MovR, the typed
///         post-allocation copies MOVWrr/MOVXrr, FMOV FPR↔FPR and the
///         cross-class FMOV FPR↔GPR bitcasts bind per instruction to their
///         decoded-word form's registered obligation
///         (`aarch64_value_decode_proofs::a64_value_bound_form`), the same
///         obligations the coverage gate credits them by. An instance whose
///         operands name none of the forms (a copy to SP or from the zero
///         register, a half-precision or cross-width FMOV, malformed operands)
///         stays `Unverified` and blocks promotion. Until L04-P11 this predicate
///         promoted every copy instance, whatever its shape and whether or not
///         ENC-5 ran, and the gate kept MOVWrr/MOVXrr outside its denominator
///         as "never selected" although `pipeline::lower_copies` emits them.
///       - Return edge (RET): a NAMED DEFERRAL, listed in
///         [`COVERED_ELSEWHERE_NAMED_DEFERRALS`] and allowlisted by the coverage
///         gate "pending a faithful return-edge obligation": the transfer is
///         architecturally fixed and the CFG return edge is covered by the
///         Branch/CallLowering family, but no faithful return-edge obligation
///         exists yet. Every function that returns emits RET.
///       - Direct call / unconditional jump targets (Call/Jmp): the CFG edge +
///         PLT32/branch relocation cover the target (mirrors the indirect family).
///       - Constant materialization (x86 MOV r,imm): the emitted immediate IS the
///         trust_ir constant by construction of the lowerer; correctness is the
///         immediate/relocation encoding (covered-elsewhere structural), the same
///         class as AArch64 MovI/Adr/Adrp ("constant materialization — covered by
///         AddressMode/relocation proofs"). The retracted X==X was const==const.
///         For x86 the ENCODING half of that "elsewhere" is
///         `x86_encoding_proofs::mov_imm_check`, an independent SDM-derived
///         decode of the emitted MOV r,imm bytes, compared as a write to the
///         64-bit root register against the machine-IR intent. This predicate
///         does NOT run it. Per compile, the check runs inside
///         trust-cg-codegen's ENC-3 decode-check (`x86_64::decode_check`) on
///         every MovRI the x86 pipeline records for it. In ENC-3's default
///         `enforce` mode a refutation fails that function's x86 pipeline run
///         (`X86PipelineError::DecodeCheck`). Under `TCG_DECODE_CHECK=off|warn`
///         or `TCG_NO_DECODE_CHECK=1` the check does not gate the compile, so
///         the certificate trust-cg-codegen builds from this predicate
///         (`compiler::unverified_instruction_certificate`) is issued
///         `verified: true` only when the compile's ENC-3 backing is enforced;
///         otherwise it is a `verified: false` `covered_elsewhere_withheld` row
///         that names the check and blocks promotion (X-OPCODES-P13; until
///         2026-10-12 it was positive whether or not the check ran). AArch64
///         `AlignNop` ([`is_covered_elsewhere_emission_padding`]) cites ENC-5
///         the same way. Either way the check covers the ENCODING only, not the
///         lowerer's choice of constant.
pub fn is_covered_elsewhere_indirect_branch(opcode: InstructionOpcode) -> bool {
    use AArch64Opcode as A;
    use X86Opcode as X;
    matches!(
        opcode,
        InstructionOpcode::X86_64(
            X::CallR | X::CallM | X::Call | X::Jmp | X::JmpR | X::Ret | X::MovRI,
        ) | InstructionOpcode::AArch64(
            A::Blr
                    | A::BLR
                    | A::Br
                    | A::Ret
                    // Fused compare-and-branch (CBZ/CBNZ branch iff reg ==/!= 0;
                    // TBZ/TBNZ on a single bit test) to a WITHIN-FUNCTION CFG
                    // target. The control transfer is architecturally FIXED by the
                    // opcode (its per-instruction value theorem is the degenerate
                    // `reg==0 == reg==0` / bit==0 identity — the retracted X==X
                    // class), and the target block is covered by the block-layout /
                    // branch family exactly as for BCond (whose FLAGS-based condbr
                    // proof is the non-degenerate sibling) and Br/Blr above.
                    // coverage_gate documents these as "compare-and-branch target —
                    // covered by Branch proofs (CFG edge, NOT value)" — a
                    // structural coverage, NOT a pending-a-proof gap. The fusion's
                    // correctness (CMP+Bcc -> CBZ/TBZ picked the right condition) is
                    // the cmp-branch-fusion PASS's obligation, not a per-instruction
                    // value theorem. NARROW: only the fused zero/bit-test branches.
                    | A::Cbz
                    | A::Cbnz
                    | A::Tbz
                    | A::Tbnz
        )
    )
}

/// Why an integer ALU instruction of a malformed shape is refused, before any
/// verifier arm can bind it. `None` for every other instruction.
///
/// * ADD/SUB/AND/ORR/EOR (shifted register, shift 0) and ADDS/SUBS with an
///   operand after their three registers, and NEG with one after its two:
///   the encoder encodes only the registers and ignores the extra (shift)
///   operand, and ENC-5 does not decode the shape, so it would be neither
///   encoded nor checked.
/// * ADD/SUB/AND/ORR/EOR/LSL/LSR/ASR immediate whose third operand is a
///   register: the obligation would be rebuilt as the register form while the
///   word encodes an immediate (the encoder refuses such a shape).
///
/// No emission site produces either.
pub fn register_alu_extra_operand_refusal_reason(inst: &MachInst) -> Option<String> {
    use AArch64Opcode as O;
    let registers = match inst.opcode {
        O::AddRR | O::SubRR | O::AndRR | O::OrrRR | O::EorRR | O::AddsRR | O::SubsRR => 3,
        O::Neg => 2,
        _ => usize::MAX,
    };
    if inst.operands.len() > registers {
        return Some(format!(
            "{:?} with {} operands is not credited: the encoder encodes only its {registers} \
             registers and ENC-5 does not decode this shape",
            inst.opcode,
            inst.operands.len()
        ));
    }
    let immediate_form = matches!(
        inst.opcode,
        O::AddRI | O::SubRI | O::AndRI | O::OrrRI | O::EorRI | O::LslRI | O::LsrRI | O::AsrRI
    );
    // Frame placeholders (incoming-argument, stack-slot, frame-index operands)
    // are resolved to immediates by frame lowering and keep their own handling.
    match inst.operands.get(2) {
        Some(operand @ (MachOperand::PReg(_) | MachOperand::VReg(_) | MachOperand::Special(_)))
            if immediate_form =>
        {
            Some(format!(
                "{:?} with a register third operand ({operand:?}) is not credited: the \
             immediate form cannot encode it",
                inst.opcode
            ))
        }
        _ => None,
    }
}

/// Why a TLSLE TPREL add (`AddTprelHi12`/`AddTprelLo12`) is refused: no
/// registered obligation binds the instruction, its operands, its word or its
/// relocation site. `None` for every other opcode.
pub fn tprel_add_refusal_reason(opcode: AArch64Opcode) -> Option<String> {
    matches!(
        opcode,
        AArch64Opcode::AddTprelHi12 | AArch64Opcode::AddTprelLo12
    )
    .then(|| {
        format!(
            "{opcode:?} is not credited: the TLSLE relocation-arithmetic identity names no \
             register, word or relocation site, and ENC-5 does not check its word (deferred in \
             the coverage gate)"
        )
    })
}

/// Emission-time padding with no value, memory, or control-flow semantics.
///
/// `AlignNop` is a real four-byte arena instruction so every offset derivation
/// counts it, but it encodes the architectural NOP `0xD503201F`. Its meaningful
/// obligations are enforced elsewhere: the AArch64 decode check pins the exact
/// word and the independent EH/encoder offset cross-check pins stream layout.
/// A per-instruction value obligation would only be the vacuous `nop == nop`
/// form retracted from proof authority. The decode check is ENC-5, which a
/// compatibility-policy compile can run in warn mode or switch off
/// (`TCG_DECODE_CHECK_A64`, `TCG_NO_DECODE_CHECK`), so trust-cg-codegen issues
/// the positive certificate only when the encoding pipeline's ENC-5 is
/// enforced and a `covered_elsewhere_withheld` row otherwise (X-OPCODES-P13).
///
/// Keep this exact and separate from the broader coverage-gate allowlist: only
/// emission padding earns this structural credit.
pub fn is_covered_elsewhere_emission_padding(opcode: InstructionOpcode) -> bool {
    matches!(opcode, InstructionOpcode::AArch64(AArch64Opcode::AlignNop))
}

/// The emitted-opcode inventory status of one row, and its detail text. The
/// one rule the inventory and the trap-guard row merge
/// (`aarch64_trap_guard::combine`) both read.
fn inventory_status(
    opcode: InstructionOpcode,
    result: &InstructionVerificationResult,
) -> (OpcodeInventoryStatus, String) {
    match result {
        InstructionVerificationResult::Verified { proof_name, .. } => {
            (OpcodeInventoryStatus::Verified, proof_name.clone())
        }
        InstructionVerificationResult::Skipped { reason } => {
            (OpcodeInventoryStatus::Skipped, reason.clone())
        }
        InstructionVerificationResult::Unverified { reason } => {
            // Indirect call/branch targets are covered by the surrounding
            // proofs, not a per-instruction tautology, so they are promotable
            // (see `CoveredElsewhere`). This is a CLOSED, opcode-identity list
            // — NOT the broad `coverage_gate` FailClosedAllowlisted set, which
            // also tags genuine "pending a proof" gaps (CSINV/bitfield) that
            // MUST keep blocking promotion. A CBNZ/CBZ the trap-guard
            // obligation refused (the skip branch of a guard window) carries
            // that verdict, not the opcode's structural exemption (L04-P12).
            if (is_covered_elsewhere_indirect_branch(opcode)
                || is_covered_elsewhere_emission_padding(opcode))
                && !reason.starts_with(crate::aarch64_trap_guard::TRAP_GUARD_TAG)
            {
                (OpcodeInventoryStatus::CoveredElsewhere, reason.clone())
            } else {
                (OpcodeInventoryStatus::Unverified, reason.clone())
            }
        }
        InstructionVerificationResult::Failed { detail, .. } => {
            (OpcodeInventoryStatus::Failed, detail.clone())
        }
    }
}

/// One emitted opcode row in the proof inventory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpcodeInventoryEntry {
    /// Index of the instruction in the verifier's deterministic walk.
    pub inst_index: usize,
    /// Target-specific machine opcode.
    pub opcode: InstructionOpcode,
    /// Proof coverage status for this emitted opcode.
    pub status: OpcodeInventoryStatus,
    /// Human-readable verifier detail for uncovered rows.
    pub detail: String,
}

/// Target-aware inventory of emitted opcodes and their proof coverage.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EmittedOpcodeInventoryReport {
    /// Function name covered by this inventory.
    pub function_name: String,
    /// A function-level precondition failure blocks promotion independently
    /// of emitted instruction coverage, including for an empty function.
    pub precondition_failure: Option<FunctionVerificationPreconditionFailure>,
    /// All emitted opcode rows, including skipped pseudo/trap instructions.
    pub entries: Vec<OpcodeInventoryEntry>,
}

impl EmittedOpcodeInventoryReport {
    /// Returns rows that block proof-required promotion.
    pub fn uncovered_non_pseudo_opcodes(&self) -> Vec<&OpcodeInventoryEntry> {
        self.entries
            .iter()
            .filter(|entry| !entry.status.is_promotable())
            .collect()
    }

    /// Returns true when every emitted non-pseudo opcode has verified proof coverage.
    pub fn is_promotable(&self) -> bool {
        self.precondition_failure.is_none() && self.uncovered_non_pseudo_opcodes().is_empty()
    }

    /// The census lines for this function (format [`OPCODE_INVENTORY_TRACE_TAG`]
    /// `v1`): one `summary` line, then one `row` line per row that blocks
    /// promotion, or one `precondition` line when a function prerequisite
    /// failed. [`Self::promotion_rejection_reason`] details only the first
    /// blocking row; these lines give every row's reason, so a census can
    /// classify the whole wall. Fields are tab-separated `key=value` pairs and
    /// `detail` is last, with tabs, carriage returns and newlines replaced by
    /// spaces. Diagnostic text only: nothing reads it back as a verdict.
    pub fn census_lines(&self) -> Vec<String> {
        fn clean(text: &str) -> String {
            text.replace(['\t', '\r', '\n'], " ")
        }
        let function = clean(&self.function_name);
        let blocking = self.uncovered_non_pseudo_opcodes();
        let mut lines = vec![format!(
            "{OPCODE_INVENTORY_TRACE_TAG} v1\tsummary\tfunction={function}\trows={}\tblocking={}\tpromotable={}",
            self.entries.len(),
            blocking.len(),
            self.is_promotable()
        )];
        if let Some(failure) = &self.precondition_failure {
            lines.push(format!(
                "{OPCODE_INVENTORY_TRACE_TAG} v1\tprecondition\tfunction={function}\tdetail={}",
                clean(&failure.to_string())
            ));
        }
        lines.extend(blocking.into_iter().map(|entry| {
            format!(
                "{OPCODE_INVENTORY_TRACE_TAG} v1\trow\tfunction={function}\tindex={}\topcode={}\tstatus={}\tdetail={}",
                entry.inst_index,
                entry.opcode,
                entry.status,
                clean(&entry.detail)
            )
        }));
        lines
    }

    /// Builds a concise fail-closed rejection reason for proof promotion.
    ///
    /// Enumerates every DISTINCT uncovered opcode (not just the first) so a
    /// fail-closed compile error names the full coverage gap in one shot —
    /// essential now that the rustc bridge requests proof certificates
    /// per-compile and surfaces this reason as the compile error.
    pub fn promotion_rejection_reason(&self) -> Option<String> {
        if let Some(failure) = &self.precondition_failure {
            return Some(format!(
                "function verification precondition failed for `{}`: {failure}",
                self.function_name
            ));
        }
        let uncovered = self.uncovered_non_pseudo_opcodes();
        let first = uncovered.first()?;
        let mut distinct: Vec<String> = Vec::new();
        for entry in &uncovered {
            let name = format!("{}", entry.opcode);
            if !distinct.contains(&name) {
                distinct.push(name);
            }
        }
        Some(format!(
            "emitted opcode inventory found {} uncovered non-pseudo opcode(s) \
             across {} distinct opcode(s) [{}]; first in {}[{}] is {} ({})",
            uncovered.len(),
            distinct.len(),
            distinct.join(", "),
            self.function_name,
            first.inst_index,
            first.opcode,
            first.detail
        ))
    }
}

// ---------------------------------------------------------------------------
// FunctionVerificationReport
// ---------------------------------------------------------------------------

/// A function-level prerequisite that failed before instruction verification.
///
/// These failures are not fabricated machine instructions and do not affect
/// per-instruction counts. Every function/certificate promotion predicate must
/// reject them, even when no instructions were examined.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FunctionVerificationPreconditionFailure {
    /// Request policy must describe the verifier configuration actually used.
    VerificationRequestConfigMismatch,
    /// Enforced source checking was requested without a LIR source.
    MissingLirSource,
    /// The supplied LIR source belongs to a differently named function.
    LirSourceNameMismatch { source_function: String },
    /// A block refers to an instruction absent from the machine function.
    InvalidInstructionReference { block: usize, instruction: u32 },
    /// Enforced source checking admitted the exact LIR source and recognized
    /// the machine's source-bound frame/control skeleton, and the machine
    /// then disagrees with that source or its own layout. This is an
    /// erroneous supported target, never missing proof coverage.
    SourceBoundFrameMismatch(crate::source_bound_frame::FrameBindingMismatch),
    /// A complete storage-free linear body's source/return routing disagrees.
    SourceBoundFramelessMismatch(crate::source_bound_frame::FrameBindingMismatch),
    /// Enforced source checking admitted the exact LIR source for the x86-64
    /// source-bound body owner (under the supplied System V convention) and
    /// recognized the pre-RA machine body, which then computes a different
    /// value, reads undefined state, writes a preserved register or breaks its
    /// own control skeleton. An erroneous supported target, never missing
    /// proof coverage.
    SourceBoundX86BodyMismatch(crate::x86_source_bound_body::X86BodyMismatch),
    /// Enforced source checking admitted the exact LIR source for the AArch64
    /// whole-body owner and recognized the frameless machine body, which then
    /// returns a different value on a concrete input, writes a preserved
    /// register, breaks its own control skeleton or differs in signature. An
    /// erroneous supported target, never missing proof coverage.
    SourceBoundA64BodyMismatch(crate::source_bound_a64_body::A64BodyMismatch),
    /// The AArch64 trap accounting ([`crate::aarch64_trap_guard::account`])
    /// found a trap no instruction row can carry: a recorded guard window
    /// that is in no block (a missing trap), or, with the replayed LIR, a
    /// source guard, `Assert` or `Trap` that no executing trap row that
    /// implements it accounts for (refused: removed under evidence this
    /// verifier does not check, dropped, moved out of the executed code, or
    /// carried only by a row that does not implement it). The instruction
    /// rows are still reported.
    TrapGuardAccounting(crate::aarch64_trap_guard::TrapGuardAccountingFailure),
}

impl std::fmt::Display for FunctionVerificationPreconditionFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::VerificationRequestConfigMismatch => f.write_str("function verification request configuration does not match this verifier"),
            Self::MissingLirSource => {
                f.write_str("enforced provenance cross-check requires the exact LIR source; no source was supplied")
            }
            Self::LirSourceNameMismatch { source_function } => write!(
                f,
                "enforced provenance cross-check requires the exact LIR source; source name mismatch: got `{source_function}`"
            ),
            Self::InvalidInstructionReference { block, instruction } => write!(
                f,
                "invalid instruction reference {instruction} in machine block {block}"
            ),
            Self::SourceBoundFramelessMismatch(mismatch) => write!(
                f, "source-bound frameless body disagrees with its LIR source: {mismatch}"
            ),
            Self::SourceBoundFrameMismatch(mismatch) => write!(
                f,
                "[TCG-SOURCE-BOUND-FRAME-MISMATCH] erroneous supported target rejected: {mismatch}"
            ),
            Self::SourceBoundX86BodyMismatch(mismatch) => write!(
                f,
                "[TCG-SOURCE-BOUND-X86-MISMATCH] erroneous supported target rejected: {mismatch}"
            ),
            Self::SourceBoundA64BodyMismatch(mismatch) => write!(
                f,
                "[TCG-SOURCE-BOUND-A64-BODY-MISMATCH] erroneous supported target rejected: {mismatch}"
            ),
            Self::TrapGuardAccounting(failure) => write!(f, "{failure}"),
        }
    }
}

/// Report from verifying all instructions in a MachFunction.
#[derive(Debug, Clone)]
pub struct FunctionVerificationReport {
    /// Function name.
    pub function_name: String,
    /// Failed function-level prerequisite, if any. Such a report cannot
    /// authorize verification or promotion, regardless of instruction counts.
    pub precondition_failure: Option<FunctionVerificationPreconditionFailure>,
    /// Per-instruction results.
    pub instructions: Vec<InstructionReport>,
}

impl FunctionVerificationReport {
    /// Whether a function prerequisite or an instruction proof failed.
    pub fn has_failures(&self) -> bool {
        self.precondition_failure.is_some() || self.failed_count() != 0
    }

    /// Total number of instructions examined.
    pub fn total(&self) -> usize {
        self.instructions.len()
    }

    /// Number of instructions with a discharged proof BINDING (includes
    /// degenerate X==X bindings). This is the cert-chain / compile-provenance
    /// count, NOT the proven headline. For STRICT proven-honesty (task #61) use
    /// [`Self::genuinely_verified_count`], which excludes degenerate bindings.
    pub fn verified_count(&self) -> usize {
        self.instructions
            .iter()
            .filter(|r| r.result.is_verified())
            .count()
    }

    /// STRICT proven-honesty (task #61): number of instructions GENUINELY
    /// verified — a discharged proof binding whose obligation is NON-DEGENERATE
    /// (`trust_ir_expr != aarch64_expr`). Degenerate X==X bindings prove nothing
    /// and are excluded. This is the honest proven count.
    pub fn genuinely_verified_count(&self) -> usize {
        self.instructions
            .iter()
            .filter(|r| r.result.is_genuinely_verified())
            .count()
    }

    /// STRICT (task #61): number of instructions whose binding is a structurally
    /// DEGENERATE (X==X) proof. Reported SEPARATELY; not genuine evidence.
    /// `verified_count() == genuinely_verified_count() + degenerate_verified_count()`.
    pub fn degenerate_verified_count(&self) -> usize {
        self.instructions
            .iter()
            .filter(|r| r.result.is_degenerate_verified())
            .count()
    }

    /// Number of `Unverified` instructions whose instruction-built obligation
    /// discharged only by sampling ([`STATISTICAL_EVIDENCE_IS_NOT_CREDIT`]).
    /// Sampling is reported here, never credited.
    pub fn sampled_uncredited_count(&self) -> usize {
        self.unverified_with_reason_prefix(STATISTICAL_EVIDENCE_IS_NOT_CREDIT)
    }

    /// Number of `Unverified` instructions whose only candidate evidence was a
    /// registry theorem selected by name ([`REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT`]):
    /// the withdrawn substring and representative credit.
    pub fn registry_name_lookup_count(&self) -> usize {
        self.unverified_with_reason_prefix(REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT)
    }

    /// Number of `Unverified` instructions whose evidence is their
    /// instruction-derived obligation ([`INSTRUCTION_DERIVED_IS_NOT_CREDIT`]):
    /// it holds or is undecided, and is never credit.
    pub fn instruction_derived_count(&self) -> usize {
        self.unverified_with_reason_prefix(INSTRUCTION_DERIVED_IS_NOT_CREDIT)
    }

    /// Number of `Unverified` memory instructions whose reason carries the
    /// clause of their word-bound memory-effect decomposition
    /// ([`MEMORY_EFFECT_IS_NOT_CREDIT`]): no part refuted the row, and none is
    /// credit however many parts have a checked certificate. The clause
    /// follows the row's previous reason, so these rows are also counted by
    /// that reason's prefix (a pair row by [`Self::sampled_uncredited_count`],
    /// a scalar row by [`Self::instruction_derived_count`]).
    pub fn memory_effect_count(&self) -> usize {
        self.instructions
            .iter()
            .filter(|r| {
                matches!(
                    &r.result,
                    InstructionVerificationResult::Unverified { reason }
                        if reason.contains(MEMORY_EFFECT_IS_NOT_CREDIT)
                )
            })
            .count()
    }

    fn unverified_with_reason_prefix(&self, prefix: &str) -> usize {
        self.instructions
            .iter()
            .filter(|r| {
                matches!(
                    &r.result,
                    InstructionVerificationResult::Unverified { reason } if reason.starts_with(prefix)
                )
            })
            .count()
    }

    /// Number of verified instructions credited `Formal`: an independently
    /// checked solver proof of the instruction's own source-bound obligation.
    ///
    /// There is no statistical companion count: a sampled discharge is reported
    /// as `Unverified` ([`STATISTICAL_EVIDENCE_IS_NOT_CREDIT`]) and never reaches
    /// `Verified`.
    pub fn formally_credited_count(&self) -> usize {
        self.instructions
            .iter()
            .filter(|r| {
                matches!(
                    &r.result,
                    InstructionVerificationResult::Verified {
                        strength: VerificationStrength::Formal,
                        ..
                    }
                )
            })
            .count()
    }

    /// STRICT proven-honesty (task #61): coverage over the non-pseudo surface
    /// counting ONLY genuinely (non-degenerate) verified instructions.
    /// `genuinely_verified / (total - skipped) * 100`. This is the honest
    /// coverage; [`Self::coverage_percent`] is the binding-level count.
    /// A failed function prerequisite reports zero coverage.
    pub fn genuine_coverage_percent(&self) -> f64 {
        if self.precondition_failure.is_some() {
            return 0.0;
        }
        let denominator = self.total() - self.skipped_count();
        if denominator == 0 {
            100.0
        } else {
            (self.genuinely_verified_count() as f64 / denominator as f64) * 100.0
        }
    }

    /// STRICT proven-honesty (task #61): true iff every non-pseudo instruction is
    /// GENUINELY verified (non-degenerate binding) — no unverified, no failed, and
    /// no degenerate X==X binding. This is the honest "fully proven" predicate.
    pub fn all_genuinely_verified(&self) -> bool {
        self.precondition_failure.is_none()
            && self.unverified_count() == 0
            && self.failed_count() == 0
            && self.degenerate_verified_count() == 0
    }

    /// Number of instructions that had no proof (unverified).
    pub fn unverified_count(&self) -> usize {
        self.instructions
            .iter()
            .filter(|r| r.result.is_unverified())
            .count()
    }

    /// Number of instructions that were skipped (pseudo-ops).
    pub fn skipped_count(&self) -> usize {
        self.instructions
            .iter()
            .filter(|r| r.result.is_skipped())
            .count()
    }

    /// Number of instructions where verification failed.
    pub fn failed_count(&self) -> usize {
        self.instructions
            .iter()
            .filter(|r| r.result.is_failed())
            .count()
    }

    /// Binding-level coverage: verified (incl. degenerate bindings) /
    /// (total - skipped) * 100. This drives the cert-chain / compile pipeline.
    /// For the STRICT proven headline use [`Self::genuine_coverage_percent`].
    ///
    /// Returns 100.0 for empty functions or functions with only pseudo-ops
    /// (vacuous truth: all non-pseudo instructions have a discharged binding),
    /// unless a function prerequisite failed, which reports zero coverage.
    pub fn coverage_percent(&self) -> f64 {
        if self.precondition_failure.is_some() {
            return 0.0;
        }
        let denominator = self.total() - self.skipped_count();
        if denominator == 0 {
            100.0
        } else {
            (self.verified_count() as f64 / denominator as f64) * 100.0
        }
    }

    /// Returns true if every non-pseudo instruction has a discharged proof
    /// BINDING (none unverified, none failed) — the cert-chain / compile gate.
    /// This admits degenerate X==X bindings; for the STRICT proven predicate use
    /// [`Self::all_genuinely_verified`].
    pub fn all_verified(&self) -> bool {
        self.precondition_failure.is_none()
            && self.unverified_count() == 0
            && self.failed_count() == 0
    }

    /// Returns only the unverified instruction reports.
    pub fn unverified_instructions(&self) -> Vec<&InstructionReport> {
        self.instructions
            .iter()
            .filter(|r| r.result.is_unverified())
            .collect()
    }

    /// Returns only the failed instruction reports.
    pub fn failed_instructions(&self) -> Vec<&InstructionReport> {
        self.instructions
            .iter()
            .filter(|r| r.result.is_failed())
            .collect()
    }

    /// Build a target-aware inventory of emitted opcodes and proof coverage.
    pub fn emitted_opcode_inventory(&self) -> EmittedOpcodeInventoryReport {
        let entries = self
            .instructions
            .iter()
            .map(|report| {
                let (status, detail) = inventory_status(report.opcode, &report.result);
                OpcodeInventoryEntry {
                    inst_index: report.inst_index,
                    opcode: report.opcode,
                    status,
                    detail,
                }
            })
            .collect();

        EmittedOpcodeInventoryReport {
            function_name: self.function_name.clone(),
            precondition_failure: self.precondition_failure.clone(),
            entries,
        }
    }
}

impl std::fmt::Display for FunctionVerificationReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Function Verification Report: {}", self.function_name)?;
        writeln!(f, "============================================")?;
        if let Some(failure) = &self.precondition_failure {
            writeln!(f, "Function precondition FAILED: {failure}")?;
        }
        writeln!(
            f,
            "Total: {} instructions ({} verified-binding, {} unverified, {} skipped, {} failed)",
            self.total(),
            self.verified_count(),
            self.unverified_count(),
            self.skipped_count(),
            self.failed_count(),
        )?;
        // STRICT proven-honesty (task #61): the GENUINE count excludes degenerate
        // X==X bindings (which prove nothing). It is the honest proven headline.
        writeln!(
            f,
            "GENUINELY proven: {} ({} degenerate X==X bindings excluded — prove nothing)",
            self.genuinely_verified_count(),
            self.degenerate_verified_count(),
        )?;
        writeln!(
            f,
            "Coverage: {:.1}% binding / {:.1}% GENUINE (strict)",
            self.coverage_percent(),
            self.genuine_coverage_percent(),
        )?;

        if self.unverified_count() > 0 {
            writeln!(f)?;
            writeln!(f, "Unverified instructions:")?;
            for ir in self.unverified_instructions() {
                if let InstructionVerificationResult::Unverified { ref reason } = ir.result {
                    writeln!(f, "  [{}] {} -- {}", ir.inst_index, ir.opcode, reason)?;
                }
            }
        }

        if self.failed_count() > 0 {
            writeln!(f)?;
            writeln!(f, "Failed instructions:")?;
            for ir in self.failed_instructions() {
                if let InstructionVerificationResult::Failed {
                    ref proof_name,
                    ref detail,
                } = ir.result
                {
                    writeln!(
                        f,
                        "  [{}] {:?} -- proof '{}': {}",
                        ir.inst_index, ir.opcode, proof_name, detail
                    )?;
                }
            }
        }

        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Phase-2 operand reconstruction (PILOT: AArch64 integer ALU) — task #63
// ---------------------------------------------------------------------------
//
// The static lowering proofs in the database build BOTH sides of an ALU
// obligation from the SAME symbolic vars `a, b` (e.g. proof_iadd_i32:
// trust_ir_expr = encode_trust_ir_binop(Iadd, a, b) = a.bvadd(b);
// aarch64_expr = encode_add_rr(a, b) = a.bvadd(b)). Those are STRUCTURALLY
// equal, so the strict gate (#61) correctly refuses to count them: a degenerate
// `X == X` obligation can never be refuted by a wrong isel choice.
//
// This pilot RECONSTRUCTS the machine side FROM THE REAL EMITTED INSTRUCTION at
// verify time. The source side is built from the INTENDED source op over the
// SAME shared symbols; the machine side is built from the REAL opcode wired to
// the REAL positional operands. The two sides therefore agree IFF isel emitted a
// semantically correct instruction. If isel emitted SUB for an Iadd, the machine
// side is bvsub and the source side is bvadd ⇒ REFUTE. If isel wired a
// non-commutative op (SUB) with swapped inputs ⇒ REFUTE. THAT is the content.
//
// ANTI-f81e45b: this path performs NO `name.contains` lookup. The
// opcode→source-op binding is a TYPED, EXHAUSTIVE match
// ([`opcode_to_source_op`]); the operand binding uses a TYPED per-opcode
// positional schema. Asserted by `tests/reconstruction_alu.rs`.
//
// TCB note (updated by TV-2): the "intended source op" used by the
// reconstruction is still derived from the emitted opcode, but on the
// compiler cert path (`verify_with_lir_source`) it is now CROSS-CHECKED
// against the TV-1 lowering-provenance stamp resolved in the REPLAYED LIR
// function: the stamped source instruction must exist, its recomputed digest
// must match the stamp, and its op class must be able to contain the emitted
// opcode's class ([`crate::provenance_xcheck`]). On AArch64 the check runs
// WARN-ONLY by default (telemetry + counter, no verdict change): the aarch64
// differential corpus cannot execute on the x86 validation host, so the §2.4
// warn->enforce flip is deferred to the Apple-Silicon lane. Until that flip,
// "isel intended Iadd when it emitted AddRR" remains TRUSTED here in enforce
// terms (x86-64 already enforces); exact-operand identity binding is deferred
// to TV-3's pre-pass walk on both arches. The wiring of the machine side to
// the real operands is the soundness crux, which is why the
// inject-wrong-wiring refutation test exists.

/// The SOURCE operand schema arity of a reconstructed ALU instruction.
///
/// Binary ALU ops (`AddRR`/`SubRR`/`MulRR`, and the immediate forms
/// `AddRI`/`SubRI`) have a `[dst, src1, src2]` operand layout; the SOURCE arity
/// (the operands that feed the value computation) is 2. Unary `Neg` has a
/// `[dst, src]` layout; SOURCE arity 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AluArity {
    /// `[dst, src1, src2]` — two value-producing source slots.
    Binary,
    /// `[dst, src]` — one value-producing source slot.
    Unary,
    /// `[dst, rn, rm, ra]` — THREE value-producing source slots. Used by the
    /// FUSED multiply-add family (`Madd`/`Msub`): the source is a COMPOUND
    /// trust_ir expression (`a*b+c` / `c-a*b`), not a single opcode.
    Ternary,
}

impl AluArity {
    fn as_u8(self) -> u8 {
        match self {
            AluArity::Binary => 2,
            AluArity::Unary => 1,
            AluArity::Ternary => 3,
        }
    }
}

/// The intended trust_ir SOURCE operation family for a reconstructed AArch64
/// instruction, resolved by a TYPED EXHAUSTIVE match (NOT a string lookup).
///
/// `trust_cg_lower::instructions::Opcode` is `Clone + PartialEq` but not
/// `Copy`/`Eq`, so this enum mirrors those bounds.
///
/// Each variant pairs a trust_ir source-side encoder with the AArch64
/// machine-side encoder it must agree with; the credit comes from those two
/// being built independently (source op + real opcode), so a wrong isel choice
/// refutes.
#[derive(Debug, Clone, PartialEq)]
enum SourceOp {
    /// Binary trust_ir arithmetic op dischargeable via
    /// `encode_trust_ir_binop` (Iadd/Isub/Imul).
    Binary(trust_cg_lower::instructions::Opcode),
    /// Binary trust_ir BITWISE op dischargeable via
    /// `encode_trust_ir_bitwise_binop` (Band/Bor/Bxor/BandNot/BorNot). Machine
    /// side is the matching AArch64 AND/ORR/EOR/BIC/ORN encoder.
    Bitwise(trust_cg_lower::instructions::Opcode),
    /// EOR whose second machine source is shifted by an in-range constant.
    /// The dedicated four-operand schema is `[dst, Rn, Rm, Imm(k)]`; the
    /// generic binary reconstructor deliberately accepts only three operands.
    BitwiseShifted {
        op: trust_cg_lower::instructions::Opcode,
        kind: crate::aarch64_semantics::RegShiftKind,
    },
    /// Binary trust_ir SHIFT op dischargeable via `encode_trust_ir_shift`
    /// (Ishl/Ushr/Sshr). Machine side is the FAITHFUL (amount-masked) AArch64
    /// LSLV/LSRV/ASRV encoder, paired with a LOAD-BEARING `amount < width`
    /// precondition (task #57).
    Shift(trust_cg_lower::instructions::Opcode),
    /// Standalone immediate rotate-right. The source side is the frontend's
    /// shift/OR idiom and the machine side is the architectural `EXTR Rn,Rn`
    /// alias emitted for `RorRI`. The baked immediate is reconstructed from
    /// the real instruction and must be in `1..width`; rotate-by-zero is a move
    /// alias and deliberately remains outside this non-degenerate lane.
    RotateRightImmediate,
    /// Unary integer negate (trust_ir `Ineg`), dischargeable via
    /// `encode_trust_ir_neg`.
    ///
    /// NOTE: the unary bitwise NOT (`Bnot`/`MVN`) is NOT a `SourceOp` variant: on
    /// AArch64 `MVN Rd, Rm` is the `ORN Rd, ZR, Rm` alias, so it shares the
    /// `OrnRR` opcode and is recognized in the reconstructor's Binary arm from
    /// the zero-register `rn` slot, not via a dedicated opcode→`SourceOp` row.
    Neg,
    /// Unary signed integer extension (trust_ir `Sextend`), width-changing:
    /// from `from_bits` to `to_bits`. Machine side is `encode_sxt`.
    Sextend { from_bits: u32, to_bits: u32 },
    /// Unary unsigned integer extension (trust_ir `Uextend`), width-changing:
    /// from `from_bits` to `to_bits`. Machine side is `encode_uxt`.
    Uextend { from_bits: u32, to_bits: u32 },

    /// Integer DIVIDE (trust_ir `Sdiv`/`Udiv`), dischargeable via
    /// `encode_trust_ir_binop`. Machine side is `encode_sdiv_rr`/`encode_udiv_rr`.
    /// Carries a LOAD-BEARING `divisor != 0` precondition (trust-ir div-by-zero
    /// is UB and scoped out): a SDIV-for-Udiv (or swapped wiring) refutes on
    /// negative operands. Non-commutative.
    IntDiv(trust_cg_lower::instructions::Opcode),

    /// FUSED multiply-add (`Madd`) or multiply-subtract (`Msub`). NOT a single
    /// trust_ir opcode: the source is the COMPOUND expression `a*b+c` (Madd) or
    /// `c-a*b` (Msub), built from `Imul` + `Iadd`/`Isub`. Machine side is
    /// `encode_madd_rr`/`encode_msub_rr` over the ternary `[dst, rn, rm, ra]`
    /// schema. A wrong fused op (Madd↔Msub) or wrong operand wiring refutes.
    MulAdd { sub: bool },

    /// Scalar FUSED FP multiply-add (`FMADD`/`FMSUB`). NOT a single trust_ir
    /// opcode: the source is the SINGLE-ROUNDING fused `a*b+c` (`FMADD`) /
    /// `c-a*b` (`FMSUB`) via `fp.fma`, matching the machine side's `encode_fmadd_rr`
    /// over the ternary `[dst, rn, rm, ra]` FP schema. The distinguishing feature
    /// vs `MulAdd` (integer) is that this is FLOATING-POINT with a SINGLE rounding
    /// — an unfused round-twice model or a sign-flipped `FMSUB` REFUTES.
    FpFma { sub: bool },

    /// Binary FLOATING-POINT value op (trust_ir `Fadd`/`Fsub`/`Fmul`/`Fdiv`),
    /// dischargeable via `encode_trust_ir_fp_binop`. Machine side is
    /// `encode_fadd_rr`/`encode_fsub_rr`/`encode_fmul_rr`/`encode_fdiv_rr`. The
    /// FP width comes from the FP register class (Fpr32→F32, Fpr64→F64). A wrong
    /// FP opcode (Fadd↔Fsub) refutes; a swapped non-commutative wiring
    /// (Fsub/Fdiv) refutes under the wiring-preserving FP evaluator.
    FpBinary(trust_cg_lower::instructions::Opcode),

    /// Unary FLOATING-POINT value op (trust_ir `Fneg`/`Fabs`/`Fsqrt`),
    /// dischargeable via `encode_trust_ir_fp_unaryop`. Machine side is
    /// `encode_fneg`/`encode_fabs`/`encode_fsqrt`.
    FpUnary(trust_cg_lower::instructions::Opcode),

    /// FP→INT conversion (trust_ir `FcvtToInt`/`FcvtToUint`), round-toward-zero.
    /// Machine side is `encode_fcvtzs`/`encode_fcvtzu`. `signed` selects the
    /// signed (FCVTZS) vs unsigned (FCVTZU) form; FCVTZS-for-FCVTZU refutes on a
    /// negative input.
    FpToInt { signed: bool },

    /// INT→FP conversion (trust_ir `FcvtFromInt`/`FcvtFromUint`),
    /// round-to-nearest-even. Machine side is `encode_scvtf`/`encode_ucvtf`.
    /// `signed` selects SCVTF vs UCVTF; SCVTF-for-UCVTF refutes on an input with
    /// the source MSB set.
    IntToFp { signed: bool },

    /// FP-FORMAT conversion — a cast BETWEEN two IEEE-754 floating-point formats
    /// (trust_ir `Fpromote`/`Fdemote`), width-CHANGING from `from_bits` to
    /// `to_bits` (both FP). Machine side is `encode_fcvt_sd` (F32→F64 widen) /
    /// `encode_fcvt_ds` (F64→F32 narrow, rounding-aware). Source side is
    /// `encode_trust_ir_fp_format_convert` keyed on the DESTINATION format. A
    /// wrong DIRECTION (FCVT-SD where FCVT-DS was intended, or vice versa)
    /// produces a different destination format and DIVERGES under the
    /// wiring-preserving FP evaluator for a value that does not round-trip through
    /// binary32 ⇒ REFUTE.
    FpFormatConvert { from_bits: u32, to_bits: u32 },

    /// Scalar `FMOV`-IMMEDIATE constant materialization (trust_ir `Fconst` with
    /// an FMOV-encodable value). NOT a runtime value op: the source is the named
    /// constant's IEEE bit pattern and the machine side is the hardware
    /// `VFPExpandImm` DECODE of the 8-bit field the codegen encoder picks. The
    /// reconstructed obligation `assemble(encode(v)) == bits(v)` is an ENCODING
    /// round-trip (structural bit-assembly vs the constant), so a wrong field
    /// formula / bit placement REFUTES — not a degenerate `const == const`.
    FmovImm,
}

/// Resolve the INTENDED trust_ir source op + operand schema for a reconstructable
/// AArch64 opcode via a TYPED, EXHAUSTIVE match — NOT a string lookup
/// (anti-f81e45b).
///
/// Reconstructable set (task #63 Phase-2 pilot + this extension):
/// - ALU:     `AddRR`/`AddRI`->Iadd, `SubRR`/`SubRI`->Isub, `MulRR`->Imul,
///   `Neg`->Ineg
/// - BITWISE: `AndRR`/`AndRI`->Band, `OrrRR`/`OrrRI`->Bor, `EorRR`/`EorRI`->Bxor,
///   `BicRR`->BandNot, `OrnRR`-> (BorNot | Bnot, decided by the rn slot)
/// - EXTENDS: `Sxtb`/`Sxth`/`Sxtw`->Sextend, `Uxtb`/`Uxth`/`Uxtw`->Uextend
/// - SHIFTS:  `LslRR`/`LslRI`->Ishl, `LsrRR`/`LsrRI`->Ushr, `AsrRR`/`AsrRI`->Sshr
///
/// `OrnRR` is special: it is the SAME opcode for both binary `BorNot`
/// (`Rd = Rn | ~Rm`) and the unary `MVN`/`Bnot` alias (`Rd = ZR | ~Rm = ~Rm`).
/// The arity returned here is `Binary` (the generic ORN shape); the
/// reconstructor inspects the `rn` slot and switches to the `Bnot` unary
/// semantics when `rn` is the zero register. The extends carry their source/dest
/// widths in `SourceOp` because they are width-CHANGING (unlike the same-width
/// ALU/bitwise ops).
///
/// Returns `None` for every NON-reconstructable opcode, so the caller leaves
/// those on their existing path unchanged. The match is wildcard-FREE over the
/// reconstructable arms and falls through to `None` for the rest.
///
/// The `OperandSize` carried here is a *default* (`S32`); the real width is
/// taken from the destination register in [`reconstruct_alu_obligation`]. It
/// exists in the return tuple to make the typed binding explicit per the
/// blueprint.
fn opcode_to_source_op(opcode: AArch64Opcode) -> Option<(SourceOp, AluArity, OperandSize)> {
    use trust_cg_lower::instructions::Opcode;
    match opcode {
        // ---- Integer ALU (pilot) ----
        AArch64Opcode::AddRR | AArch64Opcode::AddRI => Some((
            SourceOp::Binary(Opcode::Iadd),
            AluArity::Binary,
            OperandSize::S32,
        )),
        AArch64Opcode::SubRR | AArch64Opcode::SubRI => Some((
            SourceOp::Binary(Opcode::Isub),
            AluArity::Binary,
            OperandSize::S32,
        )),
        AArch64Opcode::MulRR => Some((
            SourceOp::Binary(Opcode::Imul),
            AluArity::Binary,
            OperandSize::S32,
        )),
        AArch64Opcode::Neg => Some((SourceOp::Neg, AluArity::Unary, OperandSize::S32)),

        // ---- Bitwise (commutative: And/Orr/Eor) ----
        AArch64Opcode::AndRR | AArch64Opcode::AndRI => Some((
            SourceOp::Bitwise(Opcode::Band),
            AluArity::Binary,
            OperandSize::S32,
        )),
        AArch64Opcode::OrrRR | AArch64Opcode::OrrRI => Some((
            SourceOp::Bitwise(Opcode::Bor),
            AluArity::Binary,
            OperandSize::S32,
        )),
        AArch64Opcode::EorRR | AArch64Opcode::EorRI => Some((
            SourceOp::Bitwise(Opcode::Bxor),
            AluArity::Binary,
            OperandSize::S32,
        )),
        AArch64Opcode::EorRRLsl => Some((
            SourceOp::BitwiseShifted {
                op: Opcode::Bxor,
                kind: crate::aarch64_semantics::RegShiftKind::Lsl,
            },
            AluArity::Binary,
            OperandSize::S32,
        )),
        AArch64Opcode::EorRRLsr => Some((
            SourceOp::BitwiseShifted {
                op: Opcode::Bxor,
                kind: crate::aarch64_semantics::RegShiftKind::Lsr,
            },
            AluArity::Binary,
            OperandSize::S32,
        )),
        // ---- Bitwise (non-commutative: Bic/Orn) ----
        AArch64Opcode::BicRR => Some((
            SourceOp::Bitwise(Opcode::BandNot),
            AluArity::Binary,
            OperandSize::S32,
        )),
        // ORN doubles as MVN (Bnot) when rn is the zero register; the
        // reconstructor decides per-instruction from the rn slot.
        AArch64Opcode::OrnRR => Some((
            SourceOp::Bitwise(Opcode::BorNot),
            AluArity::Binary,
            OperandSize::S32,
        )),

        // ---- Shifts (resolve #57 with a load-bearing amount<width precond) ----
        AArch64Opcode::LslRR | AArch64Opcode::LslRI => Some((
            SourceOp::Shift(Opcode::Ishl),
            AluArity::Binary,
            OperandSize::S32,
        )),
        AArch64Opcode::LsrRR | AArch64Opcode::LsrRI => Some((
            SourceOp::Shift(Opcode::Ushr),
            AluArity::Binary,
            OperandSize::S32,
        )),
        AArch64Opcode::AsrRR | AArch64Opcode::AsrRI => Some((
            SourceOp::Shift(Opcode::Sshr),
            AluArity::Binary,
            OperandSize::S32,
        )),
        AArch64Opcode::RorRI => Some((
            SourceOp::RotateRightImmediate,
            AluArity::Unary,
            OperandSize::S32,
        )),

        // ---- Extends (unary, width-changing) ----
        AArch64Opcode::Sxtb => Some((
            SourceOp::Sextend {
                from_bits: 8,
                to_bits: 32,
            },
            AluArity::Unary,
            OperandSize::S32,
        )),
        AArch64Opcode::Sxth => Some((
            SourceOp::Sextend {
                from_bits: 16,
                to_bits: 32,
            },
            AluArity::Unary,
            OperandSize::S32,
        )),
        AArch64Opcode::Sxtw => Some((
            SourceOp::Sextend {
                from_bits: 32,
                to_bits: 64,
            },
            AluArity::Unary,
            OperandSize::S64,
        )),
        AArch64Opcode::Uxtb => Some((
            SourceOp::Uextend {
                from_bits: 8,
                to_bits: 32,
            },
            AluArity::Unary,
            OperandSize::S32,
        )),
        AArch64Opcode::Uxth => Some((
            SourceOp::Uextend {
                from_bits: 16,
                to_bits: 32,
            },
            AluArity::Unary,
            OperandSize::S32,
        )),
        AArch64Opcode::Uxtw => Some((
            SourceOp::Uextend {
                from_bits: 32,
                to_bits: 64,
            },
            AluArity::Unary,
            OperandSize::S64,
        )),

        // ---- Integer divide (load-bearing divisor!=0 precond; UB scoped) ----
        AArch64Opcode::SDiv => Some((
            SourceOp::IntDiv(Opcode::Sdiv),
            AluArity::Binary,
            OperandSize::S32,
        )),
        AArch64Opcode::UDiv => Some((
            SourceOp::IntDiv(Opcode::Udiv),
            AluArity::Binary,
            OperandSize::S32,
        )),

        // ---- Fused multiply-add/sub (ternary [dst, rn, rm, ra]) ----
        AArch64Opcode::Madd => Some((
            SourceOp::MulAdd { sub: false },
            AluArity::Ternary,
            OperandSize::S32,
        )),
        AArch64Opcode::Msub => Some((
            SourceOp::MulAdd { sub: true },
            AluArity::Ternary,
            OperandSize::S32,
        )),

        // ---- FP binary value ops (commutative: Fadd/Fmul; non-comm: Fsub/Fdiv) ----
        AArch64Opcode::FaddRR => Some((
            SourceOp::FpBinary(Opcode::Fadd),
            AluArity::Binary,
            OperandSize::S32,
        )),
        AArch64Opcode::FsubRR => Some((
            SourceOp::FpBinary(Opcode::Fsub),
            AluArity::Binary,
            OperandSize::S32,
        )),
        AArch64Opcode::FmulRR => Some((
            SourceOp::FpBinary(Opcode::Fmul),
            AluArity::Binary,
            OperandSize::S32,
        )),
        AArch64Opcode::FdivRR => Some((
            SourceOp::FpBinary(Opcode::Fdiv),
            AluArity::Binary,
            OperandSize::S32,
        )),
        // Scalar FUSED multiply-add (ternary [dst, rn, rm, ra], single rounding).
        AArch64Opcode::FmaddRR => Some((
            SourceOp::FpFma { sub: false },
            AluArity::Ternary,
            OperandSize::S32,
        )),
        AArch64Opcode::FminnmRR => Some((
            SourceOp::FpBinary(Opcode::Fmin),
            AluArity::Binary,
            OperandSize::S32,
        )),
        AArch64Opcode::FmaxnmRR => Some((
            SourceOp::FpBinary(Opcode::Fmax),
            AluArity::Binary,
            OperandSize::S32,
        )),

        // ---- FP unary value ops ----
        AArch64Opcode::FnegRR => Some((
            SourceOp::FpUnary(Opcode::Fneg),
            AluArity::Unary,
            OperandSize::S32,
        )),
        AArch64Opcode::FabsRR => Some((
            SourceOp::FpUnary(Opcode::Fabs),
            AluArity::Unary,
            OperandSize::S32,
        )),
        AArch64Opcode::FsqrtRR => Some((
            SourceOp::FpUnary(Opcode::Fsqrt),
            AluArity::Unary,
            OperandSize::S32,
        )),
        // ---- FP round-to-integral (FRINT{M,P,Z} = floor/ceil/trunc) ----
        AArch64Opcode::FrintmRR => Some((
            SourceOp::FpUnary(Opcode::Ffloor),
            AluArity::Unary,
            OperandSize::S32,
        )),
        AArch64Opcode::FrintpRR => Some((
            SourceOp::FpUnary(Opcode::Fceil),
            AluArity::Unary,
            OperandSize::S32,
        )),
        AArch64Opcode::FrintzRR => Some((
            SourceOp::FpUnary(Opcode::Ftrunc),
            AluArity::Unary,
            OperandSize::S32,
        )),

        // ---- FP <-> int conversions (cross int/fp; rounding-mode aware) ----
        AArch64Opcode::FcvtzsRR => Some((
            SourceOp::FpToInt { signed: true },
            AluArity::Unary,
            OperandSize::S32,
        )),
        AArch64Opcode::FcvtzuRR => Some((
            SourceOp::FpToInt { signed: false },
            AluArity::Unary,
            OperandSize::S32,
        )),
        AArch64Opcode::ScvtfRR => Some((
            SourceOp::IntToFp { signed: true },
            AluArity::Unary,
            OperandSize::S32,
        )),
        AArch64Opcode::UcvtfRR => Some((
            SourceOp::IntToFp { signed: false },
            AluArity::Unary,
            OperandSize::S32,
        )),

        // ---- FP-format casts (FCVT precision widen/narrow; both operands FP) ----
        // FcvtSD widens F32→F64 (Fpromote); FcvtDS narrows F64→F32 (Fdemote).
        AArch64Opcode::FcvtSD => Some((
            SourceOp::FpFormatConvert {
                from_bits: 32,
                to_bits: 64,
            },
            AluArity::Unary,
            OperandSize::S64,
        )),
        AArch64Opcode::FcvtDS => Some((
            SourceOp::FpFormatConvert {
                from_bits: 64,
                to_bits: 32,
            },
            AluArity::Unary,
            OperandSize::S32,
        )),

        // Scalar FMOV-immediate constant materialization (FP `[dst, FImm]`).
        AArch64Opcode::FmovImm => Some((SourceOp::FmovImm, AluArity::Unary, OperandSize::S32)),

        // All non-reconstructable opcodes keep their existing DB-substring path.
        _ => None,
    }
}

/// TV-2: the DEFINITE semantic [`OpClass`] of an emitted AArch64 instruction,
/// derived from the SAME typed [`opcode_to_source_op`] binding the cert's
/// reconstruction path uses — or `None` when the instruction carries no
/// definite class (unmapped opcodes, and universal lowering GLUE any source
/// may legitimately emit: extends of narrow carriers, FMOV-immediate constant
/// materialization, and the `EOR r,r,r` zero idiom).
///
/// `None` exempts the instruction from the class-consistency half of the
/// provenance cross-check only; the attribution-integrity half (dangling
/// coordinates / digest mismatch) still applies to every stamped instruction.
fn aarch64_emitted_op_class(inst: &MachInst) -> Option<OpClass> {
    use trust_cg_lower::instructions::Opcode;

    // Zero idiom: EOR of a register with itself materializes 0 — constant
    // materialization glue, not a semantic Bxor claim.
    if matches!(inst.opcode, AArch64Opcode::EorRR)
        && inst.operands.len() == 3
        && inst.operands[1] == inst.operands[2]
    {
        return None;
    }

    let (source_op, _, _) = opcode_to_source_op(inst.opcode)?;
    let int_binop_class = |op: &Opcode| -> Option<OpClass> {
        match op {
            Opcode::Iadd => Some(OpClass::IntAdd),
            Opcode::Isub => Some(OpClass::IntSub),
            Opcode::Imul => Some(OpClass::IntMul),
            _ => None,
        }
    };
    match &source_op {
        SourceOp::Binary(op) => int_binop_class(op),
        SourceOp::Bitwise(_) => Some(OpClass::Bitwise),
        SourceOp::BitwiseShifted { .. } => Some(OpClass::Bitwise),
        SourceOp::Shift(_) => Some(OpClass::Shift),
        SourceOp::RotateRightImmediate => Some(OpClass::Bitwise),
        SourceOp::Neg => Some(OpClass::IntNeg),
        // Universal glue: exempt from the class check (never from integrity).
        SourceOp::Sextend { .. } | SourceOp::Uextend { .. } | SourceOp::FmovImm => None,
        SourceOp::IntDiv(_) => Some(OpClass::IntDiv),
        // MADD/MSUB legitimately implement an Iadd/Isub anchor that consumed
        // an Imul — the dedicated class encodes that fusion in the matrix.
        SourceOp::MulAdd { .. } => Some(OpClass::FusedMulAdd),
        SourceOp::FpFma { .. } => Some(OpClass::FpArith),
        SourceOp::FpBinary(_) | SourceOp::FpUnary(_) => Some(OpClass::FpArith),
        SourceOp::FpToInt { .. } | SourceOp::IntToFp { .. } | SourceOp::FpFormatConvert { .. } => {
            Some(OpClass::FpConvert)
        }
    }
}

/// Map an FP register class width (32→F32, 64→F64) to the SMT
/// `(eb, sb)` exponent/significand pair and a [`FPSize`].
///
/// Returns `None` for any non-FP width (the reconstruction fails closed rather
/// than guess an FP format for a GPR-width destination).
fn fp_format_from_width(width: u32) -> Option<(u32, u32, crate::aarch64_semantics::FPSize)> {
    use crate::aarch64_semantics::FPSize;
    match width {
        32 => Some((8, 24, FPSize::Single)),
        64 => Some((11, 53, FPSize::Double)),
        _ => None,
    }
}

/// True iff a [`MachOperand`] is in an FP/SIMD register class (Sd/Dd/...).
fn operand_is_fp_reg(op: &MachOperand) -> bool {
    use trust_cg_ir::RegClass;
    let class = match op {
        MachOperand::VReg(v) => v.class,
        MachOperand::PReg(p) => preg_class(*p),
        _ => return false,
    };
    matches!(
        class,
        RegClass::Fpr8 | RegClass::Fpr16 | RegClass::Fpr32 | RegClass::Fpr64 | RegClass::Fpr128
    )
}

/// Width of a scalar GPR operand that denotes a value-bearing register.
///
/// SP/WSP, ZR, and FP/SIMD registers are intentionally rejected. A
/// reconstruction that binds a fresh symbolic value must not silently treat a
/// fixed zero register, stack pointer, or differently typed register as that
/// unconstrained source.
fn operand_plain_gpr_width_bits(op: &MachOperand) -> Option<u32> {
    use trust_cg_ir::RegClass;
    let class = match op {
        MachOperand::VReg(v) => v.class,
        MachOperand::PReg(p) if !matches!(*p, SP | WSP | XZR | WZR) => preg_class(*p),
        _ => return None,
    };
    matches!(class, RegClass::Gpr32 | RegClass::Gpr64).then(|| class.size_bits())
}

/// True iff `op` is the AArch64 zero register (`XZR`/`WZR`).
///
/// Used to recognize the `MVN` (`Bnot`) alias of `OrnRR` (`ORN Rd, ZR, Rm`): an
/// `OrnRR` whose `rn` slot is the zero register computes `ZR | ~Rm = ~Rm`, i.e.
/// a unary bitwise NOT of `Rm`, not a binary OR-NOT.
fn is_zero_reg(op: &MachOperand) -> bool {
    matches!(
        op,
        MachOperand::Special(SpecialReg::XZR | SpecialReg::WZR) | MachOperand::PReg(XZR | WZR)
    )
}

/// Width in bits of a register-bearing [`MachOperand`].
///
/// Returns `None` for non-register operands (the caller treats an immediate
/// slot separately, and anything else fails the reconstruction closed).
fn operand_reg_width_bits(op: &MachOperand) -> Option<u32> {
    match op {
        MachOperand::VReg(v) => Some(v.class.size_bits()),
        MachOperand::PReg(p) => Some(preg_class(*p).size_bits()),
        MachOperand::Special(SpecialReg::XZR) => Some(64),
        MachOperand::Special(SpecialReg::WZR) => Some(32),
        MachOperand::Special(SpecialReg::SP) => Some(64),
        _ => None,
    }
}

/// Map an AArch64 destination/operand width to an [`OperandSize`].
fn width_to_operand_size(width: u32) -> Option<OperandSize> {
    match width {
        32 => Some(OperandSize::S32),
        64 => Some(OperandSize::S64),
        _ => None,
    }
}

/// Reconstruct a lowering [`ProofObligation`] for a reconstructable AArch64
/// instruction directly FROM THE REAL EMITTED INSTRUCTION (task #63 Phase-2).
///
/// Returns `None` (caller falls back to the existing path) for any
/// non-reconstructable opcode or any instruction whose operand shape does not
/// match the typed per-opcode schema (fail-closed: a malformed instruction is
/// NOT silently credited, it simply is not reconstructed).
///
/// # What it does
///
/// 1. Resolves the INTENDED source op family + arity via the TYPED exhaustive
///    [`opcode_to_source_op`] (no string lookup).
/// 2. Reads `inst.operands` POSITIONALLY using the typed per-opcode schema:
///    - Binary: `[dst, src1, src2]` (ALU/bitwise: src2 reg or imm; shifts:
///      src2 is the amount; ORN-as-MVN: src1 is the zero register)
///    - Unary:  `[dst, src]`        (Neg/extends)
///      Each SOURCE register slot is bound to a FRESH symbolic var of the
///      operand's width; an immediate slot (the `RI` forms) is bound to a
///      `bv_const` of the immediate value at the destination width.
/// 3. Builds `trust_ir_expr` from the INTENDED source op over the shared syms
///    and `aarch64_expr` from the REAL opcode's encoder, wired EXACTLY as the
///    emitted instruction wires its operands.
/// 4. Tags the obligation [`MachineSideProvenance::Reconstructed`].
///
/// The two sides agree IFF the real opcode is the correct lowering of the
/// intended source op with correct operand wiring. A wrong opcode or wrong
/// (non-commutative) wiring yields structurally distinct sides ⇒ the obligation
/// REFUTES under `verify_by_evaluation`.
///
/// SHIFTS additionally carry a LOAD-BEARING `amount < width` precondition (task
/// #57): the machine side is the FAITHFUL hardware-masked encoder
/// (`encode_lsl_rr_masked` etc.) and the source side is the plain-`bvshl`
/// trust_ir encoder. In range the mask is the identity so they agree; out of
/// range the masked machine side and the clamp-to-0 source side DIVERGE, so the
/// precondition is genuinely required for the proof to discharge `Valid` (strip
/// it and a shift by exactly `width` refutes).
pub fn reconstruct_alu_obligation(inst: &MachInst) -> Option<ProofObligation> {
    use crate::aarch64_semantics::{
        encode_add_rr, encode_and_rr, encode_asr_rr_masked, encode_bic_rr, encode_eor_rr,
        encode_lsl_rr_masked, encode_lsr_rr_masked, encode_mul_rr, encode_mvn, encode_neg,
        encode_orn_rr, encode_orr_rr, encode_sub_rr,
    };
    use crate::trust_ir_semantics::{
        encode_trust_ir_binop, encode_trust_ir_bitwise_binop, encode_trust_ir_bnot,
        encode_trust_ir_neg, encode_trust_ir_shift,
    };
    use trust_cg_lower::instructions::Opcode;

    let (source_op, arity, _default_size) = opcode_to_source_op(inst.opcode)?;
    if register_alu_extra_operand_refusal_reason(inst).is_some() {
        return None;
    }

    let from_opcode = format!("{:?}", inst.opcode);

    // FP / DIV / MADD families have their OWN operand schemas and source models
    // (FP-typed leaves, the ternary [dst,rn,rm,ra] schema, the divisor!=0
    // precond, cross int/fp conversions). Dispatch them to dedicated builders
    // BEFORE the generic same-width integer GPR logic below, which assumes
    // GPR-width same-class operands.
    match &source_op {
        SourceOp::IntDiv(op) => {
            return reconstruct_int_div(inst, op, from_opcode);
        }
        SourceOp::MulAdd { sub } => {
            return reconstruct_mul_add(inst, *sub, from_opcode);
        }
        SourceOp::FpFma { sub } => {
            return reconstruct_fp_fma(inst, *sub, from_opcode);
        }
        SourceOp::FpBinary(op) => {
            return reconstruct_fp_binary(inst, op, from_opcode);
        }
        SourceOp::FpUnary(op) => {
            return reconstruct_fp_unary(inst, op, from_opcode);
        }
        SourceOp::FpToInt { signed } => {
            return reconstruct_fp_to_int(inst, *signed, from_opcode);
        }
        SourceOp::IntToFp { signed } => {
            return reconstruct_int_to_fp(inst, *signed, from_opcode);
        }
        SourceOp::FpFormatConvert { from_bits, to_bits } => {
            return reconstruct_fp_format_convert(inst, *from_bits, *to_bits, from_opcode);
        }
        SourceOp::FmovImm => {
            return reconstruct_fmov_imm(inst, from_opcode);
        }
        SourceOp::BitwiseShifted { op, kind } => {
            return reconstruct_bitwise_shifted(inst, op, *kind, from_opcode);
        }
        SourceOp::RotateRightImmediate => {
            return reconstruct_ror_immediate(inst, from_opcode);
        }
        // Integer ALU / bitwise / shift / extend / neg fall through to the
        // generic logic below.
        SourceOp::Binary(_)
        | SourceOp::Bitwise(_)
        | SourceOp::Shift(_)
        | SourceOp::Neg
        | SourceOp::Sextend { .. }
        | SourceOp::Uextend { .. } => {}
    }

    // Destination is always operand slot 0 and fixes the operation width.
    let dst = inst.operands.first()?;
    // The generic reconstruction models the result as a value produced into a
    // normal scalar GPR. A zero-register destination discards that value and a
    // stack-pointer destination has distinct architectural semantics, so
    // neither may inherit this ordinary-register obligation.
    let dst_width = operand_plain_gpr_width_bits(dst)?;
    let size = width_to_operand_size(dst_width)?;
    let ty = crate::aarch64_semantics::operand_size_to_type(size);

    match arity {
        AluArity::Binary => {
            // Typed positional schema: [dst, src1, src2].
            if inst.operands.len() != 3 {
                return None;
            }
            let src1 = &inst.operands[1];
            let src2 = &inst.operands[2];

            // SPECIAL CASE — ORN as MVN/Bnot: `ORN Rd, ZR, Rm == ~Rm`. When the
            // rn slot is the zero register, the instruction is a UNARY bitwise
            // NOT of Rm, not a binary OR-NOT. Re-route to the Bnot reconstruction
            // over src2 so the proof models the actual (unary) semantics.
            if matches!(source_op, SourceOp::Bitwise(Opcode::BorNot)) && is_zero_reg(src1) {
                if operand_reg_width_bits(src1)? != dst_width {
                    return None;
                }
                let rm_width = operand_reg_width_bits(src2)?;
                if rm_width != dst_width {
                    return None;
                }
                let sym = SmtExpr::var("recon_src", dst_width);
                let trust_ir_expr = encode_trust_ir_bnot(ty, sym.clone());
                let aarch64_expr = encode_mvn(size, sym.clone());
                return Some(ProofObligation {
                    name: format!(
                        "RECONSTRUCTED Bnot_{} -> {:?} (MVN alias, real-operand)",
                        dst_width, inst.opcode
                    ),
                    trust_ir_expr,
                    aarch64_expr,
                    inputs: vec![("recon_src".to_string(), dst_width)],
                    preconditions: vec![],
                    fp_inputs: vec![],
                    category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
                    machine_side_provenance: MachineSideProvenance::Reconstructed {
                        from_opcode,
                        // Unary semantics even though the opcode shape is ternary.
                        arity: AluArity::Unary.as_u8(),
                    },
                });
            }

            // src1 must be a register; bind to a fresh symbolic var at its width.
            let src1_width = operand_reg_width_bits(src1)?;
            // src1 width must match the destination width (W vs X consistency).
            if src1_width != dst_width {
                return None;
            }
            let sym1 = SmtExpr::var("recon_src1", dst_width);

            // src2 is either a register (RR form) or an immediate (RI form).
            let sym2 = match src2 {
                MachOperand::Imm(imm) => {
                    // RI form: bind the immediate to a bv_const at the op width.
                    let raw = (*imm as i128) as u128;
                    let masked = (raw as u64) & crate::smt::mask(u64::MAX, dst_width);
                    SmtExpr::bv_const(masked, dst_width)
                }
                reg => {
                    let w = operand_reg_width_bits(reg)?;
                    if w == dst_width {
                        SmtExpr::var("recon_src2", dst_width)
                    } else if w < dst_width && matches!(source_op, SourceOp::Shift(_)) {
                        // Mixed-width SHIFT amount (e.g. `x:u64 >> y:u32`): isel keeps
                        // the amount in a narrower (W) register. The hardware reads it
                        // zero-extended into the X register and masks to the bottom
                        // 5/6 bits, so the high bits are don't-cares. Model the amount
                        // as a w-bit var zero-extended to dst_width; the #57
                        // amount<width precondition and the masked machine encoder are
                        // unaffected, and trust-ir over-shift is UB (interpret.rs
                        // shift_amount returns Err(ub) for amount>=width), so crediting
                        // the masked lowering is sound for EVERY amount. Without this,
                        // the width check fell closed and rejected all u32-amount
                        // shifts on 64-bit values. (Restricted to shifts: other binary
                        // ops never have a width-mismatched second operand.)
                        SmtExpr::var("recon_src2", w).zero_ext(dst_width - w)
                    } else {
                        return None;
                    }
                }
            };

            // SOURCE side: the INTENDED trust_ir op over the shared syms. Plus,
            // for shifts, a LOAD-BEARING amount<width precondition (#57).
            let mut preconditions: Vec<SmtExpr> = vec![];
            let (trust_ir_expr, source_label): (SmtExpr, String) = match &source_op {
                SourceOp::Binary(op) => (
                    encode_trust_ir_binop(op, ty, sym1.clone(), sym2.clone()),
                    format!("{op:?}"),
                ),
                SourceOp::Bitwise(op) => (
                    encode_trust_ir_bitwise_binop(op, ty, sym1.clone(), sym2.clone()),
                    format!("{op:?}"),
                ),
                SourceOp::Shift(op) => {
                    // LOAD-BEARING precondition (#57): amount (src2) < width. In
                    // range the hardware mask is the identity; out of range the
                    // faithful (masked) machine side diverges from the clamp-to-0
                    // trust_ir side, so this precondition is genuinely required
                    // for the obligation to discharge Valid (not cosmetic).
                    preconditions.push(
                        sym2.clone()
                            .bvult(SmtExpr::bv_const(dst_width as u64, dst_width)),
                    );
                    (
                        encode_trust_ir_shift(op, ty, sym1.clone(), sym2.clone()),
                        format!("{op:?}"),
                    )
                }
                // Unary families never reach the Binary arm. The FP/div/madd
                // families are dispatched to dedicated builders ABOVE and never
                // reach here either.
                SourceOp::Neg
                | SourceOp::BitwiseShifted { .. }
                | SourceOp::RotateRightImmediate
                | SourceOp::Sextend { .. }
                | SourceOp::Uextend { .. }
                | SourceOp::IntDiv(_)
                | SourceOp::MulAdd { .. }
                | SourceOp::FpFma { .. }
                | SourceOp::FpBinary(_)
                | SourceOp::FpUnary(_)
                | SourceOp::FpToInt { .. }
                | SourceOp::IntToFp { .. }
                | SourceOp::FpFormatConvert { .. }
                | SourceOp::FmovImm => return None,
            };

            // MACHINE side: the REAL opcode's encoder, wired EXACTLY as emitted
            // (src1 -> rn, src2 -> rm, in operand order). For a non-commutative
            // op (Sub/Bic/Orn/shifts) a swap of the source slots changes the
            // result ⇒ refutes. Shifts use the FAITHFUL amount-masked encoder.
            let aarch64_expr = match inst.opcode {
                AArch64Opcode::AddRR | AArch64Opcode::AddRI => {
                    encode_add_rr(size, sym1.clone(), sym2.clone())
                }
                AArch64Opcode::SubRR | AArch64Opcode::SubRI => {
                    encode_sub_rr(size, sym1.clone(), sym2.clone())
                }
                AArch64Opcode::MulRR => encode_mul_rr(size, sym1.clone(), sym2.clone()),
                AArch64Opcode::AndRR | AArch64Opcode::AndRI => {
                    encode_and_rr(size, sym1.clone(), sym2.clone())
                }
                AArch64Opcode::OrrRR | AArch64Opcode::OrrRI => {
                    encode_orr_rr(size, sym1.clone(), sym2.clone())
                }
                AArch64Opcode::EorRR | AArch64Opcode::EorRI => {
                    encode_eor_rr(size, sym1.clone(), sym2.clone())
                }
                AArch64Opcode::BicRR => encode_bic_rr(size, sym1.clone(), sym2.clone()),
                AArch64Opcode::OrnRR => encode_orn_rr(size, sym1.clone(), sym2.clone()),
                AArch64Opcode::LslRR | AArch64Opcode::LslRI => {
                    encode_lsl_rr_masked(size, sym1.clone(), sym2.clone())
                }
                AArch64Opcode::LsrRR | AArch64Opcode::LsrRI => {
                    encode_lsr_rr_masked(size, sym1.clone(), sym2.clone())
                }
                AArch64Opcode::AsrRR | AArch64Opcode::AsrRI => {
                    encode_asr_rr_masked(size, sym1.clone(), sym2.clone())
                }
                // Unreachable: opcode_to_source_op only returned Binary for the
                // arms above. Fail closed rather than panic.
                _ => return None,
            };

            // Only register sources become declared SMT inputs; an immediate is a
            // constant and is NOT declared.
            let mut inputs = vec![("recon_src1".to_string(), dst_width)];
            if matches!(
                src2,
                MachOperand::VReg(_) | MachOperand::PReg(_) | MachOperand::Special(_)
            ) {
                inputs.push(("recon_src2".to_string(), dst_width));
            }

            Some(ProofObligation {
                name: format!(
                    "RECONSTRUCTED {}_{} -> {:?} (real-operand)",
                    source_label, dst_width, inst.opcode
                ),
                trust_ir_expr,
                aarch64_expr,
                inputs,
                preconditions,
                fp_inputs: vec![],
                category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
                machine_side_provenance: MachineSideProvenance::Reconstructed {
                    from_opcode,
                    arity: arity.as_u8(),
                },
            })
        }
        AluArity::Unary => {
            // Typed positional schema: [dst, src].
            if inst.operands.len() != 2 {
                return None;
            }
            let src = &inst.operands[1];
            let src_reg_width = operand_reg_width_bits(src)?;

            match &source_op {
                SourceOp::Neg => {
                    // Same-width unary: src register width must match dst width.
                    if src_reg_width != dst_width {
                        return None;
                    }
                    let sym = SmtExpr::var("recon_src", dst_width);
                    let trust_ir_expr = encode_trust_ir_neg(ty, sym.clone());
                    let aarch64_expr = match inst.opcode {
                        AArch64Opcode::Neg => encode_neg(size, sym.clone()),
                        _ => return None,
                    };
                    Some(ProofObligation {
                        name: format!(
                            "RECONSTRUCTED Ineg_{} -> {:?} (real-operand)",
                            dst_width, inst.opcode
                        ),
                        trust_ir_expr,
                        aarch64_expr,
                        inputs: vec![("recon_src".to_string(), dst_width)],
                        preconditions: vec![],
                        fp_inputs: vec![],
                        category: Some(
                            crate::lowering_proof::TransvalCheckKind::InstructionLowering,
                        ),
                        machine_side_provenance: MachineSideProvenance::Reconstructed {
                            from_opcode,
                            arity: arity.as_u8(),
                        },
                    })
                }
                SourceOp::Sextend { from_bits, to_bits } => {
                    reconstruct_extend(inst, *from_bits, *to_bits, true, from_opcode, arity)
                }
                SourceOp::Uextend { from_bits, to_bits } => {
                    reconstruct_extend(inst, *from_bits, *to_bits, false, from_opcode, arity)
                }
                // Binary families never reach the Unary arm. FP unary value ops
                // (Fneg/Fabs/Fsqrt/Frint*), conversions, and FmovImm are
                // dispatched ABOVE.
                SourceOp::Binary(_)
                | SourceOp::Bitwise(_)
                | SourceOp::BitwiseShifted { .. }
                | SourceOp::Shift(_)
                | SourceOp::RotateRightImmediate
                | SourceOp::IntDiv(_)
                | SourceOp::MulAdd { .. }
                | SourceOp::FpFma { .. }
                | SourceOp::FpBinary(_)
                | SourceOp::FpUnary(_)
                | SourceOp::FpToInt { .. }
                | SourceOp::IntToFp { .. }
                | SourceOp::FpFormatConvert { .. }
                | SourceOp::FmovImm => None,
            }
        }
        // Ternary (Madd/Msub) is dispatched to `reconstruct_mul_add` above and
        // never reaches the generic GPR logic. Fail closed.
        AluArity::Ternary => None,
    }
}

/// Reconstruct standalone `ROR Rd, Rn, #k` from its real three-operand form.
///
/// SOURCE is the frontend shift/OR rotate idiom. MACHINE directly decodes the
/// `EXTR Rd, Rn, Rn, #k` alias emitted by the code generator. The two formulas
/// are structurally distinct but equivalent; perturbing the EXTR amount or
/// either concatenated source refutes. Only W/X same-width GPRs and non-zero
/// in-range immediates receive authority. `#0` encodes as a move alias and must
/// not inherit this rotate proof.
fn reconstruct_ror_immediate(inst: &MachInst, from_opcode: String) -> Option<ProofObligation> {
    use crate::aarch64_semantics::{encode_ror_imm_extr, encode_ror_imm_source};

    if inst.opcode != AArch64Opcode::RorRI || inst.operands.len() != 3 {
        return None;
    }
    let dst_width = operand_plain_gpr_width_bits(inst.operands.first()?)?;
    let src_width = operand_plain_gpr_width_bits(inst.operands.get(1)?)?;
    if src_width != dst_width {
        return None;
    }
    let size = width_to_operand_size(dst_width)?;
    let MachOperand::Imm(amount) = inst.operands.get(2)? else {
        return None;
    };
    if *amount < 1 || *amount >= i64::from(dst_width) {
        return None;
    }
    let amount = *amount as u32;
    let src = SmtExpr::var("recon_src", dst_width);
    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED Ror_{} #{} -> {:?} (EXTR alias, real-operand)",
            dst_width, amount, inst.opcode
        ),
        trust_ir_expr: encode_ror_imm_source(size, src.clone(), amount),
        aarch64_expr: encode_ror_imm_extr(size, src, amount),
        inputs: vec![("recon_src".to_string(), dst_width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: AluArity::Unary.as_u8(),
        },
    })
}

/// Reconstruct `EOR Rd, Rn, Rm, LSL|LSR #k` from its real four-operand form.
///
/// The source side uses an independent power-of-two multiplication/division
/// identity for the shift, while the machine side uses the AArch64
/// shifted-register model. This keeps the obligation structurally non-degenerate
/// and makes a wrong amount or shift kind refutable. Operand widths, shift range,
/// and the opcode-to-kind mapping are checked before any authority is produced.
fn reconstruct_bitwise_shifted(
    inst: &MachInst,
    op: &trust_cg_lower::instructions::Opcode,
    kind: crate::aarch64_semantics::RegShiftKind,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::aarch64_semantics::{RegShiftKind, encode_eor_shifted_reg};
    use crate::trust_ir_semantics::encode_trust_ir_bitwise_binop;
    use trust_cg_lower::instructions::Opcode;

    if !matches!(op, Opcode::Bxor)
        || !matches!(
            (inst.opcode, kind),
            (AArch64Opcode::EorRRLsl, RegShiftKind::Lsl)
                | (AArch64Opcode::EorRRLsr, RegShiftKind::Lsr)
        )
        || inst.operands.len() != 4
    {
        return None;
    }

    let dst_width = operand_reg_width_bits(inst.operands.first()?)?;
    let size = width_to_operand_size(dst_width)?;
    let ty = crate::aarch64_semantics::operand_size_to_type(size);
    if operand_reg_width_bits(inst.operands.get(1)?)? != dst_width
        || operand_reg_width_bits(inst.operands.get(2)?)? != dst_width
    {
        return None;
    }
    let MachOperand::Imm(amount) = inst.operands.get(3)? else {
        return None;
    };
    if *amount < 1 || *amount >= i64::from(dst_width) {
        return None;
    }

    let rn = SmtExpr::var("recon_src1", dst_width);
    let rm = SmtExpr::var("recon_src2", dst_width);
    let power_of_two = SmtExpr::bv_const(1u64 << (*amount as u32), dst_width);
    let independently_shifted = match kind {
        RegShiftKind::Lsl => rm.clone().bvmul(power_of_two),
        RegShiftKind::Lsr => rm.clone().bvudiv(power_of_two),
        RegShiftKind::Asr | RegShiftKind::Ror => return None,
    };
    let trust_ir_expr = encode_trust_ir_bitwise_binop(op, ty, rn.clone(), independently_shifted);
    let aarch64_expr = encode_eor_shifted_reg(size, rn, rm, kind, *amount as u32);

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED Bxor_{} with {:?} #{} -> {:?} (real-operand)",
            dst_width, kind, amount, inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![
            ("recon_src1".to_string(), dst_width),
            ("recon_src2".to_string(), dst_width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: AluArity::Binary.as_u8(),
        },
    })
}

/// The immediate-baked binary/shift RI opcodes whose whole WIDTH family PROOF-5
/// covers with a single PARAMETRIC (free-immediate) rule. Their RR siblings
/// share the same machine encoder (`AddRI`/`AddRR` → `encode_add_rr`, etc.), so
/// the free-immediate obligation is byte-identical to the RR-form reconstruction
/// — one committed tier-0 row credits the RR instance AND every RI immediate.
const fn parametric_imm_register_opcode(op: AArch64Opcode) -> Option<AArch64Opcode> {
    use AArch64Opcode as A;
    match op {
        A::AddRI => Some(A::AddRR),
        A::SubRI => Some(A::SubRR),
        A::AndRI => Some(A::AndRR),
        A::OrrRI => Some(A::OrrRR),
        A::EorRI => Some(A::EorRR),
        A::LslRI => Some(A::LslRR),
        A::LsrRI => Some(A::LsrRR),
        A::AsrRI => Some(A::AsrRR),
        _ => None,
    }
}

/// PROOF-5 (aarch64): the CANONICAL (parametric) reconstruction obligation used
/// for the tier-0 verdict lookup. Mirrors the x86
/// `canonical_reconstruct_obligation`: the immediate-baked RI families have
/// their baked immediate FREED to a fresh same-width register (forall-imm; still
/// QF_BV; the shift `amount < width` precondition rides symbolically over the
/// free variable), and every immediate-free family is already stable per
/// (family, width) so its reconstruction is its canonical form. Drift-free: goes
/// through the SAME [`reconstruct_alu_obligation`].
pub(crate) fn canonical_reconstruct_obligation(inst: &MachInst) -> Option<ProofObligation> {
    // Validate the actual instruction before constructing a family theorem.
    // Canonicalization must not turn a refused operand shape into valid input.
    let instance = reconstruct_alu_obligation(inst)?;
    if let Some(register_opcode) = parametric_imm_register_opcode(inst.opcode) {
        use trust_cg_ir::RegClass;
        use trust_cg_ir::regs::VReg;
        let dst_width = operand_reg_width_bits(inst.operands.first()?)?;
        let class = match dst_width {
            32 => RegClass::Gpr32,
            64 => RegClass::Gpr64,
            _ => return Some(instance),
        };
        let mut synth = inst.clone();
        // The symbolic amount is a register operand, so use its RR sibling.
        // An RI opcode with this operand is malformed and correctly refused.
        synth.opcode = register_opcode;
        synth.operands[2] = MachOperand::VReg(VReg::new(u32::MAX, class));
        return reconstruct_alu_obligation(&synth).or(Some(instance));
    }
    Some(instance)
}

/// PROOF-5 (aarch64): the finite set of CANONICAL (parametric) reconstruction
/// obligations to prove offline into tier-0 — the integer ALU / bitwise / shift
/// / neg surface at both emitted GPR widths (W=32, X=64). RI instances
/// canonicalize to the byte-identical RR-form obligation, so one row is the
/// parametric proof for the whole width family. FP / division / madd families
/// are left to the per-compile live-solver credit (division stays a tracked
/// statistical-fallback exemption).
pub fn enumerate_reconstruct_tier0_obligations() -> Vec<ProofObligation> {
    use trust_cg_ir::RegClass;
    use trust_cg_ir::regs::VReg;
    let mut out: Vec<ProofObligation> = Vec::new();
    let add = |inst: MachInst, out: &mut Vec<ProofObligation>| {
        if let Some(ob) = reconstruct_alu_obligation(&inst)
            && !out.iter().any(|x| x == &ob)
        {
            out.push(ob);
        }
    };
    for &class in &[RegClass::Gpr32, RegClass::Gpr64] {
        let r = |id: u32| MachOperand::VReg(VReg::new(id, class));
        // Binary register ALU / bitwise: [dst, src1, src2].
        for op in [
            AArch64Opcode::AddRR,
            AArch64Opcode::SubRR,
            AArch64Opcode::MulRR,
            AArch64Opcode::AndRR,
            AArch64Opcode::OrrRR,
            AArch64Opcode::EorRR,
            AArch64Opcode::BicRR,
            AArch64Opcode::OrnRR,
        ] {
            add(MachInst::new(op, vec![r(0), r(1), r(2)]), &mut out);
        }
        // Shifts RR: [dst, src1, src2] (amount in a register; amount<width precond).
        for op in [
            AArch64Opcode::LslRR,
            AArch64Opcode::LsrRR,
            AArch64Opcode::AsrRR,
        ] {
            add(MachInst::new(op, vec![r(0), r(1), r(2)]), &mut out);
        }
        // Unary Neg: [dst, src].
        add(
            MachInst::new(AArch64Opcode::Neg, vec![r(0), r(1)]),
            &mut out,
        );
    }
    // Width-fixed immediate-free sign/zero extends (one representative each; the
    // source/dest widths are fixed by the opcode).
    for op in [
        AArch64Opcode::Sxtw,
        AArch64Opcode::Uxtw,
        AArch64Opcode::Sxtb,
        AArch64Opcode::Sxth,
        AArch64Opcode::Uxtb,
        AArch64Opcode::Uxth,
    ] {
        if let Some(inst) = representative_reconstructable_inst(op) {
            add(inst, &mut out);
        }
    }
    out
}

/// Reconstruct an integer DIVIDE obligation (`SDIV`/`UDIV`) from the real
/// emitted instruction, with a LOAD-BEARING `divisor != 0` precondition.
///
/// Schema: `[dst, rn, rm]` (rn = dividend, rm = divisor). The source side is
/// `encode_trust_ir_binop(Sdiv|Udiv, ...)` (= `bvsdiv`/`bvudiv`); the machine
/// side is `encode_sdiv_rr`/`encode_udiv_rr` wired EXACTLY as emitted.
///
/// trust-ir defines division-by-zero as UNDEFINED BEHAVIOR (scoped out here), so
/// the obligation is guarded by `rm != 0`. That precondition is LOAD-BEARING:
/// the SMT evaluator returns a sentinel `0` for `bv*div` by zero on BOTH sides,
/// so they would *spuriously* agree at `rm == 0`; but soundness must NOT claim
/// the divide is correct in the UB region. More importantly, with the precond
/// PRESENT the obligation discharges Valid only over the DEFINED region; if a
/// future change made the two sides diverge at `rm == 0`, stripping the precond
/// would surface that — the refutation test `sdiv_divzero_precondition_is_load_bearing`
/// asserts the precond is required.
///
/// SDIV-for-UDIV (or swapped wiring) diverges on negative operands ⇒ REFUTE.
fn reconstruct_int_div(
    inst: &MachInst,
    op: &trust_cg_lower::instructions::Opcode,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::aarch64_semantics::{encode_sdiv_rr, encode_udiv_rr};
    use crate::trust_ir_semantics::encode_trust_ir_binop;

    if inst.operands.len() != 3 {
        return None;
    }
    let dst = inst.operands.first()?;
    let dst_width = operand_reg_width_bits(dst)?;
    let size = width_to_operand_size(dst_width)?;
    let ty = crate::aarch64_semantics::operand_size_to_type(size);

    let rn = &inst.operands[1];
    let rm = &inst.operands[2];
    if operand_reg_width_bits(rn)? != dst_width || operand_reg_width_bits(rm)? != dst_width {
        return None;
    }

    let sym1 = SmtExpr::var("recon_src1", dst_width);
    let sym2 = SmtExpr::var("recon_src2", dst_width);

    let trust_ir_expr = encode_trust_ir_binop(op, ty, sym1.clone(), sym2.clone());
    let aarch64_expr = match inst.opcode {
        AArch64Opcode::SDiv => encode_sdiv_rr(size, sym1.clone(), sym2.clone()),
        AArch64Opcode::UDiv => encode_udiv_rr(size, sym1.clone(), sym2.clone()),
        _ => return None,
    };

    // LOAD-BEARING precondition: divisor != 0 (div-by-zero is trust-ir UB).
    let divisor_nonzero = sym2
        .clone()
        .eq_expr(SmtExpr::bv_const(0, dst_width))
        .not_expr();

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED {op:?}_{dst_width} -> {:?} (real-operand, divisor!=0)",
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![
            ("recon_src1".to_string(), dst_width),
            ("recon_src2".to_string(), dst_width),
        ],
        preconditions: vec![divisor_nonzero],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: AluArity::Binary.as_u8(),
        },
    })
}

/// Reconstruct a FUSED multiply-add (`MADD`) / multiply-subtract (`MSUB`)
/// obligation from the real emitted instruction.
///
/// Ternary schema: `[dst, rn, rm, ra]`. MADD computes `Rd = Ra + Rn*Rm`; MSUB
/// computes `Rd = Ra - Rn*Rm`. There is NO single trust_ir opcode for these:
/// the SOURCE is the COMPOUND expression
///   * MADD: `Iadd(Imul(rn, rm), ra)`  (= `a*b + c`)
///   * MSUB: `Isub(ra, Imul(rn, rm))`  (= `c - a*b`)
///     built from the integer `Imul`/`Iadd`/`Isub` encoders over the shared syms.
///     The machine side is `encode_madd_rr`/`encode_msub_rr` wired EXACTLY as
///     emitted. A wrong fused op (MADD↔MSUB) flips the `+`/`-`, and a wrong operand
///     wiring (e.g. `ra` and `rn` swapped) changes the value ⇒ REFUTE.
fn reconstruct_mul_add(inst: &MachInst, sub: bool, from_opcode: String) -> Option<ProofObligation> {
    use crate::aarch64_semantics::{encode_madd_rr, encode_msub_rr};
    use crate::trust_ir_semantics::encode_trust_ir_binop;
    use trust_cg_lower::instructions::Opcode;

    // Ternary positional schema: [dst, rn, rm, ra].
    if inst.operands.len() != 4 {
        return None;
    }
    let dst = inst.operands.first()?;
    let dst_width = operand_reg_width_bits(dst)?;
    let size = width_to_operand_size(dst_width)?;
    let ty = crate::aarch64_semantics::operand_size_to_type(size);

    let rn = &inst.operands[1];
    let rm = &inst.operands[2];
    let ra = &inst.operands[3];
    if operand_reg_width_bits(rn)? != dst_width
        || operand_reg_width_bits(rm)? != dst_width
        || operand_reg_width_bits(ra)? != dst_width
    {
        return None;
    }

    let sn = SmtExpr::var("recon_rn", dst_width);
    let sm = SmtExpr::var("recon_rm", dst_width);
    let sa = SmtExpr::var("recon_ra", dst_width);

    // COMPOUND source: a*b+c (MADD) / c-a*b (MSUB).
    let prod = encode_trust_ir_binop(&Opcode::Imul, ty.clone(), sn.clone(), sm.clone());
    let trust_ir_expr = if sub {
        encode_trust_ir_binop(&Opcode::Isub, ty.clone(), sa.clone(), prod)
    } else {
        encode_trust_ir_binop(&Opcode::Iadd, ty.clone(), prod, sa.clone())
    };

    let aarch64_expr = match inst.opcode {
        AArch64Opcode::Madd => encode_madd_rr(size, sn.clone(), sm.clone(), sa.clone()),
        AArch64Opcode::Msub => encode_msub_rr(size, sn.clone(), sm.clone(), sa.clone()),
        _ => return None,
    };

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED {}_{dst_width} -> {:?} (real-operand, ternary a*b{}c)",
            if sub { "Msub" } else { "Madd" },
            inst.opcode,
            if sub { "-" } else { "+" }
        ),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![
            ("recon_rn".to_string(), dst_width),
            ("recon_rm".to_string(), dst_width),
            ("recon_ra".to_string(), dst_width),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: AluArity::Ternary.as_u8(),
        },
    })
}

/// Reconstruct a binary FP value op (`FADD`/`FSUB`/`FMUL`/`FDIV`) from the real
/// emitted instruction.
///
/// Schema: `[dst, rn, rm]`, all FP registers; the FP width (F32/F64) is taken
/// from the FP register class (Sd→F32, Dd→F64). The operands are bound to
/// DISTINCT NAMED FP leaves (`recon_a`/`recon_b`) so the wiring-preserving FP
/// evaluator (`verify_fp_reconstructed_by_evaluation`) can refute a swapped
/// non-commutative op (FSUB/FDIV). The source side is `encode_trust_ir_fp_binop`
/// and the machine side is `encode_f{add,sub,mul,div}_rr`, both RNE-rounded. A
/// wrong FP opcode (FADD↔FSUB) refutes; FADD/FMUL are commutative so a swap does
/// NOT refute (documented).
fn reconstruct_fp_binary(
    inst: &MachInst,
    op: &trust_cg_lower::instructions::Opcode,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::aarch64_semantics::{
        FPSize, encode_fadd_rr, encode_fdiv_rr, encode_fmaxnm_rr, encode_fminnm_rr, encode_fmul_rr,
        encode_fsub_rr,
    };
    use crate::trust_ir_semantics::encode_trust_ir_fp_binop;

    if inst.operands.len() != 3 {
        return None;
    }
    let dst = inst.operands.first()?;
    let rn = &inst.operands[1];
    let rm = &inst.operands[2];
    if !operand_is_fp_reg(dst) || !operand_is_fp_reg(rn) || !operand_is_fp_reg(rm) {
        return None;
    }
    let dst_width = operand_reg_width_bits(dst)?;
    if operand_reg_width_bits(rn)? != dst_width || operand_reg_width_bits(rm)? != dst_width {
        return None;
    }
    let (eb, sb, fpsize): (u32, u32, FPSize) = fp_format_from_width(dst_width)?;
    let ty = if dst_width == 32 {
        trust_cg_lower::types::Type::F32
    } else {
        trust_cg_lower::types::Type::F64
    };

    let a = SmtExpr::var("recon_a", dst_width);
    let b = SmtExpr::var("recon_b", dst_width);

    let trust_ir_expr = encode_trust_ir_fp_binop(op, ty, a.clone(), b.clone());
    let aarch64_expr = match inst.opcode {
        AArch64Opcode::FaddRR => encode_fadd_rr(fpsize, a.clone(), b.clone()),
        AArch64Opcode::FsubRR => encode_fsub_rr(fpsize, a.clone(), b.clone()),
        AArch64Opcode::FmulRR => encode_fmul_rr(fpsize, a.clone(), b.clone()),
        AArch64Opcode::FdivRR => encode_fdiv_rr(fpsize, a.clone(), b.clone()),
        AArch64Opcode::FminnmRR => encode_fminnm_rr(fpsize, a.clone(), b.clone()),
        AArch64Opcode::FmaxnmRR => encode_fmaxnm_rr(fpsize, a.clone(), b.clone()),
        _ => return None,
    };

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED {op:?}_F{dst_width} -> {:?} (real-operand)",
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![
            ("recon_a".to_string(), eb, sb),
            ("recon_b".to_string(), eb, sb),
        ],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: AluArity::Binary.as_u8(),
        },
    })
}

/// Reconstruct a scalar FUSED FP multiply-add (`FMADD`) from the real emitted
/// instruction.
///
/// Schema: `[dst, rn, rm, ra]`, all FP registers; the FP width (F32/F64) is
/// taken from the FP register class. Operands bind to DISTINCT NAMED FP leaves
/// (`recon_a`/`recon_b`/`recon_c`) so the wiring-preserving ternary FP evaluator
/// can refute a swapped operand. BOTH sides are the SINGLE-ROUNDING `fp.fma`
/// (`round_RNE(a*b + c)` with ONE rounding) over the shared bit-model: source =
/// `a*b+c`, machine = `encode_fmadd_rr`. HONESTY: like the other FP proofs this
/// is lane-plumbing / op-selection over the shared fp_bitmodel + silicon bridge,
/// NOT a symbolic FP proof. The refute controls (a round-TWICE unfused
/// `fp_add(fp_mul(a,b),c)` and a sign-flipped `FMSUB` machine model) live in the
/// dedicated negative-control test and diverge on a round-once-vs-twice triple.
fn reconstruct_fp_fma(inst: &MachInst, sub: bool, from_opcode: String) -> Option<ProofObligation> {
    use crate::aarch64_semantics::{FPSize, encode_fmadd_rr};

    if inst.operands.len() != 4 {
        return None;
    }
    let dst = inst.operands.first()?;
    let rn = &inst.operands[1];
    let rm = &inst.operands[2];
    let ra = &inst.operands[3];
    if !operand_is_fp_reg(dst)
        || !operand_is_fp_reg(rn)
        || !operand_is_fp_reg(rm)
        || !operand_is_fp_reg(ra)
    {
        return None;
    }
    let dst_width = operand_reg_width_bits(dst)?;
    if operand_reg_width_bits(rn)? != dst_width
        || operand_reg_width_bits(rm)? != dst_width
        || operand_reg_width_bits(ra)? != dst_width
    {
        return None;
    }
    let (eb, sb, fpsize): (u32, u32, FPSize) = fp_format_from_width(dst_width)?;

    let a = SmtExpr::var("recon_a", dst_width);
    let b = SmtExpr::var("recon_b", dst_width);
    let c = SmtExpr::var("recon_c", dst_width);

    // Source side: the SINGLE-ROUNDING fused `a*b + c` (FMADD) / `c - a*b`
    // (FMSUB, via `-a * b + c`). FMSUB is not emitted today (fail-closed at the
    // opcode level) but the builder stays honest for both forms.
    use crate::smt::RoundingMode;
    let trust_ir_expr = if sub {
        SmtExpr::fp_fma(RoundingMode::RNE, a.clone().fp_neg(), b.clone(), c.clone())
    } else {
        SmtExpr::fp_fma(RoundingMode::RNE, a.clone(), b.clone(), c.clone())
    };
    let aarch64_expr = match inst.opcode {
        AArch64Opcode::FmaddRR => encode_fmadd_rr(fpsize, a.clone(), b.clone(), c.clone()),
        _ => return None,
    };

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED FMADD_F{dst_width} -> {:?} (real-operand, ternary a*b+c)",
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![
            ("recon_a".to_string(), eb, sb),
            ("recon_b".to_string(), eb, sb),
            ("recon_c".to_string(), eb, sb),
        ],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: AluArity::Ternary.as_u8(),
        },
    })
}

/// Reconstruct a unary FP value op (`FNEG`/`FABS`/`FSQRT`) from the real emitted
/// instruction. Schema: `[dst, rn]`, FP registers; width from the FP reg class.
///
/// Source = `encode_trust_ir_fp_unaryop`, machine = `encode_fneg`/`encode_fabs`/
/// `encode_fsqrt`/`encode_frint{m,p,z}`. A wrong unary op (FNEG-as-FABS, or a
/// wrong rounding direction FRINTM-as-FRINTP) diverges on a discriminating input
/// (a negative / non-integral value) ⇒ REFUTE.
fn reconstruct_fp_unary(
    inst: &MachInst,
    op: &trust_cg_lower::instructions::Opcode,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::aarch64_semantics::{
        FPSize, encode_fabs, encode_fneg, encode_frintm, encode_frintp, encode_frintz, encode_fsqrt,
    };
    use crate::trust_ir_semantics::try_encode_trust_ir_fp_unaryop;

    if inst.operands.len() != 2 {
        return None;
    }
    let dst = inst.operands.first()?;
    let rn = &inst.operands[1];
    if !operand_is_fp_reg(dst) || !operand_is_fp_reg(rn) {
        return None;
    }
    let dst_width = operand_reg_width_bits(dst)?;
    if operand_reg_width_bits(rn)? != dst_width {
        return None;
    }
    let (eb, sb, fpsize): (u32, u32, FPSize) = fp_format_from_width(dst_width)?;
    let ty = if dst_width == 32 {
        trust_cg_lower::types::Type::F32
    } else {
        trust_cg_lower::types::Type::F64
    };

    let a = SmtExpr::var("recon_a", dst_width);

    let trust_ir_expr = try_encode_trust_ir_fp_unaryop(op, ty, a.clone()).ok()?;
    let aarch64_expr = match inst.opcode {
        AArch64Opcode::FnegRR => encode_fneg(fpsize, a.clone()),
        AArch64Opcode::FabsRR => encode_fabs(fpsize, a.clone()),
        AArch64Opcode::FsqrtRR => encode_fsqrt(fpsize, a.clone()),
        AArch64Opcode::FrintmRR => encode_frintm(fpsize, a.clone()),
        AArch64Opcode::FrintpRR => encode_frintp(fpsize, a.clone()),
        AArch64Opcode::FrintzRR => encode_frintz(fpsize, a.clone()),
        _ => return None,
    };

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED {op:?}_F{dst_width} -> {:?} (real-operand)",
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("recon_a".to_string(), eb, sb)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: AluArity::Unary.as_u8(),
        },
    })
}

/// Reconstruct a scalar `FMOV`-IMMEDIATE constant materialization from the real
/// emitted instruction. Schema: `[dst(FP), FImm(value)]`.
///
/// This is an ENCODING obligation, NOT a runtime value op:
///   - trust_ir side = the named constant's IEEE-754 bit pattern at the
///     destination format (`Sd` → binary32, `Dd` → binary64);
///   - machine side  = the hardware `VFPExpandImm` DECODE (a structural
///     extract/shift/or assembly, [`encode_fmov_imm_bits`]) of the 8-bit field
///     the codegen encoder picks ([`fmov_imm8_field`]).
///
/// The obligation is thus `assemble(encode(v)) == bits(v)` — a real encoding
/// round-trip whose machine side is a structural bit-assembly (a wrong field
/// formula or wrong bit placement REFUTES), NOT the degenerate `const == const`
/// that re-stating `bits(v)` on both sides would be. The value has no runtime
/// freedom, so a single phantom FP leaf (absent from both sides) routes it to
/// the reconstruction FP evaluator, which compares the two assembled constants
/// across its battery. Fails closed (returns `None`) for a non-FMOV-encodable
/// value — the ISel never emits `FmovImm` in that case (it materializes the bits
/// in a GPR and `FMOV`s them across instead).
fn reconstruct_fmov_imm(inst: &MachInst, from_opcode: String) -> Option<ProofObligation> {
    use crate::aarch64_semantics::{encode_fmov_imm_bits, fmov_imm8_field};

    if inst.operands.len() != 2 {
        return None;
    }
    let dst = inst.operands.first()?;
    if !operand_is_fp_reg(dst) {
        return None;
    }
    let dst_width = operand_reg_width_bits(dst)?;
    if dst_width != 32 && dst_width != 64 {
        return None;
    }
    let value = match &inst.operands[1] {
        MachOperand::FImm(v) => *v,
        _ => return None,
    };
    // The exact 8-bit field the codegen encoder selects; fail-closed if the
    // value is not FMOV-encodable (the ISel would not have emitted FmovImm).
    let field = fmov_imm8_field(value)?;
    let (eb, sb) = if dst_width == 32 {
        (8u32, 24u32)
    } else {
        (11u32, 53u32)
    };
    // trust_ir: the constant's IEEE bit pattern at the destination format. For a
    // single-precision destination the value is the f64 widening of the f32
    // literal (the ISel passes it as f64), so narrow it back to binary32 bits.
    let value_bits = if dst_width == 32 {
        u64::from((value as f32).to_bits())
    } else {
        value.to_bits()
    };
    let trust_ir_expr = SmtExpr::bv_const(value_bits, dst_width);
    let aarch64_expr = encode_fmov_imm_bits(field, dst_width);

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED FmovImm_F{dst_width} (#{value}) -> VFPExpandImm(0x{field:02x})"
        ),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![],
        preconditions: vec![],
        // Phantom FP leaf (absent from both sides): the obligation is a closed
        // constant equality, so substitution is a no-op and the verdict is the
        // genuine `assemble(encode(v)) == bits(v)`.
        fp_inputs: vec![("recon_a".to_string(), eb, sb)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: AluArity::Unary.as_u8(),
        },
    })
}

/// Reconstruct an FP→INT conversion (`FCVTZS`/`FCVTZU`, round toward zero) from
/// the real emitted instruction. Schema: `[dst, rn]` where `dst` is a GPR (the
/// integer result) and `rn` is an FP register (the source). The integer width
/// comes from the GPR destination; the FP source format from the FP reg class.
///
/// Source = `encode_trust_ir_fcvt_to_sint`/`_uint`; machine = `encode_fcvtzs`/
/// `encode_fcvtzu`, both RTZ. FCVTZS-for-FCVTZU diverges on a negative input ⇒
/// REFUTE. The single FP operand carries no wiring ambiguity (unary).
fn reconstruct_fp_to_int(
    inst: &MachInst,
    signed: bool,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::aarch64_semantics::{encode_fcvtzs, encode_fcvtzu};
    use crate::trust_ir_semantics::{encode_trust_ir_fcvt_to_sint, encode_trust_ir_fcvt_to_uint};

    if inst.operands.len() != 2 {
        return None;
    }
    let dst = inst.operands.first()?;
    let rn = &inst.operands[1];
    // dst is the INTEGER result (GPR); rn is the FP source.
    if operand_is_fp_reg(dst) || !operand_is_fp_reg(rn) {
        return None;
    }
    let int_width = operand_reg_width_bits(dst)?;
    let fp_width = operand_reg_width_bits(rn)?;
    let (eb, sb, _fpsize) = fp_format_from_width(fp_width)?;
    if int_width != 32 && int_width != 64 {
        return None;
    }

    let a = SmtExpr::var("recon_a", fp_width);

    let trust_ir_expr = if signed {
        encode_trust_ir_fcvt_to_sint(int_width, a.clone())
    } else {
        encode_trust_ir_fcvt_to_uint(int_width, a.clone())
    };
    let aarch64_expr = match inst.opcode {
        AArch64Opcode::FcvtzsRR => encode_fcvtzs(int_width, a.clone()),
        AArch64Opcode::FcvtzuRR => encode_fcvtzu(int_width, a.clone()),
        _ => return None,
    };

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED Fcvt{}_I{int_width}_F{fp_width} -> {:?} (real-operand)",
            if signed { "ToInt" } else { "ToUint" },
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("recon_a".to_string(), eb, sb)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: AluArity::Unary.as_u8(),
        },
    })
}

/// Reconstruct an INT→FP conversion (`SCVTF`/`UCVTF`, round-to-nearest-even) from
/// the real emitted instruction. Schema: `[dst, rn]` where `dst` is an FP
/// register (the result) and `rn` is a GPR (the integer source).
///
/// The source operand is a bitvector, so the obligation carries it in `inputs`
/// (NOT `fp_inputs`) and is verified through the standard by-name BV evaluator —
/// which preserves the (single) operand and reasons over the real integer range.
/// Source = `encode_trust_ir_fcvt_from_sint`/`_uint`; machine = `encode_scvtf`/
/// `encode_ucvtf`. SCVTF and UCVTF use the same `BvToFP` node, so they are
/// distinguished by the source side's handling of the sign bit: the UNSIGNED
/// form zero-extends the operand on BOTH sides, while the SIGNED form does not —
/// an SCVTF-for-UCVTF mismatch diverges for an MSB-set input ⇒ REFUTE.
fn reconstruct_int_to_fp(
    inst: &MachInst,
    signed: bool,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::aarch64_semantics::{encode_scvtf, encode_ucvtf};
    use crate::trust_ir_semantics::{
        encode_trust_ir_fcvt_from_sint, encode_trust_ir_fcvt_from_uint,
    };

    if inst.operands.len() != 2 {
        return None;
    }
    let dst = inst.operands.first()?;
    let rn = &inst.operands[1];
    // dst is the FP result; rn is the INTEGER source (GPR).
    if !operand_is_fp_reg(dst) || operand_is_fp_reg(rn) {
        return None;
    }
    let fp_width = operand_reg_width_bits(dst)?;
    let int_width = operand_reg_width_bits(rn)?;
    let (eb, sb, _fpsize) = fp_format_from_width(fp_width)?;
    if int_width != 32 && int_width != 64 {
        return None;
    }

    let a = SmtExpr::var("recon_src", int_width);

    // For the UNSIGNED form the operand must be zero-extended on BOTH sides so
    // the shared `BvToFP` (which interprets its operand as SIGNED) computes the
    // unsigned value. The machine encoder takes the SAME zero-extended operand.
    let (trust_ir_operand, machine_operand): (SmtExpr, SmtExpr) = if signed {
        (a.clone(), a.clone())
    } else {
        let zext = SmtExpr::ZeroExtend {
            operand: Arc::new(a.clone()),
            extra_bits: int_width,
            width: int_width * 2,
        };
        (zext.clone(), zext)
    };

    let trust_ir_expr = if signed {
        encode_trust_ir_fcvt_from_sint(eb, sb, trust_ir_operand)
    } else {
        // The source-side encoder zero-extends internally; pass the RAW operand
        // so the two sides are built from the SAME public encoders. We already
        // zero-extended `machine_operand`, so call the machine encoder on it.
        encode_trust_ir_fcvt_from_uint(eb, sb, a.clone(), int_width)
    };
    let aarch64_expr = match inst.opcode {
        AArch64Opcode::ScvtfRR => encode_scvtf(eb, sb, machine_operand),
        AArch64Opcode::UcvtfRR => encode_ucvtf(eb, sb, machine_operand),
        _ => return None,
    };

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED Fcvt{}_F{fp_width}_I{int_width} -> {:?} (real-operand)",
            if signed { "FromInt" } else { "FromUint" },
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![("recon_src".to_string(), int_width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: AluArity::Unary.as_u8(),
        },
    })
}

/// Reconstruct an FP-FORMAT conversion (`FCVT Dd,Sn` widen / `FCVT Ss,Dn` narrow)
/// from the real emitted instruction. Schema: `[dst, rn]` where BOTH `dst` and
/// `rn` are FP registers of DIFFERING widths (the cast changes precision).
///
/// The single FP source is bound to a `from_bits`-wide named FP leaf (`recon_a`)
/// carried in `fp_inputs`, so the obligation is verified through the
/// WIRING-PRESERVING FP evaluator (`verify_fp_reconstructed_by_evaluation`),
/// which substitutes the same concrete FP value into BOTH sides. Source =
/// `encode_trust_ir_fp_format_convert(to_eb, to_sb, recon_a)` (keyed on the
/// DESTINATION format); machine = `encode_fcvt_sd` (widen) / `encode_fcvt_ds`
/// (narrow). The conversion DIRECTION is encoded entirely by the destination
/// format: an `FcvtSD`-for-`FcvtDS` (wrong-direction) mismatch produces a
/// different destination format and DIVERGES for a value that does not round-trip
/// through binary32 ⇒ REFUTE. The single FP operand carries no wiring ambiguity
/// (unary).
fn reconstruct_fp_format_convert(
    inst: &MachInst,
    from_bits: u32,
    to_bits: u32,
    from_opcode: String,
) -> Option<ProofObligation> {
    use crate::aarch64_semantics::{encode_fcvt_ds, encode_fcvt_sd};
    use crate::trust_ir_semantics::encode_trust_ir_fp_format_convert;

    if inst.operands.len() != 2 {
        return None;
    }
    let dst = inst.operands.first()?;
    let rn = &inst.operands[1];
    // BOTH operands are FP registers; the cast changes precision (widths differ).
    if !operand_is_fp_reg(dst) || !operand_is_fp_reg(rn) {
        return None;
    }
    let dst_width = operand_reg_width_bits(dst)?;
    let src_width = operand_reg_width_bits(rn)?;
    // The emitted instruction must match the typed schema EXACTLY (fail-closed).
    if dst_width != to_bits || src_width != from_bits || from_bits == to_bits {
        return None;
    }
    // Source format `(eb, sb)` for the from_bits-wide FP leaf; destination format
    // `(to_eb, to_sb)` for the cast target.
    let (src_eb, src_sb, _src_fpsize) = fp_format_from_width(from_bits)?;
    let (to_eb, to_sb, _to_fpsize) = fp_format_from_width(to_bits)?;

    // Single FP source leaf, named `recon_a` so the wiring-preserving FP
    // evaluator substitutes it into BOTH sides.
    let a = SmtExpr::var("recon_a", from_bits);

    let trust_ir_expr = encode_trust_ir_fp_format_convert(to_eb, to_sb, a.clone());
    let aarch64_expr = match inst.opcode {
        AArch64Opcode::FcvtSD => encode_fcvt_sd(a.clone()),
        AArch64Opcode::FcvtDS => encode_fcvt_ds(a.clone()),
        _ => return None,
    };

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED {}_F{from_bits}_to_F{to_bits} -> {:?} (real-operand)",
            if to_bits > from_bits {
                "Fpromote"
            } else {
                "Fdemote"
            },
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("recon_a".to_string(), src_eb, src_sb)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: AluArity::Unary.as_u8(),
        },
    })
}

/// Reconstruct a width-CHANGING extend obligation (`SXTB`/`SXTH`/`SXTW` or
/// `UXTB`/`UXTH`/`UXTW`) from the real emitted instruction.
///
/// The source value occupies the low `from_bits` of its register; we model it as
/// a `from_bits`-wide fresh symbol so the obligation reasons over exactly the
/// bits the extend reads. The trust_ir side
/// (`encode_trust_ir_sextend`/`uextend`) and the AArch64 side
/// (`encode_sxt`/`encode_uxt`) both extend that `from_bits`-wide symbol to the
/// `to_bits`-wide destination. They agree IFF isel chose the right sign/zero
/// extension of the right source width: a UXT-for-Sextend (or vice versa) yields
/// a different result for a negative source ⇒ REFUTE.
fn reconstruct_extend(
    inst: &MachInst,
    from_bits: u32,
    to_bits: u32,
    signed: bool,
    from_opcode: String,
    arity: AluArity,
) -> Option<ProofObligation> {
    use crate::aarch64_semantics::{encode_sxt, encode_uxt};
    use crate::trust_ir_semantics::{encode_trust_ir_sextend, encode_trust_ir_uextend};

    // Destination register must be the to_bits width (W for 32-bit, X for 64).
    let dst = inst.operands.first()?;
    if operand_reg_width_bits(dst)? != to_bits {
        return None;
    }
    // Source register must hold at least the from_bits source value; the
    // architectural register width is >= from_bits (e.g. SXTB reads a W reg).
    let src = &inst.operands[1];
    let src_reg_width = operand_reg_width_bits(src)?;
    if src_reg_width < from_bits {
        return None;
    }

    // Model the source as a from_bits-wide symbol (the bits the extend reads).
    let sym = SmtExpr::var("recon_src", from_bits);
    let trust_ir_expr = if signed {
        encode_trust_ir_sextend(from_bits, to_bits, sym.clone())
    } else {
        encode_trust_ir_uextend(from_bits, to_bits, sym.clone())
    };
    let aarch64_expr = if signed {
        encode_sxt(from_bits, to_bits, sym.clone())
    } else {
        encode_uxt(from_bits, to_bits, sym.clone())
    };

    Some(ProofObligation {
        name: format!(
            "RECONSTRUCTED {}extend_{}_to_{} -> {:?} (real-operand)",
            if signed { "S" } else { "U" },
            from_bits,
            to_bits,
            inst.opcode
        ),
        trust_ir_expr,
        aarch64_expr,
        inputs: vec![("recon_src".to_string(), from_bits)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode,
            arity: arity.as_u8(),
        },
    })
}

/// Build a REPRESENTATIVE `MachInst` for a reconstructable AArch64 opcode, with
/// fresh virtual-register operands wired in the typed positional schema the
/// reconstructor expects. Returns `None` for any opcode not in
/// [`opcode_to_source_op`].
///
/// This is the opcode-complete entry point the COVERAGE GATE uses (task #63 Step
/// 4): the gate has only an opcode (no instruction), so it synthesizes a
/// representative instance, reconstructs the obligation from it, and credits the
/// opcode COVERED iff that obligation discharges `Valid`. The representative is
/// the GENERIC register form of the opcode (no immediates, no zero-register
/// aliasing), so it exercises the same source-op-vs-real-opcode equivalence the
/// per-instruction walk would for the common case.
///
/// All widths are 32-bit (`Gpr32`) except `Sxtw`/`Uxtw`, which are 32->64 and so
/// take a 64-bit destination; the extends read a narrower source from a `Gpr32`
/// (`Sxtb`/`Sxth`/`Uxtb`/`Uxth`) or `Gpr32`->`Gpr64` (`Sxtw`/`Uxtw`).
pub fn representative_reconstructable_inst(opcode: AArch64Opcode) -> Option<MachInst> {
    use trust_cg_ir::RegClass;
    use trust_cg_ir::regs::VReg;

    // Only opcodes the reconstructor handles get a representative instance.
    let (_, arity, _) = opcode_to_source_op(opcode)?;

    let w = |id: u32| MachOperand::VReg(VReg::new(id, RegClass::Gpr32));
    let x = |id: u32| MachOperand::VReg(VReg::new(id, RegClass::Gpr64));
    // S registers (Fpr32) are the representative FP width (F32) — same width as
    // a W reg, so the per-family width logic is identical to the 32-bit GPR case.
    let s = |id: u32| MachOperand::VReg(VReg::new(id, RegClass::Fpr32));
    // D registers (Fpr64) are the F64 width — used for the FP-format casts where
    // one operand is single (S) and the other double (D).
    let d = |id: u32| MachOperand::VReg(VReg::new(id, RegClass::Fpr64));

    let operands = match opcode {
        // Extends: dst width differs from source. Sxtw/Uxtw widen W -> X.
        AArch64Opcode::Sxtw | AArch64Opcode::Uxtw => vec![x(0), w(1)],
        AArch64Opcode::Sxtb | AArch64Opcode::Sxth | AArch64Opcode::Uxtb | AArch64Opcode::Uxth => {
            vec![w(0), w(1)]
        }

        // FUSED multiply-add/sub: ternary [dst, rn, rm, ra], all GPR.
        AArch64Opcode::Madd | AArch64Opcode::Msub => vec![w(0), w(1), w(2), w(3)],

        // FP binary value ops: [dst, rn, rm], all S (F32) registers.
        // FMAXNM/FMINNM are here too: `opcode_to_source_op` maps them to
        // `FpBinary(Fmax/Fmin)`, and without this arm they would fall through
        // to the GPR fallback below and silently fail to reconstruct (the
        // universe-backfill audit caught exactly that).
        AArch64Opcode::FaddRR
        | AArch64Opcode::FsubRR
        | AArch64Opcode::FmulRR
        | AArch64Opcode::FdivRR
        | AArch64Opcode::FmaxnmRR
        | AArch64Opcode::FminnmRR => vec![s(0), s(1), s(2)],

        // Scalar FUSED FP multiply-add: ternary [dst, rn, rm, ra], all S (F32).
        AArch64Opcode::FmaddRR => vec![s(0), s(1), s(2), s(3)],

        // FP unary value ops: [dst, rn], S registers.
        AArch64Opcode::FnegRR
        | AArch64Opcode::FabsRR
        | AArch64Opcode::FsqrtRR
        | AArch64Opcode::FrintmRR
        | AArch64Opcode::FrintpRR
        | AArch64Opcode::FrintzRR => {
            vec![s(0), s(1)]
        }

        // FP -> int conversions: [dst(GPR), rn(FP)].
        AArch64Opcode::FcvtzsRR | AArch64Opcode::FcvtzuRR => vec![w(0), s(1)],

        // int -> FP conversions: [dst(FP), rn(GPR)].
        AArch64Opcode::ScvtfRR | AArch64Opcode::UcvtfRR => vec![s(0), w(1)],

        // FP-format casts: FcvtSD widens S->D ([D, S]); FcvtDS narrows D->S
        // ([S, D]). Both operands are FP, of DIFFERING widths.
        AArch64Opcode::FcvtSD => vec![d(0), s(1)],
        AArch64Opcode::FcvtDS => vec![s(0), d(1)],

        // FMOV-immediate: [dst(FP S), FImm]. 2.0 is FMOV-encodable (field 0x00).
        AArch64Opcode::FmovImm => vec![s(0), MachOperand::FImm(2.0)],

        // Shifted-register EOR: [dst, Rn, Rm, Imm(k)].
        AArch64Opcode::EorRRLsl | AArch64Opcode::EorRRLsr => {
            vec![w(0), w(1), w(2), MachOperand::Imm(7)]
        }

        // ROR-immediate / EXTR alias: [dst, Rn, Imm(k)]. Use a non-zero
        // in-range amount because #0 is encoded as the separate move alias.
        AArch64Opcode::RorRI => vec![w(0), w(1), MachOperand::Imm(7)],

        // The other immediate forms: [dst, Rn, #imm]. Their representative
        // carries an immediate the form can encode (a non-zero shift amount, an
        // imm12, a logical bitmask immediate); a register third operand would
        // be the register form, which their word cannot carry and the verifier
        // refuses.
        AArch64Opcode::AddRI
        | AArch64Opcode::SubRI
        | AArch64Opcode::LslRI
        | AArch64Opcode::LsrRI
        | AArch64Opcode::AsrRI => vec![w(0), w(1), MachOperand::Imm(7)],
        AArch64Opcode::AndRI | AArch64Opcode::OrrRI | AArch64Opcode::EorRI => {
            vec![w(0), w(1), MachOperand::Imm(0xFF)]
        }

        // Other unary (Neg): [dst, src].
        _ if arity == AluArity::Unary => vec![w(0), w(1)],
        // Binary register form: [dst, src1, src2].
        _ => vec![w(0), w(1), w(2)],
    };
    Some(MachInst::new(opcode, operands))
}

/// Does a representative reconstructed obligation for `opcode` discharge `Valid`
/// under `config`? Used by the COVERAGE GATE to mark a reconstructable opcode as
/// covered in its inventory (task #63 Step 4).
///
/// Returns `false` (NOT covered) for any opcode that is not reconstructable, that
/// has no representative instance, that fails to reconstruct, or whose
/// reconstructed obligation does not discharge `Valid`. The criterion is the
/// obligation being `Reconstructed` (its machine side came from the REAL
/// opcode) AND discharging `Valid` for ONE synthesized representative instance,
/// where a sampled sweep counts as `Valid`. That is NOT the per-instruction
/// walk's credit rule and does not measure it: since E0.2 the walk credits an
/// emitted instruction only from an obligation built from that instruction
/// whose discharge is complete (exhaustive or formal), and reports a sampled
/// discharge as unverified. A `true` here is inventory evidence about a
/// representative form, never instruction credit, and no promotion decision
/// reads it. `RorRI` additionally checks an X64 representative: its EXTR
/// immediate field and concatenation width are width-sensitive, so the
/// opcode-level mark requires both emitted W32 and X64 forms to discharge.
pub fn reconstruction_discharges_valid(opcode: AArch64Opcode, config: &VerificationConfig) -> bool {
    let Some(inst) = representative_reconstructable_inst(opcode) else {
        return false;
    };
    let discharges = |inst: &MachInst| {
        let Some(obligation) = reconstruct_alu_obligation(inst) else {
            return false;
        };
        if !obligation.is_reconstructed() {
            return false;
        }
        // Routed through the shared CONTENT-keyed memo (PROOF-2): sound by
        // construction (the key embeds the full obligation, never just its
        // name) and skips re-sweeping the same representative obligation per
        // compile.
        matches!(
            memoized_verify_by_evaluation(&obligation, config),
            VerificationResult::Valid
        )
    };
    if !discharges(&inst) {
        return false;
    }
    if opcode != AArch64Opcode::RorRI {
        return true;
    }

    use trust_cg_ir::RegClass;
    use trust_cg_ir::regs::VReg;
    let x = |id: u32| MachOperand::VReg(VReg::new(id, RegClass::Gpr64));
    let x64 = MachInst::new(AArch64Opcode::RorRI, vec![x(0), x(1), MachOperand::Imm(7)]);
    discharges(&x64)
}

// ---------------------------------------------------------------------------
// FunctionVerifier
// ---------------------------------------------------------------------------

/// Verifier that maps MachFunction instructions to proof obligations.
/// Which registry family a precise citation names (see `refine_citation`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum PreciseFamily {
    Icmp,
    CondBr,
}

/// `TCG_PRECISE_CITATIONS=1`: name the instruction's own family member
/// instead of the category's first match. A citation is diagnostic text in a
/// refusal only: registry name lookup is never instruction credit, so this flag
/// changes no verdict and no code.
pub(crate) fn precise_citations_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("TCG_PRECISE_CITATIONS").is_some())
}

/// `TCG_TIME_WALK=1`: per-function split of the certificate walk's time by arm.
fn walk_timing_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("TCG_TIME_WALK").is_some())
}

/// `TCG_TRACE_CITATIONS=1`: one line per refined / fallen-back citation.
fn citation_trace_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("TCG_TRACE_CITATIONS").is_some())
}

/// One replay answer: the verdict, and why there is none (diagnostic only).
type TrapReplayAnswer = (Option<VerificationResult>, Option<String>);

/// The successor walk is conservative beyond the shared optimizer's bound.
const NZCV_LIVENESS_BLOCK_LIMIT: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NzcvLivenessEffect {
    Reads,
    Unknown,
    Kill,
    Neutral,
}

/// How one walk replays holding trap expansions (L04-P12): through the
/// caller's discharge context, or else through the walk's own request,
/// captured once on first use. Either way the replay is the request's (its
/// admitted AY and Clean, policy and refusals). Answers are memoised for this
/// walk, so for one request only, keyed by the register-renamed obligation.
struct TrapReplayRoute<'c, 'r> {
    xcheck_mode: ProvenanceXCheckMode,
    context: Option<&'c crate::function_request::FunctionDischargeContext<'r>>,
    owned_request: &'c std::cell::OnceCell<crate::FunctionVerificationRequest>,
    answers: std::cell::RefCell<std::collections::HashMap<ProofObligation, TrapReplayAnswer>>,
}

impl TrapReplayRoute<'_, '_> {
    fn replay(
        &self,
        verifier: &FunctionVerifier,
        replay: &crate::aarch64_trap_expansion::TrapExpansionReplay,
    ) -> TrapReplayAnswer {
        if let Some(answer) = self.answers.borrow().get(replay.obligation()) {
            return answer.clone();
        }
        let answer = match self.context {
            Some(context) => context.trap_expansion(replay),
            None => {
                let request = self
                    .owned_request
                    .get_or_init(|| verifier.capture_request_with_mode(self.xcheck_mode));
                crate::function_request::FunctionDischargeContext::new(request)
                    .trap_expansion(replay)
            }
        };
        self.answers
            .borrow_mut()
            .insert(replay.obligation().clone(), answer.clone());
        answer
    }
}

pub struct FunctionVerifier {
    db: ProofDatabase,
    config: VerificationConfig,
    /// `(category, query)` → index into `db.all()` of the registry proof the
    /// walk's query resolves to (or `None`). The queries are a fixed set of
    /// `&'static str`s chosen per opcode/operand shape; resolving one meant
    /// collecting the category's proofs into a fresh `Vec` and lowercasing
    /// every candidate's name, per instruction of every certificate walk and
    /// pre-warm enumeration. Resolved once per process instead.
    query_memo:
        std::sync::Mutex<std::collections::HashMap<(ProofCategory, &'static str), Option<usize>>>,
}

/// Reaching definitions and limb anchoring for the i128 `CSET`/`CSEL`
/// bindings (the ROLE, ARM-PAIR and DATA-FLOW holes `2e194289f` disclosed). A
/// child module so it can reuse this verifier's flag-producer scan unchanged.
#[path = "aarch64_i128_chain_dataflow.rs"]
mod i128_chain_dataflow;

/// The i128 variable-shift chain's sibling shape, as
/// [`FunctionVerifier::i128_shift_chain_siblings`] reports it: each reaching
/// integer CMP as `(condition immediate, carrier width)`, then the CSEL
/// condition immediates that read those flags.
type I128ShiftChainSiblings = (Vec<(i64, u32)>, Vec<i64>);

impl FunctionVerifier {
    /// Every proof category reachable from this verifier's query builders.
    ///
    /// Building only these categories avoids constructing architecture-specific
    /// databases this AArch64 verifier cannot consult (notably 531 x86-64
    /// obligations). `ProofDatabase::for_categories` preserves each category's
    /// full-database order and fails closed if this list ever under-requests.
    const CONSULTED_CATEGORIES: &'static [ProofCategory] = &[
        ProofCategory::AddressMode,
        ProofCategory::Arithmetic,
        ProofCategory::AtomicOperations,
        ProofCategory::BitwiseShift,
        ProofCategory::Branch,
        ProofCategory::CmpCombine,
        ProofCategory::Comparison,
        ProofCategory::ConstantMaterialization,
        ProofCategory::Division,
        ProofCategory::ExtensionTruncation,
        ProofCategory::FloatingPoint,
        ProofCategory::FpConversion,
        ProofCategory::FrameLayout,
        ProofCategory::MachOEmission,
        ProofCategory::Memory,
        ProofCategory::NeonLowering,
        ProofCategory::RegAlloc,
    ];

    /// Create a new function verifier with default configuration.
    pub fn new() -> Self {
        Self {
            // AArch64 never discharges an x86-64 obligation, and skipping that
            // one registry is already worth 40.6 ms of the 50.2 ms database
            // build, once per compile (see `ProofDatabase::new_without_x86_64`).
            // `for_categories(CONSULTED_CATEGORIES)` SUBSUMES that saving — it
            // runs only the registrars whose categories this verifier can
            // actually consult, x86-64 included — and, unlike a hand-maintained
            // second registrar list, it is CHECKED rather than assumed:
            // `registrar_category_table_matches_reality`,
            // `for_categories_matches_full_database` and
            // `aarch64_database_matches_full_database_for_consulted_categories`
            // fail closed if the manifest ever under-requests. That check is
            // load-bearing, not ceremony: `new_without_x86_64` has ALREADY
            // drifted from `new()` — it omits `register_widening_multiply_proofs`,
            // whose obligation the `Umull => "-> umull xd"` binding below
            // consults — so building through it would silently drop that credit.
            db: ProofDatabase::for_categories(Self::CONSULTED_CATEGORIES),
            query_memo: std::sync::Mutex::new(std::collections::HashMap::new()),
            config: VerificationConfig::default(),
        }
    }

    /// Create a new function verifier with custom verification configuration.
    pub fn with_config(config: VerificationConfig) -> Self {
        Self {
            // Same category-filtered database as `new`; see the note there for
            // why this is the checked form of "don't build x86-64 obligations".
            db: ProofDatabase::for_categories(Self::CONSULTED_CATEGORIES),
            query_memo: std::sync::Mutex::new(std::collections::HashMap::new()),
            config,
        }
    }

    /// Map an AArch64 opcode to a registry search query and category.
    ///
    /// Returns `Some((search_substring, category))` for opcodes that name a
    /// registered theorem family, or `None` otherwise. The mapping is an
    /// inventory and diagnostic surface (the coverage gate and refusal text):
    /// the theorem a substring selects is not about the emitted instruction, so
    /// the walk never credits it.
    pub fn opcode_to_proof_query(opcode: AArch64Opcode) -> Option<(&'static str, ProofCategory)> {
        use AArch64Opcode::*;
        match opcode {
            // Arithmetic
            AddRR | AddRI => Some(("add", ProofCategory::Arithmetic)),
            SubRR | SubRI => Some(("sub", ProofCategory::Arithmetic)),
            MulRR => Some(("mul", ProofCategory::Arithmetic)),
            Madd => Some(("madd_rr", ProofCategory::Arithmetic)),
            Msub => Some(("msub_rr", ProofCategory::Arithmetic)),
            // 32->64 UNSIGNED widening multiply (UMULL Xd, Wn, Wm — the
            // UMADDL-with-XZR alias). UMULL has EXACTLY ONE legal form (sf=1 is
            // hardwired; sources always W, destination always X; the encoder
            // emits only this word), so an OPCODE-level binding is faithful —
            // the #62 unfaithful-inheritance hazard (one form's proof credited
            // to a different form) cannot arise. Bound to the FAITHFUL widening
            // obligation (lowering_proof::proof_umull_rr: SOURCE = the
            // Concat-zext ring form `concat(0,a)*concat(0,b)`, MACHINE = the
            // encoder-faithful `0 + ZeroExtend(a)*ZeroExtend(b)` — structurally
            // distinct, provably equal over BV64). The SMULL sext confusion —
            // exactly what separates UMULL from SMULL — and the truncating-MUL
            // confusion both REFUTE (umull_wrong_controls). SMULL deliberately
            // stays UNMAPPED (deferred RED in coverage_gate): the SIGNED
            // widening multiply must NOT inherit this unsigned-zext proof.
            // Query MUST be lowercase: verify() does
            // name.to_lowercase().contains(query) WITHOUT lowercasing the query.
            Umull => Some(("-> umull xd", ProofCategory::Arithmetic)),
            Neg => Some(("neg", ProofCategory::Arithmetic)),

            // Division
            SDiv => Some(("sdiv", ProofCategory::Division)),
            UDiv => Some(("udiv", ProofCategory::Division)),

            // Compare / NZCV
            CmpRR | CmpRI | CMPWrr | CMPXrr | CMPWri | CMPXri => {
                Some(("cmp", ProofCategory::Comparison))
            }
            // TST produces the COMPLETE NZCV state, and the packed-NZCV
            // theorem (`cmp_combine_proofs::proof_tst_packed_nzcv`) pins all
            // four flags — N, Z and the architecturally CLEARED C/V — against
            // the encoder, so this is NOT the #62 unfaithful-inheritance hazard.
            // (Crediting ONE condition's theorem for all conditions WOULD be:
            // the faithful per-condition obligations from `proof_tst_nzcv_effect`
            // are a narrower authority and are bound CONTEXT-SENSITIVELY by
            // `tst_nzcv_consumer_query` in the in-block chain, which runs first.)
            // Concrete instructions are width/shape-bound below by
            // `operand_sensitive_or_opcode_query`; this opcode-level token is
            // used only by callers that do not have operands (the coverage gate
            // separately demands BOTH registered widths discharge). Fusion forms
            // TST;B.EQ ≡ TBZ stay covered under CmpCombine.
            Tst => Some(("tst packed nzcv", ProofCategory::CmpCombine)),

            // Branch
            BCond | Bcc => Some(("condbr", ProofCategory::Branch)),
            // RET: its only mapped proof was the degenerate "Call lowering: RET
            // branches to LR" X==X (retracted in #62). No value-proof mapping;
            // RET is FailClosedAllowlisted in classify_aarch64 (the return edge is
            // covered by the Branch/CallLowering CFG family).
            Ret => None,

            // Memory
            LdrRI | LdrbRI | LdrhRI | LdrsbRI | LdrshRI | LdrRO | LdrbRO | LdrhRO => {
                Some(("load", ProofCategory::Memory))
            }
            StrRI | StrbRI | StrhRI | StrRO | StrbRO | StrhRO | STRWui | STRXui | STRSui
            | STRDui => Some(("store", ProofCategory::Memory)),
            // Legacy single-vector memory queries remain unchanged here. The
            // pair siblings explicitly refuse attribution below: sharing a
            // broad load/store query does not authenticate pair semantics.
            NeonLd1Post => Some(("load", ProofCategory::Memory)),
            NeonSt1Post => Some(("store", ProofCategory::Memory)),
            // Legacy scalar writeback/literal queries are outside the pair
            // withdrawal. Their presence is not a complete memory-effect or
            // base-writeback binding and must not authorize pair instructions.
            LdrPreIndex | LdrPostIndex | LdrLiteral => Some(("load", ProofCategory::Memory)),
            StrPreIndex | StrPostIndex => Some(("store", ProofCategory::Memory)),
            // Acquire/release atomic load & store — bound to the registered
            // AtomicOperations memory-model proofs (atomic_proofs::all_atomic_load_
            // proofs `AtomicLoad_I{8,16,32,64} -> LDAR{B,H,_W,_X}`;
            // all_atomic_store_proofs `AtomicStore_Load_I*: STLR->LDAR roundtrip`),
            // registered under ProofCategory::AtomicOperations and disclosed on
            // GENUINE_IDENTITY_ALLOWLIST. These were UNWIRED per-compile (like
            // NeonUmovGen) so every atomic program fail-closed on Ldar/Stlr; the
            // proofs already exist. Query MUST be lowercase; "-> ldar" is a unique
            // substring of the four LDAR* names, "stlr" of the four STLR* names.
            Ldar | Ldarb | Ldarh => Some(("-> ldar", ProofCategory::AtomicOperations)),
            Stlr | Stlrb | Stlrh => Some(("stlr", ProofCategory::AtomicOperations)),
            // Compare-and-swap — the RETAINED CAS_I{32,64} success-path proof
            // (`mem[addr] = desired`). NARROW: only the CAS family. The exclusive
            // (Ldaxr/Stlxr) and min/max LSE RMW opcodes stay fail-closed here.
            //
            // CORRECTION (measured): this comment used to say the same of `Swp*`,
            // on the grounds that `all_atomic_proofs()` "RETRACTED their degenerate
            // 'returns old value' obligations, so no retained proof backs them".
            // That conflates two different halves. The #62 retraction drops only
            // names ending `": returns old value"` and the `Fence_*`/`-> DMB`
            // tautologies — `SWP_I32: mem[addr] = operand` is registered and IS
            // retained, exactly like the `LDADD_I*: mem[addr] = ...` proofs the arm
            // below names. SWP's MEMORY EFFECT was backed all along;
            // only its returned-value half was not.
            //
            // `Swp*` is therefore bound in `operand_sensitive_or_opcode_query`
            // instead of here, because the binding must be WIDTH-CORRECT and the
            // opcode alone cannot say which width was emitted.
            Cas | Casa | Casal | Casl => {
                Some(("cas_i32: success path", ProofCategory::AtomicOperations))
            }
            // LSE fetch-op RMW (fetch_add / _or / _xor / _and) — bound to the
            // RETAINED memory-effect proofs `LD{ADD,SET,EOR,CLR}_I32: mem[addr] =
            // old OP operand` (the faithful side; the returned old value is the old
            // memory read, the shared Ldr* load debt). All four acquire/release
            // ordering variants share the opcode's memory semantics. SWP and the
            // signed/unsigned min/max RMW deliberately STAY fail-closed here
            // (conservative — see the atomic_swap_and_exclusive negative control).
            Ldadd | Ldadda | Ldaddal | Ldaddl => {
                Some(("ldadd_i32: mem", ProofCategory::AtomicOperations))
            }
            Ldset | Ldseta | Ldsetal | Ldsetl => {
                Some(("ldset_i32: mem", ProofCategory::AtomicOperations))
            }
            Ldeor | Ldeora | Ldeoral | Ldeorl => {
                Some(("ldeor_i32: mem", ProofCategory::AtomicOperations))
            }
            Ldclr | Ldclra | Ldclral | Ldclrl => {
                Some(("ldclr_i32: mem", ProofCategory::AtomicOperations))
            }
            // Dense-`match` / fieldless-enum JUMP-TABLE scaled table-entry load:
            // LDRSW Xt,[Xn,Xm,LSL#2]. Credited to the FAITHFUL scaled-EFFECTIVE-
            // ADDRESS proof (proof_ldrsw_ro_scaled_addr, AddressMode): the emitted
            // `[Xn,Xm,LSL#2]` addressing mode computes `base + (index<<2)`, which
            // equals the intended 4-byte-entry indexing `base + 4*index` (bvshl vs
            // bvmul — STRUCTURALLY DISTINCT, so a wrong scale REFUTES). This is the
            // non-degenerate ADDRESS-MODE part LdrswRO contributes — strictly
            // STRONGER than the degenerate `("load", Memory)` query (which is on the
            // KNOWN_DEGENERATE_PENDING_FIX debt and proves nothing); it is NOT a full
            // memory-load proof (the dereference + i32->i64 sext loaded VALUE stays
            // the shared unfaithful-load debt of the Ldr* family). Query MUST be
            // lowercase: verify() does name.to_lowercase().contains(query) WITHOUT
            // lowercasing the query. "jump-table ldrsw" is a substring of the
            // (lowercased) AddressMode proof name and disjoint from the other
            // AddrMode rows. (DELIBERATELY not folded into the Memory "load" arm.)
            LdrswRO => Some(("jump-table ldrsw", ProofCategory::AddressMode)),

            // Pair encodability is not source/frame proof applicability. The
            // static alignment, slot non-overlap and one-slot restore models
            // do not bind these operands, both transfers, memory state or base
            // writeback. Even SP/X29 does not establish a prior matching save.
            // Keep those models as diagnostics, with no runtime attribution.
            // Do not fall back to "load"/"store": those broad searches can
            // select a retained I32/offset0 pair or byte-roundtrip theorem,
            // neither of which authenticates this concrete instruction.
            StpRI | LdpRI | StpPreIndex | LdpPostIndex | NeonLdpQPost | NeonStpQPost => None,

            // Floating-point
            FaddRR => Some(("fadd", ProofCategory::FloatingPoint)),
            FmaddRR => Some(("fmadd", ProofCategory::FloatingPoint)),
            FsubRR => Some(("fsub", ProofCategory::FloatingPoint)),
            FmulRR => Some(("fmul", ProofCategory::FloatingPoint)),
            FminnmRR => Some(("fminnm", ProofCategory::FloatingPoint)),
            FmaxnmRR => Some(("fmaxnm", ProofCategory::FloatingPoint)),
            FnegRR => Some(("fneg", ProofCategory::FloatingPoint)),
            // Static FCMP+CSET Boolean models do not bind this instruction's
            // operands/width, full NZCV result, or reaching consumers. One GE
            // model cannot certify all flags (it never observes C). They stay
            // diagnostic and the opcode stays unmapped: a concrete FCMP binds
            // per instruction, by its operand width, to the packed-NZCV
            // obligation of `aarch64_flag_consumer_proofs` (see
            // `operand_sensitive_or_opcode_query`).
            Fcmp => None,
            // FMOV (FPR scalar copy) and the cross-class scalar bitcasts
            // (FPR↔GPR: to_bits/from_bits/copysign). The retracted CopyProp
            // X==X credits nothing and there is no OPCODE-wide query: each
            // concrete instruction binds to its decoded-word form's obligation
            // in `operand_sensitive_or_opcode_query`
            // (`aarch64_value_decode_proofs::a64_value_bound_form`); any other
            // shape stays Unverified.
            FmovFprFpr => None,
            FmovFprGpr | FmovGprFpr => None,

            // Generated scalar FP conversion instructions from casts,
            // promote, and demote lowering.
            FcvtzsRR => Some(("fcvtzs", ProofCategory::FpConversion)),
            FcvtzuRR => Some(("fcvtzu", ProofCategory::FpConversion)),
            ScvtfRR => Some(("scvtf", ProofCategory::FpConversion)),
            UcvtfRR => Some(("ucvtf", ProofCategory::FpConversion)),
            FcvtSD => Some(("fpromote_f64_f32", ProofCategory::FpConversion)),
            FcvtDS => Some(("fdemote_f32_f64", ProofCategory::FpConversion)),

            // Generated scalar extensions used by return-value placement and
            // integer extension lowering.
            Sxtb => Some(("sextend_i8_to_i32", ProofCategory::ExtensionTruncation)),
            Sxth => Some(("sextend_i16_to_i32", ProofCategory::ExtensionTruncation)),
            Sxtw => Some(("sextend_i32_to_i64", ProofCategory::ExtensionTruncation)),
            Uxtb => Some(("uextend_i8_to_i32", ProofCategory::ExtensionTruncation)),
            Uxth => Some(("uextend_i16_to_i32", ProofCategory::ExtensionTruncation)),
            Uxtw => Some(("uextend_i32_to_i64", ProofCategory::ExtensionTruncation)),

            // GPR register copy (MOV and the typed post-allocation copies
            // MOVWrr/MOVXrr): the retracted CopyProp X==X credits nothing and
            // there is no OPCODE-wide query. Each concrete instruction binds to
            // its decoded-word form (MovW/MovX/MovXFromSp, MovWrr/MovXrr) in
            // `operand_sensitive_or_opcode_query`; any other shape stays
            // Unverified.
            MovR | MOVWrr | MOVXrr => None,

            // Generated constant materialization moves used by large frame
            // offsets and small negative integer constants. MovI and the typed
            // aliases are shift-zero forms. Canonical Movz also carries an
            // optional halfword shift architecturally, but hw1/hw2/hw3 identity
            // obligations are deliberately retracted under #62 and the encoder
            // rejects those forms. `operand_sensitive_or_opcode_query` prevents
            // malformed/external shifted forms from inheriting the hw0 proof.
            MovI | Movz | MOVZWi | MOVZXi => Some((
                "movz #imm16, lsl #0",
                ProofCategory::ConstantMaterialization,
            )),
            // MOVN is credited ONLY through the operand-sensitive per-(width,
            // halfword) inverted-field binding in
            // `operand_sensitive_or_opcode_query`
            // (`const_materialize_proofs::movn_halfword_query`); the W forms pin
            // the 32-bit complement plus zero-extension. Opcode-wide credit
            // would let one form's theorem stand for another. The coverage gate
            // demands every legal form (`aarch64_form_polymorphic_proofs`).
            Movn => None,
            // MOVK is credited ONLY through the operand-sensitive per-(width,
            // halfword) splice binding in `operand_sensitive_or_opcode_query`
            // (`const_materialize_proofs::movk_halfword_query`): opcode-wide
            // credit would let a malformed or wrong-slot MOVK inherit another
            // slot's proof. The historical "MOVK idempotent" theorem remains
            // registered but is not a lowering proof and is never bound here.
            Movk => None,

            // PC-relative address materialization (ADRP page + ADD lo12 pair
            // reconstructing the full symbol address). Credited to the
            // AY-discharged MachO data-relocation proofs
            // (aarch64_macho_data_reloc_proofs, registered under MachOEmission):
            // PAGE21 — `ADRP == page(S+A)`; PAGEOFF12 — `ADRP+ADD == S+A`. These
            // are FAITHFUL obligations (aarch64_expr = page+offset reconstruction,
            // trust_ir_expr = S+A — structurally distinct, so a broken page/offset
            // split REFUTES), NOT the degenerate const==const X==X that was
            // retracted (#62). This can clear the instruction-evidence lane;
            // the separately inventoried object relocation rows remain
            // production blockers without Certified, object-bound authority.
            Adrp => Some((
                "arm64_reloc_page21 adrp == page",
                ProofCategory::MachOEmission,
            )),
            AddPCRel => Some((
                "arm64_reloc_pageoff12 adrp+add == s+a",
                ProofCategory::MachOEmission,
            )),
            // TLS descriptor load (ADRP+LDR via TLVP relocations) — the
            // AY-discharged TLVP_LOAD_PAGEOFF12 proof (ADRP+LDR == D+A). The
            // preceding ADRP page is already covered by the data PAGE21 proof (the
            // page arithmetic is identical for a TLV slot). Query is a substring of
            // the TLVP-PAGEOFF12 name only (not the data ADRP+ADD nor TLVP-PAGE21).
            LdrTlvp => Some((
                "arm64_reloc_tlvp_load_pageoff12 adrp+ldr == d+a",
                ProofCategory::MachOEmission,
            )),
            // GOT load (ADRP+LDR via GOT relocations) — fn-pointer / extern-symbol
            // address materialization. The AY-discharged GOT_LOAD_PAGEOFF12 proof
            // (ADRP+LDR == G+A); the preceding ADRP page is already covered by the
            // data PAGE21 proof (page arithmetic is identical for a GOT slot).
            LdrGot => Some((
                "arm64_reloc_got_load_pageoff12 adrp+ldr == g+a",
                ProofCategory::MachOEmission,
            )),
            // ELF initial-exec GOT-TPREL load (ADRP+LDR via TLSIE relocations) —
            // solver-backed TLSIE_LD64_GOTTPREL_LO12_NC evidence (ADRP+LDR ==
            // G+A, the 8-aligned GOT slot holding TPREL(sym); 8-scaled imm12,
            // bits [11:3]). The preceding ADRP page is the
            // TLSIE_ADR_GOTTPREL_PAGE21 proof (same page ring identity). The ELF
            // TLS sibling of LdrGot/LdrTlvp above; registered with the ELF TLS
            // reloc lane under the shared object-emission proof family. This
            // does not mint production Certified object-inventory authority.
            // ELF local-exec TLS TPREL adds — the RETAINED faithful relocation
            // proofs (trust_ir = TP + (TPREL slice) vs the aarch64 patched-imm
            // contribution — structurally distinct; a dropped LSL#12 / wrong slice
            // REFUTES). Proven-but-unwired. The distinctive suffix avoids binding
            // the Invalid refutation-control proof of the same family (verify()
            // takes the FIRST category match).
            // The TLSLE TPREL adds are NOT credited: the registered
            // relocation-arithmetic identities (TP + TPREL slices over S/A)
            // name no register, word or relocation site, the LO12 one is a
            // two-instruction composite, and ENC-5 does not check their words.
            // They are named deferred rows in the coverage gate and refused
            // here (`tprel_add_refusal_reason`).
            AddTprelHi12 | AddTprelLo12 => None,
            LdrGottprel => Some((
                "tlsie_ld64_gottprel_lo12_nc adrp+ldr == g+a",
                ProofCategory::MachOEmission,
            )),
            // Dense-`match` / fieldless-enum JUMP-TABLE dispatch base: ADR
            // materializes the (appended) jump-table base via the internal __text
            // PC-relative delta `imm21 = T - P`, so the CPU computes
            // `Xd = P + (T - P) == T`. Credited to the AY-discharged
            // proof_adr_jumptable_pcrel (MachOEmission). FAITHFUL (machine =
            // P + (T - P) vs spec = T, structurally distinct, so an ABSOLUTE
            // encoder dropping `-P` refutes), the byte-granular sibling of the
            // BRANCH26 call-target ring identity. Query MUST be lowercase: verify()
            // does name.to_lowercase().contains(query) WITHOUT lowercasing the
            // query. "adr xd == table_base" is a substring of the (lowercased)
            // proof name and disjoint from the ADRP page/pageoff proofs.
            Adr => Some(("adr xd == table_base", ProofCategory::MachOEmission)),

            // Direct PC-relative branch / call (B / BL): the BRANCH26-relocated
            // target reconstructs `P + ((S+A)-P) == S+A`. Credited to the
            // AY-discharged call-relocation proof (proof_branch26_call_target,
            // MachOEmission). FAITHFUL (machine = P+offset vs spec = S+A,
            // structurally distinct, so a wrong/absolute relocation refutes), NOT
            // an X==X. The PC<-target control transfer is architecturally fixed;
            // this certifies the TARGET computation, exactly as ADRP/ADD above
            // certify the address. (Indirect Br/Blr/BLR are CoveredElsewhere —
            // the jump-table BR's register is bound per compile to the
            // ADR/LDRSW/ADD chain, bounds check and table bytes by
            // `aarch64_switch_binding`; BLR's target register is the call
            // lowering's obligation.)
            B | Bl | BL | TailCall => Some(("branch26 bl == s+a", ProofCategory::MachOEmission)),

            // Logical ops: bound to the registered GENERAL bitwise proofs whose
            // machine side IS the AArch64 AND/ORR/EOR bitvector form
            // (lowering_proof.rs: aarch64_expr a.bvand/bvor/bvxor(b)). These
            // mirror the x86 mapping (AndRR -> "Band_I", etc.). The op-keyed
            // lowercase query resolves first-contains (within the BitwiseShift
            // category) to the i8 representative (Band_I8/Bor_I8/Bxor_I8), all
            // of which discharge. NOTE: do NOT bind these to ProofCategory::
            // Peephole — that category only holds degenerate special-case
            // rewrite identities (e.g. "AND Xd,Xn,Xn ≡ MOV", which proves only
            // Xn&Xn=Xn), NOT the general operation semantics.
            AndRR | AndRI => Some(("band_i", ProofCategory::BitwiseShift)),
            OrrRR | OrrRI => Some(("bor_i", ProofCategory::BitwiseShift)),
            EorRR | EorRI => Some(("bxor_i", ProofCategory::BitwiseShift)),
            // EOR with a ROR-shifted operand — the RETAINED faithful
            // Eor_Ror_Shift_I{32,64} obligations (non-degenerate: wrong ROR amount /
            // LSR-not-ROR / operand-swap REFUTE). Proven-but-unwired (like
            // NeonUmovGen); the width-poly coverage table demands BOTH widths.
            EorRRShift => Some(("eor_ror_shift_i32", ProofCategory::BitwiseShift)),
            // ADD/SUB with an LSL-shifted second source — the FAITHFUL
            // Add/Sub_Lsl_Shift_I{32,64} obligations (non-degenerate: wrong
            // amount / ADD-vs-SUB / SUB operand-swap REFUTE). Placed in
            // BitwiseShift (not Arithmetic) so the "add"/"sub" Arithmetic queries
            // cannot first-contains-collide; the width-poly table demands BOTH
            // widths. The lower-case name "add_lsl_shift_i32" resolves here.
            AddRRShift => Some(("add_lsl_shift_i32", ProofCategory::BitwiseShift)),
            SubRRShift => Some(("sub_lsl_shift_i32", ProofCategory::BitwiseShift)),
            // ADD with an LSR-shifted second source — the FAITHFUL
            // Add_Lsr_Shift_I{32,64} obligations (non-degenerate: wrong amount /
            // ASR-not-LSR / LSL-not-LSR / SUB-not-ADD REFUTE). Placed in
            // BitwiseShift like its LSL sibling (no Arithmetic "add" query
            // collision); the width-poly table demands BOTH widths. The
            // lower-case name "add_lsr_shift_i32" resolves here.
            AddRRShiftLsr => Some(("add_lsr_shift_i32", ProofCategory::BitwiseShift)),

            // Shifts (LSL/LSR/ASR): the static "Ishl/Ushr/Sshr -> SHL/LSL/LSR/ASR"
            // proofs were degenerate X==X (#57 precond added identically to both
            // sides — cosmetic) and were RETRACTED in #62. These opcodes are now
            // CREDITED via OPERAND RECONSTRUCTION with the faithful hardware-
            // amount-masked machine encoder under a LOAD-BEARING amount<width
            // precondition — that is the genuine coverage. They therefore have no
            // static value-proof mapping here (reconstruction is the credit).
            LslRR | LslRI | LsrRR | LsrRI | AsrRR | AsrRI => None,

            // Bitfield EXTRACT (UBFM/SBFM): bound to the FAITHFUL extract-ENCODING
            // proofs — the isel encoding `immr=lsb, imms=lsb+width-1`, decoded by
            // the ARM hardware UBFM/SBFM (mask width `imms-immr+1`), equals the
            // trust_ir ExtractBits/SextractBits (mask width `width`). The two sides
            // are STRUCTURALLY DISTINCT, so a wrong immr/imms formula REFUTES (NOT
            // the degenerate X==X that reusing the structurally-identical
            // `encode_ubfm_extract` reconstruction would be). Concrete
            // instructions are shape-checked and bound to their exact w32/w64
            // theorem by `operand_sensitive_or_opcode_query`; this opcode-level
            // family token is the inventory fallback. The coverage gate's
            // width-polymorphic table ADDITIONALLY requires BOTH proofs discharge
            // (see `aarch64_width_polymorphic_proofs`), so neither width ships
            // unproven.
            // Query MUST be lowercase: verify() does name.to_lowercase().contains(query)
            // WITHOUT lowercasing the query. The "ubfm"/"sbfm" prefix keeps the two
            // disjoint (and clear of the sextend/uextend extends in the same
            // category). BFM (insert) and RBIT stay fail-closed — no faithful
            // per-opcode obligation yet. RorRI has no static mapping HERE
            // either, but for the opposite reason: it is now emitted standalone
            // by the rotate recognizer and binds per DESTINATION WIDTH in
            // `operand_sensitive_or_opcode_query` to `all_ror_immediate_proofs`
            // ("rorri_i32"/"rorri_i64"), while its real immediate and EXTR alias
            // are credited by operand reconstruction. An opcode-wide entry here
            // would let a malformed RorRI inherit the wrong width's credit.
            Ubfm => Some(("ubfm extract w", ProofCategory::ExtensionTruncation)),
            Sbfm => Some(("sbfm extract w", ProofCategory::ExtensionTruncation)),

            // NEON bitwise vector ops (AND/ORR/EOR/BIC/NOT) — bound to the
            // FAITHFUL per-LANE-intent == whole-register lowering proofs: the
            // SOURCE is the trust_ir per-lane vector op (split the V128 into the 16
            // `.16B` byte lanes, apply the lane bitwise op, concat back) and the
            // MACHINE is the single whole-128-bit-register op the lowerer emits
            // (encode_neon_{and,orr,eor,bic,not}). The two sides are STRUCTURALLY
            // DISTINCT (a 16-lane concat tree vs one whole-register op), so a wrong
            // machine op (ORR where the source is AND, or BIC without the `~vm`
            // complement) REFUTES — NOT the degenerate X==X the OLD same-shape
            // `proof_vector_*` proofs are. One 128-bit obligation per opcode
            // suffices: bitwise ops are lane-width-INDEPENDENT over the register.
            // Query MUST be lowercase: verify() does name.to_lowercase().contains(query)
            // WITHOUT lowercasing the query. The "<opcode> lanewise-intent" token is
            // unique per opcode and disjoint from the OLD degenerate "VectorAnd ->
            // …" names in the same NeonLowering category, so `find` resolves to the
            // faithful proof. The NEON arith/compare/shift/perm ops STAY fail-closed
            // (they need separate per-lane reconstruction infra, not modeled here).
            // None of them has an opcode-wide mapping: each binds its
            // lanewise obligation per instruction, and only in the 16B shape
            // (`aarch64_value_decode_proofs::neon_bitwise_16b_bound_query`,
            // in `operand_sensitive_or_opcode_query`); the ORR register copy
            // binds its decoded-word form. The 8B shapes (V64 operands, Q = 0)
            // are refused by their exact shape.
            NeonAndV | NeonOrrV | NeonEorV | NeonBicV | NeonNotV => None,

            // NEON LANE-WISE COMPUTE ops (arith / compare / min-max / immediate
            // shift) — bound to the FAITHFUL per-lane D-REGISTER-PAIR obligations
            // (neon_lowering_proofs::proof_neon_*_lanewise_4s). The SOURCE slices
            // each lane DIRECTLY from the two 64-bit D-halves of the Q register
            // (`Extract(Var(vn_lo|vn_hi), …)`) and applies the per-lane op; the
            // MACHINE is the real `encode_neon_*` encoder over the reassembled
            // `Concat(hi, lo)` register (`Extract(Concat(…), …)`). STRUCTURALLY
            // DISTINCT (raw-half Var leaf vs an Extract-of-Concat), so a wrong NEON
            // instruction — wrong op (SUB for ADD), wrong SIGNEDNESS (SMAX for UMAX,
            // CMGT for CMHI, USHR for SSHR), wrong DIRECTION (CMGE for CMGT), or
            // wrong LANE WIDTH — REFUTES; NOT the degenerate X==X the same-shape
            // `proof_vector_*` obligations are. One `.4S` representative per opcode
            // (the arrangement the reduction / vectorization passes emit; the D-pair
            // decomposition is arrangement-parametric). Queries MUST be lowercase:
            // verify() does name.to_lowercase().contains(query) WITHOUT lowercasing
            // the query. Each `<opcode>.4s lanewise-intent` token is unique per
            // opcode and disjoint from the OLD degenerate "VectorAdd -> …" names and
            // the `.16b` bitwise tokens. HONEST SCOPE: this certifies the emitted
            // instruction computes the right per-lane op at the right width — the
            // same right-instruction guarantee the gate certifies elsewhere — with
            // NO cross-lane content (NEON lanes are independent).
            NeonAddV => Some(("addv.4s lanewise-intent", ProofCategory::NeonLowering)),
            NeonSubV => Some(("subv.4s lanewise-intent", ProofCategory::NeonLowering)),
            NeonMulV => Some(("mulv.4s lanewise-intent", ProofCategory::NeonLowering)),
            NeonCmeqV => Some(("cmeqv.4s lanewise-intent", ProofCategory::NeonLowering)),
            NeonCmgeV => Some(("cmgev.4s lanewise-intent", ProofCategory::NeonLowering)),
            NeonCmgtV => Some(("cmgtv.4s lanewise-intent", ProofCategory::NeonLowering)),
            NeonCmhiV => Some(("cmhiv.4s lanewise-intent", ProofCategory::NeonLowering)),
            NeonCmhsV => Some(("cmhsv.4s lanewise-intent", ProofCategory::NeonLowering)),
            NeonSmaxV => Some(("smaxv.4s lanewise-intent", ProofCategory::NeonLowering)),
            NeonSminV => Some(("sminv.4s lanewise-intent", ProofCategory::NeonLowering)),
            NeonUmaxV => Some(("umaxv.4s lanewise-intent", ProofCategory::NeonLowering)),
            NeonUminV => Some(("uminv.4s lanewise-intent", ProofCategory::NeonLowering)),
            NeonShlVImm => Some(("shlvimm.4s #3 lanewise-intent", ProofCategory::NeonLowering)),
            NeonUshrVImm => Some((
                "ushrvimm.4s #5 lanewise-intent",
                ProofCategory::NeonLowering,
            )),
            NeonSshrVImm => Some((
                "sshrvimm.4s #7 lanewise-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON POPCOUNT-FOLD ops (per-byte population count + unsigned add long
            // pairwise) — bound to the FAITHFUL D-REGISTER-PAIR obligations
            // (neon_lowering_proofs::proof_neon_cntv_lanewise_16b / _uaddlpv_*). The
            // SOURCE slices each INPUT lane DIRECTLY from the two 64-bit D-halves and
            // applies the per-byte popcount / pairwise zext-add; the MACHINE is the
            // real `encode_neon_cnt` / `encode_neon_uaddlp` over the reassembled
            // `Concat(hi, lo)` register. STRUCTURALLY DISTINCT, so a wrong NEON
            // instruction (CNT-as-identity, UADDLP-as-pairwise-SUB) REFUTES. Queries
            // MUST be lowercase (verify() does name.to_lowercase().contains(query)
            // WITHOUT lowercasing the query); each token is unique per opcode form.
            // NeonUaddlpV is one opcode with two arrangements (`.16B->.8H` and
            // `.8H->.4S`). Concrete instructions bind to the exact arrangement
            // theorem in `operand_sensitive_or_opcode_query`; this representative
            // fallback remains for opcode-only callers, whose coverage audit requires
            // BOTH obligations through `aarch64_width_polymorphic_proofs`.
            NeonCntV => Some(("cntv.16b lanewise-intent", ProofCategory::NeonLowering)),
            NeonUaddlpV => Some((
                "uaddlpv.16b->.8h lanewise-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON SIGNED add-long-pairwise — the signed sibling of NeonUaddlpV,
            // bound to the FAITHFUL D-REGISTER-PAIR obligations
            // (neon_lowering_proofs::proof_neon_saddlpv_16b_8h / _8h_4s): the
            // SOURCE slices each INPUT lane DIRECTLY from the two 64-bit D-halves
            // and applies the pairwise SIGN-extending add; the MACHINE is the real
            // `encode_neon_saddlp` over the reassembled `Concat(hi, lo)` register.
            // STRUCTURALLY DISTINCT, so a wrong NEON instruction — most notably
            // the SIGN-CONFUSION mutation SADDLP-as-UADDLP (zero- instead of
            // sign-extending, diverges on 0x80/0x8000 lanes) — REFUTES. Like
            // NeonUaddlpV, concrete instructions bind to the exact arrangement in
            // `operand_sensitive_or_opcode_query`; this representative fallback is
            // for opcode-only callers, whose audit requires both arrangements.
            NeonSaddlpV => Some((
                "saddlpv.16b->.8h lanewise-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON UMOV (lane -> GPR extract, zero-extending) — bound to the
            // FAITHFUL per-(element-size, lane) obligations
            // (neon_lowering_proofs::all_neon_umov_proofs, registered alongside the
            // popcount proofs at neon_lowering_proofs.rs). The SOURCE slices the
            // selected lane DIRECTLY from the two 64-bit D-halves and zero-extends
            // to the GPR width; the MACHINE is the real `encode_neon_umov_general`
            // over the reassembled `Concat(hi, lo)`. STRUCTURALLY DISTINCT — a
            // wrong lane or wrong element-size operand REFUTES
            // (`neon_umov_wrong_encoding_controls`); every lane is a compile-time
            // constant so the whole `(size, lane)` matrix is provable (NOT the X==X
            // #62 retracted). Like NeonUaddlpV, one opcode with many arrangements:
            // the query matches the `.4s lane00` obligation (the `.4S`-lane extract
            // the horizontal-reduce fold emits); the rest of the matrix is
            // co-registered and discharged by the same batch + gate tests, so the
            // opcode-level credit is that UMOV extracts the right lane. Query MUST
            // be lowercase (verify() does name.to_lowercase().contains(query)).
            NeonUmovGen => Some((
                "umovgen.4s lane00 extract-to-gpr32",
                ProofCategory::NeonLowering,
            )),

            // NEON CONSTANT MATERIALIZATION (`MOVI Vd.<T>, #imm8`, byte form) —
            // the vectorizers' accumulator zeroing, all-ones masks and byte
            // thresholds. Bound to the FAITHFUL byte-replication obligations
            // (neon_lowering_proofs::all_neon_movi_proofs).
            //
            // This previously credited the NeonEncoding identity "movi immediate"
            // on the stated grounds that "a faithful non-degenerate obligation is
            // impossible for a pure constant (its value IS the immediate)". That
            // reasoning does NOT hold, and the obligations it justified were
            // degenerate X==X. Two changes make a genuine theorem available:
            //   * the immediate is a SYMBOLIC 8-bit `Var`, so the claim is about
            //     EVERY byte value rather than one constant — which is what the
            //     emitters rely on (they pass 0, 1, 0x0F, 10, 39, 96, ...);
            //   * the SOURCE expresses replication ARITHMETICALLY
            //     (`zext(imm8) * 0x01..01` per element) while the MACHINE builds
            //     it STRUCTURALLY as a Concat chain. Same value by a non-trivial
            //     identity, so the solver must prove the replication rather than
            //     match syntax. `is_genuinely_proven()` holds; a test asserts it.
            // Q=0 upper-half zeroing and dropped replication both REFUTE.
            NeonMovi => Some((
                "movi.16b byte-replicated-immediate-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON DUP-from-GPR broadcast (DUP Vd.T, Wn — replicate a scalar GPR to
            // ALL lanes). Bound to the EXISTING `NeonEncoding: DUP broadcast 4S/8H`
            // proof (neon_encoding_proofs::proof_dup_4s/_8h: SOURCE = concat of N
            // identical lanes, MACHINE = encode_neon_dup) — a disclosed GENUINE
            // IDENTITY on GENUINE_IDENTITY_ALLOWLIST, EXACTLY the NeonMovi posture
            // (Verified but credits ZERO in the strict tally). SOUND because DupGen
            // broadcasts to ALL lanes with NO lane SELECTION — its per-instruction
            // NEON GPR-TO-ALL-LANES BROADCAST (`DUP Vd.<T>, Rn`) — was credited by
            // the DEGENERATE `all-lanes == src` encoding identity, which declared
            // its scalar AT LANE WIDTH so both sides were literally the expression
            // `encode_neon_dup` builds. Now bound to the FAITHFUL per-(element
            // size, lane) ROUND-TRIP obligations
            // (neon_lowering_proofs::all_neon_dup_gen_proofs): build the vector
            // with the real `encode_neon_dup`, read lane k back with the real
            // `encode_neon_umov_general`, and recover the GPR's low bits — against
            // a SOURCE that is a plain slice of the 64-bit GPR `Var`. Declaring the
            // GPR at its real width also forces the encoder's TRUNCATION branch,
            // which the degenerate identity never exercised. Wrong element SIZE
            // (read back at lane >= 1, where the sizes genuinely diverge) REFUTES.
            NeonDupGen => Some((
                "dupgen.4s lane00 gpr-broadcast-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON GPR-INTO-SELECTED-LANE INSERT (`INS Vd.<T>[lane], Rn`, TIED
            // destination). Bound to the FAITHFUL per-(element size, lane)
            // obligations (neon_lowering_proofs::all_neon_ins_gen_proofs): the
            // SOURCE splices the D-pair lanes, substituting the TRUNCATED GPR at
            // the target lane and PRESERVING every other lane sliced from the raw
            // halves; the MACHINE is the real `encode_neon_ins_general` (the dual
            // of `encode_neon_umov_general` — it truncates where UMOV
            // zero-extends). Because every 128-bit arrangement has >= 2 lanes, a
            // PRESERVED lane always appears, so lane preservation is genuinely
            // constrained. Wrong LANE (which also clobbers a preserved lane) and
            // wrong element SIZE REFUTE.
            NeonInsGen => Some((
                "insgen.4s lane00 gpr-insert-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON BIT (bitwise insert if true, tied destination) — bound to the
            // FAITHFUL obligation neon_lowering_proofs::proof_neon_bitv_lanewise_16b:
            // the SOURCE applies the per-BYTE insert `d ^ ((d ^ n) & m)` over the 16
            // byte lanes; the MACHINE is the whole-register `encode_neon_bit`.
            // STRUCTURALLY DISTINCT; the BSL/BIT/BIF family confusions (inverted
            // mask polarity, Vd-as-mask wiring, plain AND) all REFUTE. Query MUST be
            // lowercase; the token is unique to this opcode.
            NeonBitV => Some(("bitv.16b lanewise-intent", ProofCategory::NeonLowering)),

            // NEON SIGNED-ABS (`ABS.4S`) — bound to the FAITHFUL D-REGISTER-PAIR
            // obligation (neon_lowering_proofs::proof_neon_absv_lanewise_4s). The
            // SOURCE slices each 32-bit lane DIRECTLY from the two 64-bit D-halves and
            // applies the per-lane signed abs (`ite(a <s 0, 0 - a, a)`, so
            // abs(INT_MIN)==INT_MIN); the MACHINE is the real `encode_neon_abs` over
            // the reassembled `Concat(hi, lo)` register. STRUCTURALLY DISTINCT, so a
            // wrong NEON instruction (abs-as-identity, abs-as-negate-always) REFUTES.
            // Query MUST be lowercase (verify() does name.to_lowercase().contains(query)
            // WITHOUT lowercasing the query); the token is unique to this opcode.
            NeonAbsV => Some(("absv.4s lanewise-intent", ProofCategory::NeonLowering)),

            // NEON UNSIGNED DOT-PRODUCT-ACCUMULATE (`UDOT.4S`, FEAT_DotProd) — bound
            // to the FAITHFUL D-REGISTER-PAIR obligation
            // (neon_lowering_proofs::proof_neon_udotv_lanewise_4s). The SOURCE slices
            // the 4 input byte lanes of Vn/Vm AND the 32-bit ACCUMULATOR lane of Vd
            // DIRECTLY from the raw 64-bit D-halves and computes
            // `acc + sum_j(zext32(n_j) * zext32(m_j))`; the MACHINE is the real
            // `encode_neon_udot` over the reassembled `Concat(hi, lo)` registers.
            // STRUCTURALLY DISTINCT, so a wrong NEON instruction (dot-without-
            // accumulate, SDOT sign-extension, wrong byte group) REFUTES. Query MUST
            // be lowercase (verify() does name.to_lowercase().contains(query) WITHOUT
            // lowercasing the query); the token is unique to this opcode.
            NeonUdotV => Some(("udotv.4s lanewise-intent", ProofCategory::NeonLowering)),

            // NEON BYTE-WISE EXTRACT/CONCATENATE (`EXT.16B #1/#4/#8/#12/#15`) —
            // bound to the FAITHFUL D-REGISTER-PAIR obligations
            // (neon_lowering_proofs::proof_neon_extv_16b, one per emitted
            // immediate: the whole-i32-lane middle windows #4/#8/#12 plus the
            // single-byte shifted-NEIGHBOR streams #1 (`a[iv+1]`) / #15
            // (`a[iv-1]`) the neon-bytesum stencil count-if forms). The SOURCE
            // selects every output byte DIRECTLY from the raw 64-bit D-halves of
            // Vn/Vm — including the bytes that CROSS the D-half boundary — and the
            // MACHINE is the real `encode_neon_ext` over the reassembled
            // `Concat(hi, lo)` registers. STRUCTURALLY DISTINCT, so a wrong NEON
            // instruction (swapped operands, wrong immediate, opposite neighbor
            // direction, identity) REFUTES. Query MUST be lowercase (verify() does
            // name.to_lowercase().contains(query) WITHOUT lowercasing the query);
            // the token is unique to this opcode.
            NeonExtV => Some(("extv.16b lanewise-intent", ProofCategory::NeonLowering)),

            // NEON 32-BIT PAIR SWAP (`REV64.4S` — the AoS butterfly
            // vectorizer's complex `{rp, ip}` swap) — bound to the FAITHFUL
            // D-REGISTER-PAIR obligation
            // (neon_lowering_proofs::proof_neon_rev64v_4s). The SOURCE selects
            // every output 32-bit lane DIRECTLY from the raw D-halves of Vn at
            // the swapped index (`j ^ 1`); the MACHINE is the real
            // `encode_neon_rev64_4s` (whole-register shift/mask form) over the
            // reassembled register. STRUCTURALLY DISTINCT, so a wrong NEON
            // instruction (identity, doubleword swap, half-lane smear)
            // REFUTES. Query MUST be lowercase; the token is unique to this
            // opcode. BOTH emitted arrangements are proven — `.4S` (the
            // butterfly pair swap) and `.16B` (the byte reversal in the
            // `<2 x i64>` bit-reverse lowering); the gate demands both via
            // `aarch64_width_polymorphic_proofs`, this query names one.
            NeonRev64V => Some(("rev64v.4s pair-swap-intent", ProofCategory::NeonLowering)),

            // NEON PER-WORD BYTE REVERSE (`REV32.16B` / `.8B`) — the byte-order
            // half of the vectorizer's i32 `reverse_bits()` lowering (paired
            // with `RBIT` of the same arrangement). Bound to the FAITHFUL
            // D-REGISTER-PAIR obligations (neon_lowering_proofs::
            // all_neon_rev32_proofs): each output byte is selected DIRECTLY from
            // the raw D-halves at the within-32-bit-container reversed index
            // (`j ^ 3`), against the real `encode_neon_rev32_{16b,8b}` SWAR
            // model. Wrong container GRANULARITY (the REV64 butterfly) and
            // `.8B`/`.16B` confusion in both directions REFUTE (see
            // `neon_rev32_wrong_encoding_controls`). Both emitted arrangements
            // are demanded via `aarch64_width_polymorphic_proofs`.
            NeonRev32V => Some((
                "rev32v.16b byte-reverse-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON HORIZONTAL UNSIGNED MAX (`UMAXV Sd, Vn.4S`) — the vectorizer's
            // collapse of a `CMEQ.4S` compare mask to a scalar "any lane matched"
            // answer. Bound to the FAITHFUL CROSS-LANE obligation
            // (neon_lowering_proofs::proof_neon_umaxv_4s): the SOURCE is a
            // BALANCED-TREE `bvuge` maximum over lanes sliced from the raw
            // D-halves, the MACHINE the real `encode_neon_umaxv` LINEAR `bvugt`
            // left fold over the reassembled register — structurally distinct in
            // both LEAVES and FOLD SHAPE, so it cannot collapse to X==X.
            // SMAXV signedness confusion (diverges on the all-ones lanes CMEQ
            // produces), lane0 passthrough, and wrong element SIZE (.16B/.8H)
            // all REFUTE (see `neon_umaxv_wrong_encoding_controls`). `.4S` is
            // arrangement-complete: the rewrite bails on any other reduction
            // shape and the encoder rejects every other arrangement.
            NeonUmaxv => Some((
                "umaxv.4s cross-lane-max-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON SCALAR PAIRWISE ADD (`ADDP Dd, Vn.2D`, L04-P6) — bound to the
            // FAITHFUL CROSS-LANE obligation
            // (neon_lowering_proofs::proof_neon_addp_scalar_2d): the SOURCE adds
            // the two doublewords sliced from the raw D-halves, the MACHINE is
            // the real `encode_neon_addp_scalar_2d` over the reassembled
            // register. No-reduction, SUB, UMAXV-confusion, lane-miswire and
            // `.4S`-size controls all REFUTE
            // (`neon_addp_wrong_encoding_controls`). `.2D` is the only
            // architectural form; the encoder and ENC-5 refuse every other.
            NeonAddpScalar => Some((
                "addpscalar.2d cross-lane-sum-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON SELECTED-LANE BROADCAST (`DUP Vd.<T>, Vn.<Ts>[lane]`) — the
            // complex-butterfly twiddle broadcast and friends. Bound to the
            // FAITHFUL per-(arrangement, lane) obligations
            // (neon_lowering_proofs::all_neon_dup_elem_proofs): the SOURCE
            // replicates a lane sliced DIRECTLY from the raw D-halves, the
            // MACHINE the real `encode_neon_dup_element` over the reassembled
            // register. Every lane of BOTH emitted arrangements is pinned via
            // `aarch64_width_polymorphic_proofs`, so a wrong-lane or
            // wrong-element-size rewrite REFUTES (see
            // `neon_dup_elem_wrong_encoding_controls`).
            NeonDupElem => Some((
                "dupelem.4s lane00 broadcast-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON PER-BYTE 8-BIT REVERSE (`RBIT.16B` — the neon-bitrev
            // vectorizer's `a[i].reverse_bits()` over `[u8; N]`) — bound to the
            // FAITHFUL D-REGISTER-PAIR obligation
            // (neon_lowering_proofs::proof_neon_rbitv_16b). The SOURCE selects
            // every output bit DIRECTLY from the raw D-halves at the mirrored
            // WITHIN-byte index (8k+7-p); the MACHINE is the real
            // `encode_neon_rbit_16b` (the within-byte SWAR reversal butterfly in
            // whole-register shift/mask form) over the reassembled register.
            // STRUCTURALLY DISTINCT, so a wrong NEON instruction (identity, a
            // byte swap [REV16.8B], a 16-bit-lane bit reverse) REFUTES. Query
            // MUST be lowercase; the token is unique to this opcode. (Only the
            // `.16B` form is emitted; the `.8B` form remains fail-closed at the
            // encoder.)
            NeonRbitV => Some((
                "rbitv.16b per-byte-reverse-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON WIDENING MULTIPLY-ACCUMULATE-LONG (`SMLAL/SMLAL2/UMLAL/UMLAL2
            // .4S -> .2D`) — bound to the FAITHFUL D-REGISTER-PAIR ACCUMULATE
            // obligations (neon_lowering_proofs::all_neon_smlal_proofs, one whole-
            // register obligation per opcode with BOTH `.2D` lanes concatenated).
            // The SOURCE slices the `.2D` accumulator lane of Vd AND the two `.4S`
            // operand lanes of Vn/Vm DIRECTLY from the raw 64-bit D-halves and
            // computes `acc_j + EXT64(n_s)*EXT64(m_s)` (sign/zero-extended EXACT
            // i32xi32->i64 product); the MACHINE is the real `encode_neon_smlal`
            // over the reassembled `Concat(hi, lo)` registers. STRUCTURALLY
            // DISTINCT, so a wrong NEON instruction (sign confusion, dot-without-
            // accumulate, wrong `.4S` half, truncating mul) REFUTES. Each query is a
            // DISTINCT lowercase token unique to that opcode (verify() does
            // name.to_lowercase().contains(query) WITHOUT lowercasing the query), so
            // it cannot first-contains-collide with the udot/mul/add queries.
            NeonSmlalV => Some((
                "smlalv.2d low widening-mac-intent",
                ProofCategory::NeonLowering,
            )),
            NeonSmlal2V => Some((
                "smlal2v.2d high widening-mac-intent",
                ProofCategory::NeonLowering,
            )),
            NeonUmlalV => Some((
                "umlalv.2d low widening-mac-intent",
                ProofCategory::NeonLowering,
            )),
            NeonUmlal2V => Some((
                "umlal2v.2d high widening-mac-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON WIDENING ADD-WIDE (`UADDW/UADDW2 .4S -> .2D`) — bound to the
            // FAITHFUL D-REGISTER-PAIR obligations
            // (neon_lowering_proofs::all_neon_uaddw_proofs, one whole-register
            // obligation per opcode with BOTH `.2D` lanes concatenated). The
            // SOURCE slices the `.2D` addend lane of Vn AND the source `.4S` lane
            // of Vm DIRECTLY from the raw 64-bit D-halves and computes
            // `addend_j + zext64(m_s)` (UNSIGNED u32->u64 extension — the ISA's
            // plain three-operand wide add, Vd's prior value never read); the
            // MACHINE is the real `encode_neon_uaddw` over the reassembled
            // `Concat(hi, lo)` registers. STRUCTURALLY DISTINCT, so a wrong NEON
            // instruction (SADDW sign confusion, widen-without-addend, wrong `.4S`
            // half, truncating 32-bit add) REFUTES. Each query is a DISTINCT
            // lowercase token unique to that opcode (verify() does
            // name.to_lowercase().contains(query) WITHOUT lowercasing the query),
            // so it cannot first-contains-collide with the smlal/umlal
            // widening-mac queries ("uaddwv"/"uaddw2v" appear in no other proof
            // name).
            NeonUaddwV => Some((
                "uaddwv.2d low widening-add-intent",
                ProofCategory::NeonLowering,
            )),
            NeonUaddw2V => Some((
                "uaddw2v.2d high widening-add-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON SIGNED WIDENING ADD-WIDE (`SADDW/SADDW2 .4S -> .2D`) — bound
            // to the FAITHFUL D-REGISTER-PAIR obligations
            // (neon_lowering_proofs::all_neon_saddw_proofs, one whole-register
            // obligation per opcode with BOTH `.2D` lanes concatenated). The
            // SOURCE slices the `.2D` addend lane of Vn AND the source `.4S`
            // lane of Vm DIRECTLY from the raw 64-bit D-halves and computes
            // `addend_j + sext64(m_s)` (SIGNED i32->i64 extension — the ISA's
            // plain three-operand wide add, Vd's prior value never read); the
            // MACHINE is the real `encode_neon_saddw` over the reassembled
            // `Concat(hi, lo)` registers. STRUCTURALLY DISTINCT, so a wrong
            // NEON instruction (UADDW zext confusion — the sign axis refutes
            // both ways, see the UADDW proofs' SADDW control — widen-without-
            // addend, wrong `.4S` half, truncating 32-bit add) REFUTES. Each
            // query is a DISTINCT lowercase token unique to that opcode
            // (verify() does name.to_lowercase().contains(query) WITHOUT
            // lowercasing the query), so it cannot first-contains-collide with
            // the uaddw widening-add queries: "saddwv.2d" is not a substring of
            // any "...uaddwv.2d..." proof name and vice versa ("saddwv"/
            // "saddw2v" appear in no other proof name).
            NeonSaddwV => Some((
                "saddwv.2d low widening-add-intent",
                ProofCategory::NeonLowering,
            )),
            NeonSaddw2V => Some((
                "saddw2v.2d high widening-add-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON VECTOR MULTIPLY-ACCUMULATE (`MLA.4S`) — bound to the
            // FAITHFUL D-REGISTER-PAIR obligation
            // (neon_lowering_proofs::all_neon_mla_proofs, one whole-register
            // obligation with ALL FOUR `.4S` lanes concatenated). The SOURCE
            // slices the accumulator lane of Vd and the source lanes of Vn/Vm
            // DIRECTLY from the raw 64-bit D-halves and computes
            // `acc_i + n_i*m_i` (mod 2^32 — the ISA's truncating MLA; Vd is a
            // TIED def-use, the accumulate READS it); the MACHINE is the real
            // `encode_neon_mla` over the reassembled `Concat(hi, lo)`
            // registers. STRUCTURALLY DISTINCT, so a wrong NEON instruction
            // (MLS subtract-confusion, MUL no-accumulate, lane-swap) REFUTES.
            // The query is a DISTINCT lowercase token unique to this opcode
            // (verify() does name.to_lowercase().contains(query) WITHOUT
            // lowercasing the query): "mlav.4s" appears in no other proof name
            // — in particular NOT in the base "VectorMla -> NEON MLA.4S"
            // proofs (no 'v' between "mla" and ".4s") and NOT in the
            // smlalv/umlalv widening-mac names (those contain "mlalv", not
            // "mlav").
            NeonMlaV => Some((
                "mlav.4s lanewise mul-accumulate-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON PAIRWISE WIDENING ACCUMULATE (`UADALP .4S -> .2D`) — bound
            // to the FAITHFUL D-REGISTER-PAIR obligation
            // (neon_lowering_proofs::all_neon_uadalp_proofs, one
            // whole-register obligation with BOTH `.2D` lanes concatenated).
            // The SOURCE slices the `.2D` accumulator lane of Vd AND the
            // adjacent `.4S` source lane pair of Vn DIRECTLY from the raw
            // 64-bit D-halves and computes `acc_j + zext64(n_2j) +
            // zext64(n_2j+1)` (UNSIGNED u32->u64 extension; Vd is a TIED
            // def-use, the accumulate READS it — contrast the
            // non-accumulating NeonUaddlpV); the MACHINE is the real
            // `encode_neon_uadalp` over the reassembled `Concat(hi, lo)`
            // registers. STRUCTURALLY DISTINCT, so a wrong NEON instruction
            // (SADALP sign-confusion, UADDLP no-accumulate, wrong-pairing)
            // REFUTES. The query token "uadalpv.2d" appears in no other proof
            // name (in particular NOT in the "uaddlpv" pairwise-widen names —
            // different letter sequence).
            NeonUadalpV => Some((
                "uadalpv.2d pairwise widening-accumulate-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON FP vector arith / compare — bound to the FAITHFUL per-lane
            // FP obligations (neon_lowering_proofs::all_neon_fp_lanewise_proofs).
            // HONESTY (see the module docs there): both sides share the SMT FP
            // model, so these obligations certify the LANE PLUMBING (which bits
            // feed the op, which op, which lane width — wrong-lane-wiring and
            // op-confusion controls REFUTE), NOT independent symbolic FP-circuit
            // semantics; the FP semantic weight rests on the shared QF_FP model
            // + the silicon-validated bdefs_differential_bridge_neon_fp bridge
            // + the whole-array bit-identity differentials. These ops are
            // width-polymorphic over {.4S, .2D}: the verifier matches a
            // representative lane here while the coverage gate demands BOTH
            // arrangements discharge (see `aarch64_width_polymorphic_proofs`).
            // Queries MUST be lowercase (verify() lowercases only the name).
            NeonFaddV => Some((
                "faddv.4s lane0 lanewise-fp-intent",
                ProofCategory::NeonLowering,
            )),
            NeonFsubV => Some((
                "fsubv.4s lane0 lanewise-fp-intent",
                ProofCategory::NeonLowering,
            )),
            NeonFmulV => Some((
                "fmulv.4s lane0 lanewise-fp-intent",
                ProofCategory::NeonLowering,
            )),
            NeonFdivV => Some((
                "fdivv.4s lane0 lanewise-fp-intent",
                ProofCategory::NeonLowering,
            )),
            NeonFcmgtV => Some((
                "fcmgtv.4s lane0 lanewise-fp-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON FP-reduction-vectorizer (`neon_fpred`) ops — bound to the
            // FAITHFUL per-lane obligations (neon_lowering_proofs::
            // all_neon_fpred_proofs). DupScalarD is emitted at `.2D`; FMLA/FMLS at
            // BOTH `.2D` (f64, neon_fpred/neon_farray) AND `.4S` (f32, the
            // neon_butterfly complex butterfly and the f32 neon_fmap map chain);
            // UCVTF/SCVTF at BOTH `.2D` (i64->f64, neon_fpred) AND `.4S` (i32->f32,
            // the neon_farray IOTA fill). The verifier matches a representative
            // lane here while the coverage gate demands each emitted arrangement's
            // lanes discharge (see `aarch64_width_polymorphic_proofs`). FMLA/FMLS
            // use the SINGLE-rounding `fp.fma` (the scalar FMADD credit, lifted per
            // lane); UCVTF/SCVTF the per-lane int->FP; DupScalarD the 64-bit lane
            // bit-copy. HONESTY as the FP lane ops: LANE/OP/WIDTH plumbing over the
            // shared FP model, not an independent FP-circuit proof. Queries MUST be
            // lowercase (verify() lowercases only the name).
            NeonFmlaV => Some((
                "fmlav.2d lane0 fused-fp-intent",
                ProofCategory::NeonLowering,
            )),
            NeonFmlsV => Some((
                "fmlsv.2d lane0 fused-fp-intent",
                ProofCategory::NeonLowering,
            )),
            NeonUcvtfV => Some((
                "ucvtfv.2d lane0 int-to-fp-intent",
                ProofCategory::NeonLowering,
            )),
            NeonScvtfV => Some((
                "scvtfv.2d lane0 int-to-fp-intent",
                ProofCategory::NeonLowering,
            )),
            NeonDupScalarD => Some((
                "dupscalard.d lane0 lane-copy-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON FMLA BY ELEMENT (`neon_fmap` da*x broadcast) — bound to the
            // FAITHFUL per-(arrangement, dest, selector) obligations
            // (neon_lowering_proofs::all_neon_fmla_lane_proofs). Width-polymorphic
            // over {.4S, .2D}: the verifier matches a representative lane here
            // (the `.4S` sel0/dest0) while the global coverage gate demands the
            // complete `.4S` + `.2D` selector-by-destination matrix discharge
            // (see `aarch64_width_polymorphic_proofs`). Query MUST be lowercase.
            NeonFmlaLaneV => Some((
                "fmlalanev.4s sel0 dest0 fused-fp-intent",
                ProofCategory::NeonLowering,
            )),

            // NEON f32->f64 widening convert (FCVTL/FCVTL2) emitted by the FP
            // array-reduction vectorizer (neon_farray) — bound to the FAITHFUL
            // per-lane obligations (neon_lowering_proofs::all_neon_fcvtl_proofs).
            // Emitted ONLY at `.2D`; the verifier matches a representative lane
            // here while the coverage gate demands BOTH `.2D` lanes discharge (see
            // `aarch64_width_polymorphic_proofs`). Each output lane is the EXACT
            // `fpext` of a source f32 lane. Queries MUST be lowercase (verify()
            // lowercases only the name).
            NeonFcvtlV => Some(("fcvtlv.2d lane0 fpext-intent", ProofCategory::NeonLowering)),
            NeonFcvtl2V => Some(("fcvtl2v.2d lane0 fpext-intent", ProofCategory::NeonLowering)),

            // A generic CMP+CSET template does not establish this CSET's
            // actual condition, carrier width, or reaching flag producer, so
            // the opcode stays unmapped. A concrete CSET binds per instruction
            // to the obligation its REACHING producer and condition name
            // (`flag_consumer_query`); without a bound producer it earns
            // nothing.
            //
            // STILL `None`, and must stay so. The decoded-word `CSET` family
            // (`aarch64_value_decode_proofs`) is keyed on this instruction's own
            // destination width and condition immediate, which is not
            // opcode-wide evidence — and it is not promotion evidence either:
            // see "WHY THE DECODED-WORD `CSET` FAMILY IS NOT AN ARM HERE" below.
            // Nor does that family cover the opcode-level `coverage_gate` row:
            // the row is covered only through the NZCV producer/consumer
            // family, whose note says it is NOT a formal proof, and a failing
            // credit hook turns it RED (`coverage_gate`'s own CSET pin).
            CSet => None,

            // #67 kept-carrier checked-overflow DETECTION idioms. Bound to the
            // registered `Checked*_I64` proofs (under ProofCategory::Arithmetic)
            // whose obligation packs `overflow_b1 :: value` and whose aarch64
            // side IS the real AArch64 flag rule (V-flag sign-mismatch for ADDS/
            // SUBS; high-half-vs-sign for SMULH; high-half-vs-0 for UMULH). These
            // are FAITHFUL idiom witnesses, not the f81e45b identity class.
            //
            // ADDS/SUBS are signed/unsigned-AMBIGUOUS at the opcode level (ADDS
            // serves BOTH CheckedSadd and CheckedUadd; SUBS both Ssub and Usub).
            // An opcode-keyed arm can bind at most one idiom per opcode; binding
            // ADDS->CheckedSadd and SUBS->CheckedSsub is a sound opcode-level
            // witness that ADDS/SUBS compute value=lhs±rhs together with the
            // overflow flag. (Both the signed AND unsigned proofs are registered
            // and discharge via the strict ay gate; the signed/unsigned
            // disambiguation by the following CSET cond is a per-block refinement
            // that does not affect opcode-level coverage.)
            // Queries MUST be lowercase: the per-compile verify() lookup does
            // name.to_lowercase().contains(query) WITHOUT lowercasing the query
            // (function_verifier.rs ~2838), so a mixed-case token silently fails
            // to match there (while the coverage gate's case-insensitive audit
            // masks it). A mixed-case "CheckedSadd_I64" left these UNCOVERED in the
            // real gate, rejecting ALL checked i64 add/sub (the debug-build default)
            // and overflow-mul; the proofs (checked_overflow_proofs.rs) discharge
            // and the lowercase token uniquely matches the _i64 names.
            AddsRR => Some(("checkedsadd_i64", ProofCategory::Arithmetic)),
            SubsRR => Some(("checkedssub_i64", ProofCategory::Arithmetic)),
            // SMULH/UMULH compute the high 64 bits of the 128-bit product; the
            // Checked{S,U}mul proofs model exactly the high-half overflow
            // predicate, faithfully witnessing both the kept-carrier detection
            // expansion and the standalone smulh-idiom high-half. UMULH is
            // also the high-half step of the i128 low-product chain
            // (`select_i128_mul`); that context is credited at the coverage
            // gate's Umulh row by `checked_mul_i128_proofs` (L04-P10), while
            // this per-instance binding stays the 64-bit obligation — a named
            // deferral of that family.
            Smulh => Some(("checkedsmul_i64", ProofCategory::Arithmetic)),
            Umulh => Some(("checkedumul_i64", ProofCategory::Arithmetic)),

            // i128 carry-chain HIGH limb (ADC/SBC occur ONLY inside an i128
            // add/sub/neg chain) -> the FAITHFUL whole-chain composition proof.
            // Query MUST be lowercase: verify() does name.to_lowercase().contains(query)
            // WITHOUT lowercasing the query (function_verifier.rs lookup), so a
            // mixed-case token silently fails to match there.
            Adc => Some(("iadd_i128 whole-chain", ProofCategory::Arithmetic)),
            Sbc => Some(("isub_i128 whole-chain", ProofCategory::Arithmetic)),

            // Conditional selects (CSEL/CSINC/CSNEG): their old mapped proofs were
            // the degenerate IfConversion X==X self-equalities, RETRACTED in #62.
            // No opcode-level query exists: a concrete select binds per
            // instruction to the obligation of its own operation, width and
            // condition over its REACHING producer (`flag_consumer_query`), and
            // an unbound select still blocks promotion. CSINV has no proof.
            Csel | Csinc | Csneg => None,

            // Scalar FP abs / sqrt / div: bound to the registered FloatingPoint
            // value proofs whose machine side IS that exact instruction. These
            // are width-polymorphic over {F32, F64}; the verifier matches a
            // representative width here while the coverage gate demands BOTH the
            // F32 and F64 proofs discharge (see `aarch64_width_polymorphic_proofs`).
            FabsRR => Some(("fabs", ProofCategory::FloatingPoint)),
            FsqrtRR => Some(("fsqrt", ProofCategory::FloatingPoint)),
            FdivRR => Some(("fdiv", ProofCategory::FloatingPoint)),

            // The FCSEL templates model a particular CMP-W-selector,#0 + mux
            // composition, not an arbitrary emitted FCSEL. An opcode-only name
            // lookup cannot bind the actual S/D width, condition, source arms,
            // or reaching NZCV producer to that composition (nor to source
            // Select operands). Keep all templates as diagnostic model evidence,
            // but deny runtime credit until those correspondences are checked.
            // Even a formally discharged template would not supply this binding.
            FcselRR => None,

            // No proof for these opcodes (yet)
            _ => None,
        }
    }

    /// Map a concrete instruction to a proof search query and category.
    ///
    /// This keeps the old opcode-level mapping as a fallback, but lets
    /// generated frame/spill forms select stronger operand-sensitive proof
    /// families when the operands identify stack-slot spill/reload code.
    ///
    /// Proof families that need surrounding instruction provenance, such as
    /// scalarized STP spills, are handled by
    /// `inst_to_proof_query_in_block_for_source`.
    pub fn inst_to_proof_query(inst: &MachInst) -> Option<(&'static str, ProofCategory)> {
        if register_alu_extra_operand_refusal_reason(inst).is_some() {
            return None;
        }
        Self::generated_stack_slot_spill_or_reload_query(inst)
            .or_else(|| Self::generated_emergency_spill_slot_address_query(inst))
            .or_else(|| Self::generated_frame_address_materialization_query(inst))
            .or_else(|| Self::generated_fp_sp_relative_addressing_query(inst))
            .or_else(|| Self::operand_sensitive_or_opcode_query(inst))
    }

    /// [`Self::inst_to_proof_query_in_block_for_source`] with no replayed LIR
    /// source: the form the direct-query tests use, which have none.
    #[cfg(test)]
    fn inst_to_proof_query_in_block(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
        inst: &MachInst,
    ) -> Option<(&'static str, ProofCategory)> {
        Self::inst_to_proof_query_in_block_for_source(func, block_insts, block_pos, inst, None)
    }

    /// The walk's in-block query. `source` is the TV-1 replayed LIR instruction
    /// `inst` was stamped from, when the walk has one; it is read only by the
    /// NZCV-consumer slot ([`Self::nzcv_consumer_query`]).
    fn inst_to_proof_query_in_block_for_source(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
        inst: &MachInst,
        source: Option<&LirSourceInst>,
    ) -> Option<(&'static str, ProofCategory)> {
        if register_alu_extra_operand_refusal_reason(inst).is_some() {
            return None;
        }
        Self::generated_stack_slot_spill_or_reload_query(inst)
            .or_else(|| Self::generated_stp_spill_scalarization_query(func, block_insts, block_pos))
            .or_else(|| Self::generated_emergency_spill_slot_address_query(inst))
            .or_else(|| Self::generated_frame_address_materialization_query(inst))
            .or_else(|| Self::generated_fp_sp_relative_addressing_query(inst))
            .or_else(|| Self::i128_carry_chain_low_limb_query(func, block_insts, block_pos))
            .or_else(|| {
                Self::checked_i128_carry_chain_high_limb_query(func, block_insts, block_pos)
            })
            .or_else(|| Self::tst_nzcv_consumer_query(func, block_insts, block_pos))
            .or_else(|| Self::nzcv_consumer_query(func, block_insts, block_pos, inst, source))
            .or_else(|| Self::operand_sensitive_or_opcode_query(inst))
    }

    /// The NZCV-consumer slot of the in-block chain: the machine-level
    /// reaching-producer binding (`flag_consumer_query`), gated by the
    /// source-bound binding (`nzcv_consumer_source_bound_query`) wherever the
    /// walk has the replayed source that binding is written for.
    ///
    /// `flag_consumer_query` names its family member from the condition the
    /// EMITTED instruction carries and the producer that reaches it, which are
    /// facts about the machine code alone: a `CSET` whose condition was mutated
    /// away from its `icmp slt` source still names a (true, different)
    /// `Icmp_SGT_I64` theorem. So for a `CSET` stamped from an `IntCmp` or
    /// `Overflow` source, or a `CSEL` stamped from a `Select` or `Shift`
    /// source ([`Self::is_source_bound_nzcv_consumer`]), the source-bound
    /// binding DECIDES: when it refuses (source condition, emission count,
    /// checked-overflow signedness, reaching-producer kind, carrier widths,
    /// i128 shift-chain wiring) the slot names nothing and the row is refused
    /// as unmapped; when it accepts, the machine-level name is kept, or the
    /// source-bound one when the machine-level binding has none.
    ///
    /// With no source (`ProvenanceXCheckMode::Off`, no `lir_source`, an
    /// unstamped instruction, and every source-free caller), or a source of
    /// any other class (an `Fcmp`-sourced `CSET`, among others), the
    /// machine-level binding stands unchanged. Since E0.2 neither binding is
    /// per-instruction credit: the walk refuses a registry theorem found by
    /// name, so this decides only what the refusal names.
    fn nzcv_consumer_query(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
        inst: &MachInst,
        source: Option<&LirSourceInst>,
    ) -> Option<(&'static str, ProofCategory)> {
        let machine = Self::flag_consumer_query(func, block_insts, block_pos);
        let Some(source) =
            source.filter(|source| Self::is_source_bound_nzcv_consumer(inst, source))
        else {
            return machine;
        };
        let bound = Self::nzcv_consumer_source_bound_query(
            func,
            block_insts,
            block_pos,
            inst,
            Some(source),
        )?;
        Some(machine.unwrap_or(bound))
    }

    /// Bind a CSET or CSEL/CSINC/CSNEG to the obligation named by its own
    /// operation, width and condition and by the kind and width of the NZCV
    /// producer that REACHES it inside its block
    /// (`aarch64_flag_consumer_proofs::reaching_flag_producer`). A consumer
    /// whose producer is absent from the block, hidden behind a call, opaque
    /// pseudo or implicit NZCV writer, malformed, or of an unmodeled kind, or
    /// whose condition has no predicate after that producer, earns nothing.
    fn flag_consumer_query(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
    ) -> Option<(&'static str, ProofCategory)> {
        use crate::aarch64_flag_consumer_proofs as flags;
        let inst = Self::inst_at_block_pos(func, block_insts, block_pos)?;
        match inst.opcode {
            AArch64Opcode::CSet => Self::cset_producer_query(
                func,
                block_insts,
                block_pos,
                flags::TransparencyPolicy::TargetFlagModel,
            ),
            AArch64Opcode::Csel | AArch64Opcode::Csinc | AArch64Opcode::Csneg => {
                flags::select_query(func, block_insts, block_pos)
            }
            _ => None,
        }
    }

    /// The CSET at `pos` cites the condition obligation of its reaching
    /// producer: `Icmp_<cc>_I<w>` after CMP, `TST w<w>: <cc>` after TST, the
    /// FCMP -> CSET obligation after FCMP, the checked-i64 overflow idiom after
    /// an X-width ADDS/SUBS, and the checked-i128 overflow bit after an
    /// adjacent ADCS/SBCS high limb. Anything else fails closed.
    fn cset_producer_query(
        func: &MachFunction,
        block_insts: &[InstId],
        pos: usize,
        policy: crate::aarch64_flag_consumer_proofs::TransparencyPolicy,
    ) -> Option<(&'static str, ProofCategory)> {
        use crate::aarch64_flag_consumer_proofs as flags;
        use AArch64Opcode::{Adcs, AddsRR, CSet, CmpRI, CmpRR, Fcmp, Sbcs, SubsRR, Tst};
        let inst = Self::inst_at_block_pos(func, block_insts, pos)?;
        if inst.opcode != CSet {
            return None;
        }
        let (_, cc) = flags::consumer_shape(inst)?;
        let (producer_pos, producer) =
            flags::reaching_flag_producer(func, block_insts, pos, policy).ok()?;
        match producer.opcode {
            CmpRR | CmpRI => Self::icmp_family_query(
                PreciseFamily::Icmp,
                i64::from(cc),
                flags::cmp_width(producer)?,
            )
            .map(|query| (query, ProofCategory::Comparison)),
            Tst => Self::tst_condition_query(flags::tst_width(producer)?, i64::from(cc))
                .map(|query| (query, ProofCategory::CmpCombine)),
            Fcmp => flags::fcmp_cset_query(flags::fcmp_width(producer)?, cc)
                .map(|query| (query, flags::FLAG_CONSUMER_CATEGORY)),
            AddsRR | SubsRR => {
                let all_x = producer.operands.len() == 3
                    && producer
                        .operands
                        .iter()
                        .all(|op| flags::gpr_operand(op).is_some_and(|(width, _)| width == 64));
                if !all_x {
                    return None;
                }
                // isel CondCode encoding: HS=2 LO=3 VS=6.
                let query = match (producer.opcode, cc) {
                    (AddsRR, 6) => "checkedsadd_i64",
                    (AddsRR, 2) => "checkeduadd_i64",
                    (SubsRR, 6) => "checkedssub_i64",
                    (SubsRR, 3) => "checkedusub_i64",
                    _ => return None,
                };
                Some((query, ProofCategory::Arithmetic))
            }
            Adcs | Sbcs if producer_pos + 1 == pos => {
                Self::checked_i128_carry_chain_high_limb_query(func, block_insts, producer_pos)
            }
            _ => None,
        }
    }

    /// Bind move-wide proofs only to concrete forms accepted by the encoder.
    ///
    /// MOVZ is restricted to hw0 because its higher-halfword identity
    /// obligations were retracted under #62. MOVI is the canonical two-operand
    /// MOVZ-at-hw0 pseudo. MOVK and MOVN retain their architectural shift
    /// ranges and bind per-(width, shift) to their halfword-splice /
    /// inverted-field obligations. Invalid shapes never fall back to
    /// opcode-wide proof credit.
    fn operand_sensitive_or_opcode_query(inst: &MachInst) -> Option<(&'static str, ProofCategory)> {
        // The register copies (MovR, MOVWrr, MOVXrr, the scalar and cross-class
        // FMOVs), SMULL, BFM, RBIT, ADD #imm12 LSL #12, MRS and the
        // half-precision FCVTs bind to exactly one decoded-word value form
        // (`aarch64_value_decode_proofs`), chosen from the operands' register
        // classes and immediates: a copy only between numbered registers of a
        // modeled width pairing (plus MOV Xd, SP), MOVWrr/MOVXrr at the width
        // their opcode fixes, SMULL only as the signed 32x32->64 form, BFM only
        // in its bitfield-insert family with matching widths, RBIT per width,
        // the shifted ADD per width with an imm12 in 0..=4095 and no zero
        // register, MRS only for TPIDR_EL0. Any other shape of these opcodes
        // refuses and never falls back to an opcode-wide query.
        // NEON AND/ORR/EOR/BIC/NOT bind their lanewise obligation only in
        // the 16B shape (Q registers, no selector; an ORR of two different
        // registers), whose word ENC-5 decodes and field-checks. The 8B
        // shapes bind nothing: the obligation does not state the zeroed upper
        // half. Every other ORR (vector) shape goes through the
        // decoded-value binding below, which binds only the 16B register copy.
        if let Some(query) = crate::aarch64_value_decode_proofs::neon_bitwise_16b_bound_query(inst)
        {
            return Some((query, ProofCategory::NeonLowering));
        }
        if let Some(bound) = crate::aarch64_value_decode_proofs::a64_value_bound_form(inst) {
            return bound.map(|form| (form.query(), form.category()));
        }
        // UADDLP/SADDLP share one opcode apiece across the two widening
        // arrangements emitted by the vectorizers. Bind each concrete
        // instruction to the theorem for its exact input arrangement; otherwise
        // the legacy opcode-level representative (`.16B->.8H`) can incorrectly
        // credit an emitted `.8H->.4S` instruction. Keep the accepted shapes in
        // lock-step with the encoder: [Vd:Fpr128, Vn:Fpr128, Imm(1|3)]. Any
        // malformed arity, register class, or arrangement fails closed instead
        // of falling back to the opcode-wide query.
        if matches!(
            inst.opcode,
            AArch64Opcode::NeonUaddlpV | AArch64Opcode::NeonSaddlpV
        ) {
            if inst.operands.len() != 3 {
                return None;
            }
            let is_fpr128 = |op: &MachOperand| match op {
                MachOperand::VReg(v) => v.class == trust_cg_ir::RegClass::Fpr128,
                MachOperand::PReg(p) => preg_class(*p) == trust_cg_ir::RegClass::Fpr128,
                _ => false,
            };
            if !is_fpr128(inst.operands.first()?) || !is_fpr128(inst.operands.get(1)?) {
                return None;
            }
            let MachOperand::Imm(arrangement) = inst.operands.get(2)? else {
                return None;
            };
            return match (inst.opcode, *arrangement) {
                (AArch64Opcode::NeonUaddlpV, 1) => Some((
                    "uaddlpv.16b->.8h lanewise-intent",
                    ProofCategory::NeonLowering,
                )),
                (AArch64Opcode::NeonUaddlpV, 3) => Some((
                    "uaddlpv.8h->.4s lanewise-intent",
                    ProofCategory::NeonLowering,
                )),
                (AArch64Opcode::NeonSaddlpV, 1) => Some((
                    "saddlpv.16b->.8h lanewise-intent",
                    ProofCategory::NeonLowering,
                )),
                (AArch64Opcode::NeonSaddlpV, 3) => Some((
                    "saddlpv.8h->.4s lanewise-intent",
                    ProofCategory::NeonLowering,
                )),
                _ => None,
            };
        }

        // FCMP has no destination: [Sn, Sm] or [Dn, Dm]. Bind the concrete
        // operand width to its complete packed-NZCV obligation (the decoded
        // FCMP word's integer-only FPCompare against the TrustIR relations).
        // Half precision, mixed widths, immediates and malformed arity refuse.
        if inst.opcode == AArch64Opcode::Fcmp {
            return crate::aarch64_flag_consumer_proofs::fcmp_query(inst);
        }

        // SWP (atomic exchange) — bound to the RETAINED memory-effect proof
        // `SWP_I{32,64}: mem[addr] = operand`, WIDTH-CORRECTLY.
        //
        // The opcode-wide arm deliberately leaves `Swp*` unmapped, because the
        // opcode alone cannot say which width was emitted and the credit must not
        // be wrong: `encode_lse_atomic` derives the access size from Rt's register
        // class (W -> word, X -> dword) EXCEPT for the narrow forms, which carry a
        // 4th access-size immediate precisely because i8/i16/i32 all use W
        // registers. There is no `SWP_I8`/`SWP_I16` memory obligation, so a narrow
        // SWP must FAIL CLOSED rather than be credited to the 32-bit theorem —
        // the same hazard the NEON arrangement arm above exists to prevent.
        //
        // Operand shape, from `encode_lse_atomic`: [Rs (value swapped IN),
        // Rt (old value OUT), Rn (address)]. Any other arity, a mismatched
        // value/result width, a non-64-bit address, or a narrow form falls closed
        // instead of reaching the opcode-wide query.
        //
        // Strength: this is the MEMORY EFFECT only (`mem[addr] = operand`). The
        // RETURNED old value stays on the shared unfaithful-load debt, exactly as
        // it does for the `Ldadd*` family bound below — the `": returns old
        // value"` obligations were retracted in #62 as degenerate (both sides route
        // through `encode_load_le`, so X==X) and are NOT what is named here.
        //
        // E0.2: like every query this function returns, the binding NAMES the
        // theorem in the walk's refusal (`withdrawn_registry_credit`); it is not
        // per-instruction credit. What it pins is the width discrimination: a
        // narrow or malformed SWP names nothing at all.
        if matches!(
            inst.opcode,
            AArch64Opcode::Swp | AArch64Opcode::Swpa | AArch64Opcode::Swpal | AArch64Opcode::Swpl
        ) {
            // A 4th operand is the narrow (byte/half) access-size immediate.
            if inst.operands.len() != 3 {
                return None;
            }
            let value_width = operand_reg_width_bits(inst.operands.first()?)?;
            if operand_reg_width_bits(inst.operands.get(1)?)? != value_width {
                return None;
            }
            if operand_reg_width_bits(inst.operands.get(2)?)? != 64 {
                return None;
            }
            return match value_width {
                32 => Some(("swp_i32: mem", ProofCategory::AtomicOperations)),
                64 => Some(("swp_i64: mem", ProofCategory::AtomicOperations)),
                _ => None,
            };
        }

        // DMB binds to the interleaving barrier obligation for the barrier kind
        // it ACTUALLY encodes, read off its CRm immediate — not to a single
        // opcode-wide "there is a fence here" credit.
        //
        // This matters because the obligations are load-load ordering: ISH (0xB,
        // full) and ISHLD (0x9, load barrier) both provide it, ISHST (0xA, store
        // barrier) does NOT — `ishst_does_not_order_loads_control` is refuted.
        // Crediting any DMB for any ordering would re-create exactly the #62
        // defect in a new place, so every other CRm (ISHST included) returns
        // None and fails closed rather than falling back to an opcode-wide query.
        if inst.opcode == AArch64Opcode::Dmb {
            if inst.operands.len() != 1 {
                return None;
            }
            let MachOperand::Imm(crm) = inst.operands.first()? else {
                return None;
            };
            return match crm {
                0xB => Some(("dmb_ish: orders", ProofCategory::AtomicOperations)),
                0x9 => Some(("dmb_ishld: orders", ProofCategory::AtomicOperations)),
                _ => None,
            };
        }

        // TST has no destination: [Rn, Rm] or [Rn, #logical-imm]. Bind the
        // concrete source width to the complete packed-NZCV theorem. Invalid
        // arity, SP, non-GPR/cross-width registers, and unencodable immediates
        // must not fall back to the opcode-wide query.
        if inst.opcode == AArch64Opcode::Tst {
            if inst.operands.len() != 2 {
                return None;
            }
            let tst_reg_width = |op: &MachOperand| match op {
                MachOperand::VReg(v)
                    if matches!(
                        v.class,
                        trust_cg_ir::RegClass::Gpr32 | trust_cg_ir::RegClass::Gpr64
                    ) =>
                {
                    Some(v.class.size_bits())
                }
                MachOperand::PReg(p) if *p != SP && *p != WSP => {
                    let class = preg_class(*p);
                    matches!(
                        class,
                        trust_cg_ir::RegClass::Gpr32 | trust_cg_ir::RegClass::Gpr64
                    )
                    .then(|| class.size_bits())
                }
                MachOperand::Special(SpecialReg::WZR) => Some(32),
                MachOperand::Special(SpecialReg::XZR) => Some(64),
                _ => None,
            };
            let width = tst_reg_width(inst.operands.first()?)?;
            match inst.operands.get(1)? {
                MachOperand::Imm(mask)
                    if trust_cg_opt::const_materialize::is_logical_immediate(
                        *mask as u64,
                        width,
                    ) => {}
                rm if tst_reg_width(rm) == Some(width) => {}
                _ => return None,
            }
            return match width {
                32 => Some(("tst packed nzcv w32", ProofCategory::CmpCombine)),
                64 => Some(("tst packed nzcv w64", ProofCategory::CmpCombine)),
                _ => None,
            };
        }

        // ROR-immediate shares one opcode across W and X. Bind the concrete
        // instruction to the matching width's rotate theorems
        // (`all_ror_immediate_proofs`) and accept only the reg-reg-imm form
        // the rotate recognizer emits, with the ROR amount inside [1, width).
        // Malformed shapes never fall back to opcode-wide credit.
        if inst.opcode == AArch64Opcode::RorRI {
            if inst.operands.len() != 3 {
                return None;
            }
            let dst_width = operand_reg_width_bits(inst.operands.first()?)?;
            if !matches!(dst_width, 32 | 64)
                || operand_reg_width_bits(inst.operands.get(1)?)? != dst_width
            {
                return None;
            }
            let MachOperand::Imm(k) = inst.operands.get(2)? else {
                return None;
            };
            if *k < 1 || *k >= i64::from(dst_width) {
                return None;
            }
            let query = if dst_width == 64 {
                "rorri_i64"
            } else {
                "rorri_i32"
            };
            return Some((query, ProofCategory::BitwiseShift));
        }
        // UBFM/SBFM share one opcode across W and X. Bind the concrete
        // instruction to the matching symbolic-width theorem and accept only
        // the non-wrapping extract form emitted by isel and LsrAndUbfx. The old
        // opcode-only fallback silently chose the first (w32) proof even for an
        // X-form instruction and credited malformed operand-less stubs.
        if matches!(inst.opcode, AArch64Opcode::Ubfm | AArch64Opcode::Sbfm) {
            if inst.operands.len() != 4 {
                return None;
            }
            let dst_width = operand_reg_width_bits(inst.operands.first()?)?;
            if !matches!(dst_width, 32 | 64)
                || operand_reg_width_bits(inst.operands.get(1)?)? != dst_width
            {
                return None;
            }
            let MachOperand::Imm(immr) = inst.operands.get(2)? else {
                return None;
            };
            let MachOperand::Imm(imms) = inst.operands.get(3)? else {
                return None;
            };
            if *immr < 0 || *imms < *immr || *imms >= i64::from(dst_width) {
                return None;
            }
            return match (inst.opcode, dst_width) {
                (AArch64Opcode::Ubfm, 32) => {
                    Some(("ubfm extract w32", ProofCategory::ExtensionTruncation))
                }
                (AArch64Opcode::Ubfm, 64) => {
                    Some(("ubfm extract w64", ProofCategory::ExtensionTruncation))
                }
                (AArch64Opcode::Sbfm, 32) => {
                    Some(("sbfm extract w32", ProofCategory::ExtensionTruncation))
                }
                (AArch64Opcode::Sbfm, 64) => {
                    Some(("sbfm extract w64", ProofCategory::ExtensionTruncation))
                }
                _ => None,
            };
        }

        let (min_operands, max_operands, allow_nonzero_shift, query) = match inst.opcode {
            AArch64Opcode::MovI => (2, 2, false, Some("movz #imm16, lsl #0")),
            AArch64Opcode::Movz => (2, 3, false, Some("movz #imm16, lsl #0")),
            AArch64Opcode::Movn => (2, 3, true, None),
            AArch64Opcode::Movk => (2, 3, true, None),
            AArch64Opcode::MOVZWi | AArch64Opcode::MOVZXi => {
                (2, 2, false, Some("movz #imm16, lsl #0"))
            }
            _ => {
                return Self::opcode_to_proof_query(inst.opcode);
            }
        };

        if !(min_operands..=max_operands).contains(&inst.operands.len()) {
            return None;
        }
        let is_w_form = match inst.operands.first() {
            Some(MachOperand::VReg(v)) => match v.class {
                trust_cg_ir::RegClass::Gpr32 => true,
                trust_cg_ir::RegClass::Gpr64 => false,
                _ => return None,
            },
            Some(MachOperand::PReg(p)) if *p != SP && *p != WSP => match preg_class(*p) {
                trust_cg_ir::RegClass::Gpr32 => true,
                trust_cg_ir::RegClass::Gpr64 => false,
                _ => return None,
            },
            Some(MachOperand::Special(SpecialReg::WZR)) => true,
            Some(MachOperand::Special(SpecialReg::XZR)) => false,
            _ => return None,
        };
        if !matches!(
            inst.operands.get(1),
            Some(MachOperand::Imm(imm)) if (0..=0xFFFF).contains(imm)
        ) {
            return None;
        }
        let shift = match inst.operands.get(2) {
            None => 0,
            Some(MachOperand::Imm(shift)) => *shift,
            Some(_) => return None,
        };
        if !matches!(shift, 0 | 16 | 32 | 48) {
            return None;
        }
        if is_w_form && shift > 16 {
            return None;
        }
        if inst.opcode == AArch64Opcode::MOVZWi && !is_w_form {
            return None;
        }
        if inst.opcode == AArch64Opcode::MOVZXi && is_w_form {
            return None;
        }
        if !allow_nonzero_shift && shift != 0 {
            return None;
        }
        // MOVN binds to the (width, halfword)-SPECIFIC inverted-field obligation
        // rather than an opcode-wide credit: the X-form proofs pin the inverted
        // halfword AND the forced-ones remainder at exactly this slot, and the
        // W-form proofs additionally pin the 32-bit complement followed by
        // zero-extension (upper 32 bits zero) — the width semantics the X-form
        // theorem cannot honestly supply. An illegal W-form shift finds no
        // query and never inherits an X slot's credit.
        if inst.opcode == AArch64Opcode::Movn {
            let width = if is_w_form { 32 } else { 64 };
            let query = crate::const_materialize_proofs::movn_halfword_query(width, shift as u32)?;
            return Some((query, ProofCategory::ConstantMaterialization));
        }
        if inst.opcode == AArch64Opcode::Movk {
            // A MOVK to WZR/XZR architecturally discards the write; the splice
            // theorem models a REAL register destination, so a zero-register
            // MOVK earns no credit (review hardening — no producer emits it,
            // and a malformed dead-splice chain must not verify).
            if matches!(
                inst.operands.first(),
                Some(MachOperand::Special(SpecialReg::WZR | SpecialReg::XZR))
            ) {
                return None;
            }
            // MOVK binds to the (width, halfword)-SPECIFIC splice obligation
            // rather than an opcode-wide credit: the proof pins BOTH the 16
            // written bits AND the preservation of the remaining bits at
            // exactly this slot, so a MOVK emitted at the wrong halfword (or an
            // illegal W-form shift, already rejected above) can never inherit
            // another slot's credit. The splice obligations are FAITHFUL per
            // #62: the trust-ir side is an independent concat/extract splice,
            // the machine side the encoder's shift/mask semantics, so a wrong
            // shift or mask REFUTES.
            let width = if is_w_form { 32 } else { 64 };
            let query = crate::const_materialize_proofs::movk_halfword_query(width, shift as u32)?;
            return Some((query, ProofCategory::ConstantMaterialization));
        }
        Some((query?, ProofCategory::ConstantMaterialization))
    }

    /// Disambiguate the SHARED `AddsRR`/`SubsRR` low limb: it is globally bound to
    /// the i64 `CheckedSadd_I64`/`CheckedSsub_I64` idiom (ADDS;CSET), but in an
    /// i128 add/sub it is the carry-GENERATING low limb (ADDS;ADC / SUBS;SBC).
    /// `Adc`/`Sbc` are emitted ONLY as i128 carry-chain high limbs, so
    /// `next == Adc/Sbc` UNIQUELY identifies the i128-add/sub low limb → credit it
    /// to the faithful whole-chain composition proof. Else fall through unchanged
    /// (the i64 checked-add/sub path is preserved).
    fn i128_carry_chain_low_limb_query(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
    ) -> Option<(&'static str, ProofCategory)> {
        use AArch64Opcode::{Adc, Adcs, AddsRR, Sbc, Sbcs, SubsRR};
        let cur = Self::inst_at_block_pos(func, block_insts, block_pos)?;
        let next = Self::inst_at_block_pos(func, block_insts, block_pos + 1)?;
        match (cur.opcode, next.opcode) {
            (AddsRR, Adc) => Some(("iadd_i128 whole-chain", ProofCategory::Arithmetic)),
            (SubsRR, Sbc) => Some(("isub_i128 whole-chain", ProofCategory::Arithmetic)),
            // CHECKED-i128 low limb: `next == Adcs/Sbcs` uniquely identifies
            // the flag-setting checked chain. The low limb's role — low value
            // plus carry-out — is exactly what the faithful VALUE whole-chain
            // composition proof models (the flag-setting variants compute the
            // identical value chain, S bit aside); the overflow bit is the
            // high limb's own obligation.
            (AddsRR, Adcs) => Some(("iadd_i128 whole-chain", ProofCategory::Arithmetic)),
            (SubsRR, Sbcs) => Some(("isub_i128 whole-chain", ProofCategory::Arithmetic)),
            _ => None,
        }
    }

    /// The checked-i128 overflow-bit obligation for a chain whose LOW-limb
    /// opcode is `low_opc` and whose CSET sits at `cset_pos`. The CSET's
    /// condition disambiguates signed (VS) from unsigned (HS carry / LO
    /// borrow); anything else fails closed. The high limb (`Adcs`/`Sbcs`)
    /// binds through here and never without its materializing CSET.
    fn checked_i128_chain_query_from_cset(
        func: &MachFunction,
        block_insts: &[InstId],
        cset_pos: usize,
        low_opc: AArch64Opcode,
    ) -> Option<(&'static str, ProofCategory)> {
        use AArch64Opcode::{AddsRR, CSet, SubsRR};
        let cset = Self::inst_at_block_pos(func, block_insts, cset_pos)?;
        if cset.opcode != CSet {
            return None;
        }
        let cc_pos = Self::nzcv_consumer_cc_pos(CSet)?;
        let MachOperand::Imm(cc) = cset.operands.get(cc_pos)? else {
            return None;
        };
        // isel CondCode encoding: HS=2 LO=3 VS=6.
        let query = match (low_opc, *cc) {
            (AddsRR, 6) => "checkedsadd_i128 overflow bit",
            (AddsRR, 2) => "checkeduadd_i128 overflow bit",
            (SubsRR, 6) => "checkedssub_i128 overflow bit",
            (SubsRR, 3) => "checkedusub_i128 overflow bit",
            _ => return None,
        };
        Some((query, ProofCategory::Arithmetic))
    }

    /// Bind the flag-setting high limb `Adcs`/`Sbcs` to its checked-i128
    /// overflow-bit obligation. The chain contract keeps the three
    /// instructions strictly adjacent, so `prev` must be the matching
    /// flag-setting low limb and `next` the CSET whose condition picks the
    /// signed/unsigned obligation. Anything else fails closed.
    fn checked_i128_carry_chain_high_limb_query(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
    ) -> Option<(&'static str, ProofCategory)> {
        use AArch64Opcode::{Adcs, AddsRR, Sbcs, SubsRR};
        let cur = Self::inst_at_block_pos(func, block_insts, block_pos)?;
        let low_opc = match cur.opcode {
            Adcs => AddsRR,
            Sbcs => SubsRR,
            _ => return None,
        };
        let prev_pos = block_pos.checked_sub(1)?;
        let prev = Self::inst_at_block_pos(func, block_insts, prev_pos)?;
        if prev.opcode != low_opc {
            return None;
        }
        Self::checked_i128_chain_query_from_cset(func, block_insts, block_pos + 1, low_opc)
    }

    /// Standalone-TST credit is CONTEXT-SENSITIVE: bind the TST to the
    /// registered per-condition NZCV-effect obligations of the conditions its
    /// consumers actually read (`proof_tst_nzcv_effect`, names
    /// "TST w{64,32}: {cc} …").
    ///
    /// TST alone does not identify which flag combination matters, and
    /// opcode-wide credit from one condition's theorem is the unfaithful
    /// inheritance #62 retracted. The binding therefore collects EVERY
    /// consumer of THIS TST's flags — not just the first (review finding:
    /// CSel-family consumers do not write NZCV, so a second consumer reading
    /// an uncovered condition would otherwise escape unvouched) — scanning
    /// forward (bounded) while the flags are live:
    ///
    ///   * consumer candidates: the `CSet`/`CSEL` family (incl. `FcselRR` —
    ///     the FP select reads NZCV exactly like `Csel`) and conditional
    ///     branches `BCond`/`Bcc` (the unfusible multi-bit-mask `TST #m; B.cc`
    ///     shape TBZ/TBNZ cannot express). Each recorded condition must map
    ///     to a registered obligation via `tst_condition_query`, else fail
    ///     closed.
    ///   * a flag WRITER kills the TST's NZCV: collection ends successfully.
    ///   * fail closed on anything not provably flag-transparent while the
    ///     flags are live: an `Adc`/`Sbc` C-reader, a call (the callee may or
    ///     may not preserve NZCV), a non-Nop pseudo (later expansion could
    ///     touch flags), a malformed condition operand, or the scan cap.
    ///   * if control can LEAVE the block with the flags still live (any
    ///     branch/terminator, or block end), every successor path must be
    ///     provably NZCV-dead-on-entry (`nzcv_dead_on_entry`) — otherwise a
    ///     cross-block consumer would escape the net. A conditional-branch
    ///     consumer's TAKEN edge carries the flags out unconditionally, so
    ///     its presence forces the all-successors check even when a LATER
    ///     in-block flags writer kills the fallthrough copy (review round 2;
    ///     the target operand is a resolved immediate post-layout, so the
    ///     superset over `block.succs` stands in for the exact edge); the
    ///     scan continues past a conditional-branch consumer only to find
    ///     the fallthrough.
    ///
    /// The TST cites the first consumer's obligation (all recorded conditions
    /// are rows of the same per-width family and every one is required to be
    /// covered). A TST with NO consumer earns nothing.
    fn tst_nzcv_consumer_query(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
    ) -> Option<(&'static str, ProofCategory)> {
        use trust_cg_ir::target_info::{AArch64Target, TargetInfo};
        const TST_CONSUMER_SCAN_CAP: usize = 16;
        let cur = Self::inst_at_block_pos(func, block_insts, block_pos)?;
        if cur.opcode != AArch64Opcode::Tst {
            return None;
        }
        // Width of the tested value = register width of the first operand
        // (TST is emitted as `[rn, rm]` or `[rn, #imm]`; both flag models are
        // width-specific).
        let width = operand_reg_width_bits(cur.operands.first()?)?;

        let mut ccs: Vec<i64> = Vec::new();
        let mut flags_die_in_block = false;
        // A conditional-branch CONSUMER carries NZCV out on its taken edge
        // REGARDLESS of what the fallthrough path later does to the flags
        // (review round 2: an in-block flags writer after the BCond must not
        // skip the successor check). Post-layout the branch target operand is
        // a resolved immediate, not `MachOperand::Block`, so the taken edge
        // cannot be extracted per-instruction — instead this flag forces the
        // CONSERVATIVE superset check over ALL of the block's successors (the
        // taken edge is necessarily among them).
        let mut cond_branch_consumer = false;
        let mut pos = block_pos + 1;
        loop {
            if pos > block_pos + TST_CONSUMER_SCAN_CAP {
                // Flags still live past the scan bound: unknown readers may
                // follow. Fail closed.
                return None;
            }
            let Some(inst) = Self::inst_at_block_pos(func, block_insts, pos) else {
                // Block ended with the flags live: treat as live-out and
                // require the successor check below.
                break;
            };
            if let Some(cc_pos) = Self::nzcv_consumer_cc_pos(inst.opcode) {
                let MachOperand::Imm(found) = inst.operands.get(cc_pos)? else {
                    return None;
                };
                ccs.push(*found);
                if matches!(inst.opcode, AArch64Opcode::BCond | AArch64Opcode::Bcc) {
                    cond_branch_consumer = true;
                }
                // Consumers do not write NZCV — keep collecting (a
                // conditional-branch consumer is followed by its fallthrough
                // branch, which ends the scan as a terminator below).
                pos += 1;
                continue;
            }
            let op = inst.opcode;
            if <AArch64Target as TargetInfo>::writes_flags(op) {
                // The TST's NZCV is shadowed from here on; nothing later on
                // the FALLTHROUGH path can read it (taken edges recorded
                // above are still checked below).
                flags_die_in_block = true;
                break;
            }
            if <AArch64Target as TargetInfo>::reads_flags(op)
                || inst.is_call()
                || (op.is_pseudo() && op != AArch64Opcode::Nop)
            {
                return None;
            }
            if inst.is_branch() || inst.is_terminator() {
                // Control leaves the block with the flags live.
                break;
            }
            pos += 1;
        }

        if !flags_die_in_block || cond_branch_consumer {
            // NZCV is (potentially) LIVE-OUT — on the fallthrough when no
            // in-block writer killed it, and on a conditional-branch
            // consumer's taken edge UNCONDITIONALLY. Every successor path
            // must be provably flag-dead-on-entry, or an unseen consumer
            // escapes. (When the flags die in-block this over-approximates
            // the taken edge with all successors — conservative, sound.)
            let block = func
                .blocks
                .iter()
                .find(|b| std::ptr::eq(b.insts.as_slice(), block_insts))?;
            let mut visited = std::collections::HashSet::new();
            for &succ in &block.succs {
                if !Self::nzcv_dead_on_entry(func, succ, &mut visited) {
                    return None;
                }
            }
        }

        // EVERY consumer's condition must have a registered obligation; the
        // TST cites the first (any uncovered condition fails the whole TST
        // closed). Zero consumers: a dead TST earns nothing.
        let queries = ccs
            .iter()
            .map(|&cc| Self::tst_condition_query(width, cc))
            .collect::<Option<Vec<&'static str>>>()?;
        let first = *queries.first()?;
        Some((first, ProofCategory::CmpCombine))
    }

    /// NZCV-consumer candidates for the TST binding, with the operand index
    /// of the ISel `CondCode` immediate each carries (isel.rs encoding:
    /// EQ=0 NE=1 HS=2 LO=3 MI=4 PL=5 VS=6 VC=7 HI=8 LS=9 GE=10 LT=11 GT=12
    /// LE=13). `FcselRR` reads NZCV exactly like `Csel` (cc at operand 3);
    /// `BCond`/`Bcc` carry `[Imm(cc), Block(target)]`.
    fn nzcv_consumer_cc_pos(opcode: AArch64Opcode) -> Option<usize> {
        use AArch64Opcode::{BCond, Bcc, CSet, Csel, Csinc, Csinv, Csneg, FcselRR};
        match opcode {
            CSet => Some(1),
            Csel | Csinc | Csinv | Csneg | FcselRR => Some(3),
            BCond | Bcc => Some(0),
            _ => None,
        }
    }

    // ------------------------------------------------------------------
    // NZCV CONSUMER binding (CSET / CSEL)
    //
    // `opcode_to_proof_query` deliberately leaves `CSet` and `Csel` UNMAPPED,
    // and must keep doing so: "A generic CMP+CSET template does not establish
    // this CSET's actual condition, carrier width, or reaching flag producer"
    // (the `CSet => None` arm), and the coverage gate says the same of the
    // select family. Those are three NAMED facts, not a blanket refusal — the
    // binding below establishes each of them at the instruction, plus a
    // fourth the certificate needs and an opcode-keyed arm can never have:
    //
    //   1. CONDITION      — the `cc` immediate this instruction carries.
    //   2. CARRIER WIDTH  — the operand width of the reaching CMP (and, for
    //                       CSEL, the width of the selected values, which is
    //                       INDEPENDENT: `CMP Wn,Wm ; CSEL Xd,Xn,Xm,cc` is
    //                       emitted whenever a 32-bit compare selects 64-bit
    //                       values).
    //   3. REACHING FLAG PRODUCER — an integer CMP found in THIS block with
    //                       nothing opaque in between (`reaching_integer_cmp`).
    //   4. SOURCE CLASS   — the TV-1 stamped LIR instruction's `OpClass`. The
    //                       cited obligation describes the lowering of ONE
    //                       source operation; crediting it to an instruction
    //                       emitted while lowering a different one is a
    //                       misattribution even when the local machine
    //                       sequence happens to satisfy the theorem. No arm
    //                       below binds a CSET that an FP comparison's
    //                       lowering emitted to an integer `Icmp_*` theorem.
    //
    // Any one of the four missing FAILS CLOSED, and this binding names
    // nothing. In particular the source class is unavailable whenever there is
    // no replayed LIR (`ProvenanceXCheckMode::Off`, or no `lir_source`).
    //
    // HOW THIS COMPOSES WITH THE MACHINE-LEVEL BINDING. The in-block chain's
    // NZCV-consumer slot (`nzcv_consumer_query`) first runs
    // `flag_consumer_query`, which binds a consumer from facts 1-3 alone and
    // needs no source. Where the walk has a source of a class an arm below is
    // written for (`is_source_bound_nzcv_consumer`), this binding DECIDES: its
    // refusal removes that citation too. Without a source, or for a source of
    // any other class, the machine-level citation stands — including the
    // `Icmp_*` name of an `Fcmp`-sourced CSET reached by an intervening CMP,
    // which `fcmp_runtime_rows_bind_only_their_reaching_producer_obligation`
    // pins as a named refusal. Since E0.2 neither binding is credit: the walk
    // refuses a registry theorem found by name, so this decides only what the
    // refusal names.
    //
    // The family is bound PER OPCODE, never per encoding family: `Csinc`,
    // `Csinv` and `Csneg` add, invert and negate their false arm and have no
    // obligation here, so they keep blocking promotion. (`Csinv` is the
    // codebase's canonical uncovered-opcode fixture; a family-wide arm would
    // silently promote it.)
    //
    //   5. SOURCE CONDITION — the condition immediate must be one a correct
    //      lowering of THAT source instruction can emit
    //      (`aarch64_source_condition`). Facts 1-4 are all read off the emitted
    //      instruction and its block, and so is the `cc` that NAMES the cited
    //      family member, so without this conjunct the theorem is selected by
    //      the thing under test. Mutating only the `cc` immediate of a `CSET`
    //      lowered from `icmp slt` moved the citation from `Icmp_SLT_I64` to
    //      `Icmp_SGT_I64` and stayed `Verified`: ten of the fourteen conditions
    //      have an `Icmp_*` family member, so for those ten `NoProofMapping`
    //      was NEVER the barrier. The four that had no member — MI/PL/VS/VC —
    //      were refused for the wrong reason, which is why mapping the opcode
    //      would have opened all fourteen at once.
    //
    // A CSET this chain declines stays UNCOVERED. There is deliberately no
    // weaker decoded-word fallback row underneath it; see "WHY THE
    // DECODED-WORD `CSET` FAMILY IS NOT AN ARM HERE".
    // ------------------------------------------------------------------

    /// How far back to look for the flag producer. Matches
    /// `TST_CONSUMER_SCAN_CAP` — past it, fail closed rather than guess.
    const NZCV_PRODUCER_SCAN_CAP: usize = 16;

    /// The carrier width of the integer CMP whose NZCV reaches the consumer at
    /// `block_pos`, or `None` when that producer is not determinable HERE.
    ///
    /// Scans backward within the block. Fails closed on:
    ///   * a flag WRITER that is not an integer CMP (an `Fcmp`'s NZCV is an FP
    ///     relation, a `Tst`'s clears C/V, an `AddsRR`/`SubsRR`'s belongs to a
    ///     checked-arithmetic idiom) — crediting an integer comparison theorem
    ///     against any of them is the unfaithful inheritance #62 retracted;
    ///   * a CMP whose compared operand has no determinable register width;
    ///   * a call (the callee may or may not preserve NZCV) or a non-`Nop`
    ///     pseudo (later expansion could touch flags);
    ///   * a flag READER that is not itself a `cc` consumer (`Adc`/`Sbc` read
    ///     C directly);
    ///   * reaching the start of the block, i.e. the flags are live-IN from a
    ///     predecessor — cross-block flag provenance is not established here;
    ///   * the scan cap.
    ///
    /// Other `cc` consumers ARE transparent: the CSel family does not write
    /// NZCV, so `CMP ; CSET ; CSET` leaves both CSETs reading the same CMP.
    fn reaching_integer_cmp_width(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
    ) -> Option<u32> {
        let (producer, width) = Self::reaching_flag_producer(func, block_insts, block_pos)?;
        // It must be an integer CMP, or this consumer earns nothing.
        Self::is_cmp_opcode(producer).then_some(width)
    }

    /// The NZCV producer reaching the consumer at `block_pos`, as
    /// `(opcode, carrier width)`.
    ///
    /// The width is the register width of the producer's FIRST operand, which
    /// is the compared/added value for every opcode this returns. The caller
    /// decides which producers it accepts; see
    /// [`Self::reaching_integer_cmp_width`] for the refusal rationale, which
    /// applies identically here.
    fn reaching_flag_producer(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
    ) -> Option<(AArch64Opcode, u32)> {
        Self::reaching_flag_producer_at(func, block_insts, block_pos)
            .map(|(_, opcode, width)| (opcode, width))
    }

    /// [`Self::reaching_flag_producer`] plus the producer's BLOCK POSITION, for
    /// the callers that must read an operand of the producer itself (the i128
    /// variable-shift guard boundary, and the guard-amount register the chain's
    /// arm-wiring check keys on). Identical refusal rules; the extra return
    /// value is the position the scan stopped at.
    fn reaching_flag_producer_at(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
    ) -> Option<(usize, AArch64Opcode, u32)> {
        use trust_cg_ir::target_info::{AArch64Target, TargetInfo};
        let mut pos = block_pos;
        for _ in 0..Self::NZCV_PRODUCER_SCAN_CAP {
            pos = pos.checked_sub(1)?;
            let previous = Self::inst_at_block_pos(func, block_insts, pos)?;
            let op = previous.opcode;
            if <AArch64Target as TargetInfo>::writes_flags(op) {
                // The first writer going back IS the reaching producer.
                let width = operand_reg_width_bits(previous.operands.first()?)?;
                return Some((pos, op, width));
            }
            if Self::nzcv_consumer_cc_pos(op).is_some() {
                // A cc consumer reads the flags and leaves them intact.
                continue;
            }
            if <AArch64Target as TargetInfo>::reads_flags(op)
                || previous.is_call()
                || (op.is_pseudo() && op != AArch64Opcode::Nop)
            {
                return None;
            }
        }
        None
    }

    /// How many `CSet`s in this block carry the SAME TV-1 source stamp as the
    /// instruction at `block_pos` (itself included).
    ///
    /// This is what separates the SCALAR comparison lowering (one `CSET`) from
    /// the i128 limb decomposition (two, or three), and therefore which
    /// condition codes `aarch64_source_condition` admits. `None` when the
    /// instruction carries no source stamp — an unattributed `CSET` earns
    /// nothing anyway, but the count must not silently read as 1.
    fn same_source_cset_count(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
    ) -> Option<usize> {
        let anchor = match func.inst_lowering_provenance(*block_insts.get(block_pos)?) {
            trust_cg_ir::LoweringProvenance::SourceInst { id, .. } => id,
            _ => return None,
        };
        let mut count = 0;
        for id in block_insts {
            let sibling = func.insts.get(id.0 as usize)?;
            if sibling.opcode != AArch64Opcode::CSet {
                continue;
            }
            if matches!(
                func.inst_lowering_provenance(*id),
                trust_cg_ir::LoweringProvenance::SourceInst { id: other, .. } if other == anchor
            ) {
                count += 1;
            }
        }
        Some(count)
    }

    /// Bind a `CSET` to the `Icmp_<cond>_I<w> -> CMP+CSET_<cc>` obligation of
    /// the comparison lowering it COMPLETES.
    ///
    /// That obligation's machine side is `encode_cmp_cset(a, b, w, cc)` — the
    /// CMP *and* the CSET, as one sequence. The CMP half is already named by
    /// the opcode-level `"cmp"` token; this binds the other half of the SAME
    /// sequence, to the exact family member for this instruction's condition
    /// and this block's reaching comparison width. Neither name is
    /// per-instruction credit (E0.2).
    ///
    /// The destination is deliberately NOT used to pick the width: ISel emits
    /// the X-form CSET (`Gpr64`) regardless of whether the reaching CMP
    /// compared W or X operands ("This Gpr64 destination selects X-form CSET,
    /// which writes exactly 0 or 1 regardless of whether the reaching CMP uses
    /// W or X operands", `isel.rs` `select_cmp`), so the carrier width is the
    /// COMPARISON's, exactly as `source_bound_cset_query` reads it.
    ///
    /// `MI`/`PL`/`VS`/`VC` have no integer family member and fail closed via
    /// `icmp_family_query`.
    fn cset_reaching_cmp_query(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
        inst: &MachInst,
        source: Option<&LirSourceInst>,
    ) -> Option<(&'static str, ProofCategory)> {
        if inst.opcode != AArch64Opcode::CSet {
            return None;
        }
        let source = source?;
        if source.class != OpClass::IntCmp {
            return None;
        }
        // Shape, from `encode.rs`'s CSet arm: [Rd, Imm(cond)].
        if inst.operands.len() != 2 {
            return None;
        }
        let MachOperand::Imm(cc) = inst.operands.get(1)? else {
            return None;
        };
        // FACT 5, THE SOURCE-CONDITION BINDING. Facts 1-4 above are all read
        // off the EMITTED instruction and its block; the citation selected
        // below is named by `cc`, which is also read off the emitted
        // instruction. Without this conjunct the theorem is chosen BY the thing
        // under test: mutating only this CSET's condition immediate — leaving
        // the LIR untouched, so the code no longer implements its own source —
        // used to move the citation from `Icmp_SLT_I64` to `Icmp_SGT_I64` and
        // stay `Verified`. Ten of the fourteen conditions have an `Icmp_*`
        // family member, so for ten of them `NoProofMapping` was never the
        // barrier and the row was already self-attesting; `MI`/`PL`/`VS`/`VC`
        // were refused only because the family has no member for them.
        //
        // `cset_conditions` computes, from the SOURCE opcode alone, the set of
        // condition codes a correct AArch64 lowering of that instruction can
        // put on a `CSET` — for `Icmp { cond }` the scalar `from_intcc(cond)`
        // union the i128 limb decomposition's `{hi_cc, EQ, lo_cc}`. A condition
        // outside it cannot come from a correct lowering of this source, so the
        // row fails closed instead of citing a theorem about a different
        // program.
        // The EMISSION COUNT is part of the conjunct: one `CSET` under this
        // source stamp is the scalar `select_cmp` lowering, which emits exactly
        // `from_intcc(cond)`; two or three is the i128 limb decomposition, whose
        // `{hi_cc, EQ, lo_cc}` triple is legitimately three DIFFERENT
        // conditions. Without the count, a scalar signed less-than would admit
        // `CSET EQ` and `CSET LO` — true `Icmp_Eq_I64` / `Icmp_ULT_I64`
        // theorems about the wrong predicate.
        let emitted = Self::same_source_cset_count(func, block_insts, block_pos)?;
        if !crate::aarch64_source_condition::cset_conditions_for_emission_count(
            &source.opcode,
            emitted,
        )
        .contains(*cc)
        {
            nzcv_binding_trace(
                inst,
                source,
                *cc,
                "cset: condition not admissible for source",
            );
            return None;
        }
        // FACT 6, THE i128 LIMB ROLE (hole 3 of `2e194289f`). At emission count
        // 2 or 3 the set above is the i128 decomposition's whole `{hi_cc, EQ,
        // lo_cc}` triple, admitted at EVERY position — so the right three
        // conditions in the wrong ORDER promoted, e.g. `CSET hi_cond, EQ ; CSET
        // hi_eq, LT` for a signed less-than, which returns `hi_a == hi_b` where
        // the source asks `a < b`. The role each `CSET` plays is derived from
        // DATA FLOW — the comparison it reads and the combiner that reads it —
        // not from its position (the two high-limb `CSET`s are independent and
        // may legally appear in either order) and not from its own condition,
        // and exactly one condition is admitted for that role.
        if emitted != 1 {
            let trust_cg_lower::instructions::Opcode::Icmp { cond } = &source.opcode else {
                return None;
            };
            let admitted = i128_chain_dataflow::block_of(func, block_insts, block_pos)
                .and_then(|block| {
                    i128_chain_dataflow::i128_cmp_cset_role(func, block_insts, block, block_pos)
                })
                .and_then(|role| {
                    crate::aarch64_source_condition::i128_cmp_role_condition(*cond, role)
                });
            if admitted != Some(*cc) {
                nzcv_binding_trace(
                    inst,
                    source,
                    *cc,
                    "cset: i128 limb role does not carry this condition",
                );
                return None;
            }
        }
        let width = Self::reaching_integer_cmp_width(func, block_insts, block_pos)?;
        Self::icmp_family_query(PreciseFamily::Icmp, *cc, width)
            .map(|query| (query, ProofCategory::Comparison))
    }

    /// Bind the `CSET` that MATERIALIZES a checked-arithmetic overflow bit to
    /// the `Checked*_I64` obligation whose theorem names it.
    ///
    /// Each of those obligations is stated over the WHOLE two-instruction
    /// sequence — their registry names are literally `CheckedSadd_I64 ->
    /// ADDS+CSET_VS`, `CheckedUsub_I64 -> SUBS+CSET_LO`, and so on — and the
    /// flag-setting producer half is already bound to them by the
    /// opcode-level `AddsRR`/`SubsRR` arms. This binds the other half.
    ///
    /// The condition is what disambiguates SIGNED from UNSIGNED: `ADDS` serves
    /// both `CheckedSadd` (V flag) and `CheckedUadd` (C flag), `SUBS` both
    /// `CheckedSsub` (V) and `CheckedUsub` (borrow). The opcode-level arm
    /// cannot tell them apart and says so — "the signed/unsigned
    /// disambiguation by the following CSET cond is a per-block refinement" —
    /// which is exactly the refinement performed here. Any other condition
    /// fails closed rather than picking one of the two.
    ///
    /// WIDTH: only 64. The registry has `Checked*_I64` and the i128
    /// overflow-bit family (bound separately, and earlier in the chain, by
    /// `checked_i128_carry_chain_high_limb_query`); there is no `_I32` member,
    /// so a 32-bit checked add/sub earns nothing here instead of inheriting
    /// the 64-bit theorem.
    ///
    /// The MUL idioms (`CheckedSmul_I64 -> MUL+SMULH+ASR+CMP+CSET_NE`,
    /// `CheckedUmul_I64 -> MUL+UMULH+CMP0+CSET_NE`) end in `CMP ; CSET NE`
    /// rather than `ADDS/SUBS ; CSET`, and telling the two apart needs the
    /// `SMULH`/`UMULH` earlier in the window; they are deliberately NOT bound
    /// here and stay uncovered.
    fn cset_checked_overflow_query(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
        inst: &MachInst,
        source: Option<&LirSourceInst>,
    ) -> Option<(&'static str, ProofCategory)> {
        use AArch64Opcode::{AddsRR, SubsRR};
        use trust_cg_lower::instructions::Opcode as LirOpcode;
        if inst.opcode != AArch64Opcode::CSet {
            return None;
        }
        let source = source?;
        if source.class != OpClass::Overflow {
            return None;
        }
        if inst.operands.len() != 2 {
            return None;
        }
        let MachOperand::Imm(cc) = inst.operands.get(1)? else {
            return None;
        };
        let (producer, width) = Self::reaching_flag_producer(func, block_insts, block_pos)?;
        if width != 64 {
            return None;
        }
        // THE SOURCE-OP BINDING. The doc above says the CSET's condition is
        // "exactly the refinement" that disambiguates SIGNED from UNSIGNED —
        // and that is the defect: the signedness was taken FROM the emitted
        // condition, so an `ADDS ; CSET VS` emitted while lowering a
        // `CheckedUadd` cited `CheckedSadd_I64` and promoted. Signed and
        // unsigned overflow of the same addition differ (`1 + i64::MAX`
        // overflows signed, not unsigned), so that is a real miscompile the row
        // graded green. The signedness now comes from the SOURCE opcode, and
        // the emitted condition must AGREE with it; a disagreement fails
        // closed rather than picking whichever the instruction says.
        let query = match (&source.opcode, producer, *cc) {
            // isel CondCode encoding: HS=2 LO=3 VS=6.
            (LirOpcode::CheckedSadd, AddsRR, 6) => "checkedsadd_i64",
            (LirOpcode::CheckedUadd, AddsRR, 2) => "checkeduadd_i64",
            (LirOpcode::CheckedSsub, SubsRR, 6) => "checkedssub_i64",
            (LirOpcode::CheckedUsub, SubsRR, 3) => "checkedusub_i64",
            _ => {
                nzcv_binding_trace(
                    inst,
                    source,
                    *cc,
                    "cset: checked-overflow source/cc disagree",
                );
                return None;
            }
        };
        Some((query, ProofCategory::Arithmetic))
    }

    /// Bind a `CSEL` to the faithful `Select_<cond>_Nzcv<w>_Sel<w> ->
    /// CSEL_<cc>` obligation (`aarch64_select_proofs`), whose machine side
    /// is the DECODED CSEL instruction word rather than a restatement of the
    /// spec — the "faithful independent conditional-select machine encoder"
    /// the coverage gate records as the family's missing evidence.
    ///
    /// Only `Csel`. `Csinc`/`Csinv`/`Csneg` share the encoding family and the
    /// `nzcv_consumer_cc_pos` arm but compute different false arms; they have
    /// no obligation here and keep blocking promotion.
    fn csel_reaching_cmp_query(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
        inst: &MachInst,
        source: Option<&LirSourceInst>,
    ) -> Option<(&'static str, ProofCategory)> {
        if inst.opcode != AArch64Opcode::Csel {
            return None;
        }
        let source = source?;
        if source.class != OpClass::Select {
            return None;
        }
        // Shape, from `encode.rs`'s Csel arm: [Rd, Rn (true), Rm (false),
        // Imm(cond)]. The three registers must share one carrier width, which
        // is the width the obligation's select arms are modeled at.
        if inst.operands.len() != 4 {
            return None;
        }
        let sel_width = operand_reg_width_bits(inst.operands.first()?)?;
        if operand_reg_width_bits(inst.operands.get(1)?)? != sel_width
            || operand_reg_width_bits(inst.operands.get(2)?)? != sel_width
        {
            return None;
        }
        let MachOperand::Imm(cc) = inst.operands.get(3)? else {
            return None;
        };
        // THE SOURCE-CONDITION BINDING, same defect as the CSET arm: the cited
        // `Select_<cond>_...` family member is named by the condition read off
        // this CSEL. `csel_conditions` derives the admissible set from the
        // source side — the `Select`'s own `from_intcc(cond)`, plus (for the
        // boolean-sense selects ISel may FOLD) the condition of the compare
        // DEFINING its boolean operand and that condition's complement, which
        // is a different LIR instruction and therefore unreachable from the
        // emitted instruction alone.
        if !crate::aarch64_source_condition::csel_conditions(source).contains(*cc) {
            nzcv_binding_trace(
                inst,
                source,
                *cc,
                "csel: condition not admissible for source",
            );
            return None;
        }
        let cmp_width = Self::reaching_integer_cmp_width(func, block_insts, block_pos)?;
        crate::aarch64_select_proofs::select_family_query_for_immediate(*cc, cmp_width, sel_width)
            .map(|query| (query, ProofCategory::Comparison))
    }

    // ------------------------------------------------------------------
    // The i128 VARIABLE-SHIFT funnel's conditional selects
    // ------------------------------------------------------------------

    /// The two guard conditions the AArch64 i128 VARIABLE-shift decomposition
    /// emits, each paired with the CMP immediate it is guarded against.
    ///
    /// `isel.rs`'s `select_i128_shl` / `_lshr` / `_ashr` emit exactly two
    /// comparisons and three conditional selects:
    ///
    /// ```text
    ///   CMP  shift, #0      ; CSEL spill,  zero, spill_raw, EQ   (shift == 0:
    ///                       ;   AArch64 register shifts mask by 63, so the
    ///                       ;   `>> (64 - 0)` spill term must be forced to 0)
    ///   CMP  shift, #64     ; CSEL dst_lo, …, …, HS              (shift >= 64)
    ///                       ; CSEL dst_hi, …, …, HS
    /// ```
    ///
    /// The condition immediates are `AArch64CC`'s own discriminants (EQ=0,
    /// HS=2), the encoding `cc_from_isel_immediate` documents.
    const I128_SHIFT_CHAIN_GUARDS: [(i64, i64); 2] = [(0, 0), (2, 64)];

    /// The per-source-instruction shape of the i128 variable-shift chain in
    /// this block: `((integer-CMP immediate, that CMP's carrier width), CSEL
    /// condition immediates)` over exactly the instructions stamped with the
    /// SAME LIR source instruction as the one at `block_pos`.
    ///
    /// Fails closed (`None`) when this instruction carries no source stamp, or
    /// when any sibling CMP/CSEL has an operand shape this cannot read — an
    /// unreadable sibling must not be silently treated as absent.
    fn i128_shift_chain_siblings(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
    ) -> Option<I128ShiftChainSiblings> {
        let anchor = match func.inst_lowering_provenance(*block_insts.get(block_pos)?) {
            trust_cg_ir::LoweringProvenance::SourceInst { id, .. } => id,
            _ => return None,
        };
        let (mut cmps, mut csels) = (Vec::new(), Vec::new());
        for id in block_insts {
            let sibling = func.insts.get(id.0 as usize)?;
            let same = matches!(
                func.inst_lowering_provenance(*id),
                trust_cg_ir::LoweringProvenance::SourceInst { id: other, .. } if other == anchor
            );
            if !same {
                continue;
            }
            if Self::is_cmp_opcode(sibling.opcode) {
                cmps.push((
                    Self::sole_immediate_operand(sibling)?,
                    operand_reg_width_bits(sibling.operands.first()?)?,
                ));
            } else if sibling.opcode == AArch64Opcode::Csel {
                let MachOperand::Imm(cc) = sibling.operands.get(3)? else {
                    return None;
                };
                csels.push(*cc);
            }
        }
        Some((cmps, csels))
    }

    /// The single `Imm` operand of an instruction, or `None` when it has none
    /// or more than one. A register-register CMP therefore fails closed rather
    /// than being read as a comparison against some default boundary.
    fn sole_immediate_operand(inst: &MachInst) -> Option<i64> {
        let mut found = None;
        for operand in &inst.operands {
            if let MachOperand::Imm(value) = operand {
                if found.is_some() {
                    return None;
                }
                found = Some(*value);
            }
        }
        found
    }

    /// The instruction that last WROTE `register` before `block_pos`, looking
    /// only through opcodes whose destination is operand 0.
    ///
    /// This is deliberately not a general def-use query: the AArch64 machine IR
    /// has no def predicate, so the scan stops at the first instruction whose
    /// operand 0 IS `register` and returns it. A caller only ever ACCEPTS a
    /// result whose opcode it recognises as dest-first, so a source-position
    /// operand-0 coincidence (`CMP Xn, #0`) stops the scan and fails the
    /// caller's test rather than being read as a definition. A call also stops
    /// it, since a callee may clobber anything.
    fn last_operand0_writer<'f>(
        func: &'f MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
        register: &MachOperand,
    ) -> Option<&'f MachInst> {
        let mut pos = block_pos;
        for _ in 0..Self::NZCV_PRODUCER_SCAN_CAP {
            pos = pos.checked_sub(1)?;
            let previous = Self::inst_at_block_pos(func, block_insts, pos)?;
            if previous.is_call() {
                return None;
            }
            if previous.operands.first() == Some(register) {
                return Some(previous);
            }
        }
        None
    }

    /// True when `inst` materialises the integer constant `value` into its
    /// destination with a single `MOVZ`.
    fn is_movz_const(inst: &MachInst, value: i64) -> bool {
        inst.opcode == AArch64Opcode::Movz
            && matches!(inst.operands.get(1), Some(MachOperand::Imm(imm)) if *imm == value)
    }

    /// True for the AArch64 register-amount shift opcodes the i128 funnel uses.
    fn is_register_shift(opcode: AArch64Opcode) -> bool {
        use AArch64Opcode::{AsrRR, LslRR, LsrRR};
        matches!(opcode, LslRR | LsrRR | AsrRR)
    }

    /// Bind a `CSEL` emitted by the i128 VARIABLE-shift decomposition to the
    /// faithful whole-chain obligation of the shift it implements
    /// (`Ishl_I128 -> LSLV/LSRV/ORR/CSEL pair`, and the `Ushr`/`Sshr` siblings
    /// — `lowering_proof::proof_ishl_i128` and friends, registered under
    /// `ProofCategory::Arithmetic`).
    ///
    /// This is the same move as `(AddsRR, Adc) => "iadd_i128 whole-chain"`: the
    /// cited obligation is stated over the WHOLE emitted sequence — its
    /// AArch64 side IS the two-limb funnel with both `CSEL` guards, compared
    /// against a 128-bit `bvshl`/`bvlshr`/`bvashr` of the limb concatenation —
    /// so it is non-degenerate, and the other constituents of the chain
    /// (`LSLV`/`LSRV`/`ASRV`/`ORR`/`SUB`/`MOVZ`) are already bound to their
    /// own opcode-level obligations. What is missing is the binding of THIS
    /// `CSEL` to that chain, which `opcode_to_proof_query` cannot have and must
    /// keep refusing (`Csel | Csinc | Csneg => None`).
    ///
    /// ELEVEN facts, each independently fail-closed (8-11 below):
    ///
    ///   1. OPCODE + CARRIER — a plain `Csel` (never `Csinc`/`Csinv`/`Csneg`,
    ///      whose false arms add, invert and negate) whose three register
    ///      operands are all 64-bit. The chain is entirely 64-bit limbs.
    ///   2. SOURCE OPERATION — the TV-1 stamped LIR instruction is exactly
    ///      `Ishl`, `Ushr` or `Sshr`, which picks the chain theorem for that
    ///      DIRECTION. A stamp of any other opcode earns nothing, so a `CSEL`
    ///      from a source `Select`, an FP min/max idiom or an unstamped
    ///      instruction never reaches here.
    ///   3. GUARD CONDITION — the condition immediate is `EQ` or `HS`, the only
    ///      two conditions the three chain selects carry, cross-checked against
    ///      `aarch64_source_condition::csel_conditions` for this source opcode.
    ///   4. GUARD BOUNDARY — the reaching in-block integer CMP (same producer
    ///      scan as the CSET/CSEL bindings, 64-bit) compares against the
    ///      immediate that condition is paired with: `#0` for the `shift == 0`
    ///      spill guard, `#64` for the `shift >= 64` selector. A `CSEL EQ`
    ///      reached by `CMP shift, #64` is therefore REFUSED, not credited.
    ///   5. CHAIN SHAPE — among the instructions stamped with this same source
    ///      instruction, the integer CMPs are exactly the two boundaries
    ///      `{0, 64}` and every `Csel` carries `EQ` or `HS`, at most three of
    ///      them. A foreign condition or a third boundary fails closed.
    ///   6. ARM WIRING, `EQ` GUARD — the TRUE arm is the chain's materialised
    ///      zero (`MOVZ Rd, #0`) and the FALSE arm is a register-amount shift
    ///      (the raw spill term). Facts 1-5 are ALL blind to which value goes
    ///      in which arm, and that is not a hypothetical: swapping the two arms
    ///      of this one select is a two-byte object change that makes
    ///      `1u128 << 0` evaluate to `2^64 + 1`, and it satisfies every one of
    ///      facts 1-5 — same opcode, same widths, same condition, same
    ///      boundary, same chain shape. The guard's whole purpose is to force
    ///      the spill term to zero WHEN the condition holds; an implementation
    ///      that forces it to zero when the condition FAILS is the negation of
    ///      the theorem being cited.
    ///   7. ARM WIRING, `HS` GUARD — the FALSE arm (the `shift < 64` value) is
    ///      the funnel's combined result (`ORR`) or a shift BY THE GUARD'S OWN
    ///      COMPARED REGISTER, and the TRUE arm (the `shift >= 64` value) is
    ///      the materialised zero, or a shift by something OTHER than that
    ///      register (`big_shift = shift - 64`, or the `#63` sign fill). Read
    ///      off the three lowerings: `shl` selects `{zero, hi_big}` against
    ///      `{lo_normal, hi_normal}`, `lshr` `{zero, lo_big}` against
    ///      `{hi_normal, lo_normal}`, `ashr` `{hi_sign, lo_big}` against
    ///      `{hi_normal, lo_normal}` — in every case the "normal" arm is an
    ///      `ORR` or a shift by `shift` itself, and the "big" arm never is.
    ///
    /// Facts 6 and 7 close the arm ORDER of each select, not the identity of the
    /// values it selects, and `2e194289f` disclosed what that left open: the
    /// `dst_lo`/`dst_hi` selects could exchange their arm PAIRS, and nothing
    /// reconstructed the funnel. Four more facts close it, each a data-flow
    /// question answered by reaching definitions over the emitted code (see
    /// `aarch64_i128_chain_dataflow`):
    ///
    ///   8. DATA FLOW — every arm of every select is built exactly as the cited
    ///      theorem builds it, from ONE low limb, ONE high limb and ONE amount
    ///      (`hi_normal == (hi << s) | guarded(lo >> (64 - s))`, the
    ///      `64 - s`/`s - 64` subtractions, the `#0`/`#64` guard compares).
    ///   9. SOURCE LIMBS — those limbs are the shifted operand's: a formal `i128`
    ///      whose AAPCS64 register pair, on function entry, is what the chain
    ///      reads.
    ///  10. AMOUNT — the amount is the source's shift-amount operand (a formal's
    ///      register, or the value its scalar defining instruction wrote).
    ///  11. RESULT LIMBS — the result's only use is the function's `Return`, and
    ///      at `RET` `x0` holds the low select and `x1` the high select.
    ///
    /// A shifted value that is not a formal, or a result with any other use, has
    /// no limb rule here and is REFUSED — the binding fails closed rather than
    /// trusting ISel's private value map for which register is which limb.
    fn i128_variable_shift_chain_csel_query(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
        inst: &MachInst,
        source: Option<&LirSourceInst>,
    ) -> Option<(&'static str, ProofCategory)> {
        use trust_cg_lower::instructions::Opcode as LirOpcode;
        if inst.opcode != AArch64Opcode::Csel {
            return None;
        }
        let source = source?;
        if source.class != OpClass::Shift {
            return None;
        }
        // FACT 2: the stamped LIR opcode picks the chain theorem's DIRECTION.
        // Queries MUST be lowercase: the walk's lookup does
        // `name.to_lowercase().contains(query)` WITHOUT lowercasing the query.
        let query = match &source.opcode {
            LirOpcode::Ishl => "ishl_i128",
            LirOpcode::Ushr => "ushr_i128",
            LirOpcode::Sshr => "sshr_i128",
            _ => return None,
        };
        // FACT 1: shape from `encode.rs`'s Csel arm, [Rd, Rn, Rm, Imm(cond)],
        // with all three limb registers at the chain's 64-bit carrier.
        if inst.operands.len() != 4 {
            return None;
        }
        for slot in 0..3 {
            if operand_reg_width_bits(inst.operands.get(slot)?)? != 64 {
                return None;
            }
        }
        let MachOperand::Imm(cc) = inst.operands.get(3)? else {
            return None;
        };
        // FACT 3: one of the chain's two guard conditions — stated once, in the
        // source-condition tables, so this arm and the `Select` arm cannot
        // drift — and FACT 4: reached by the integer CMP against THAT guard's
        // boundary.
        if !crate::aarch64_source_condition::csel_conditions(source).contains(*cc) {
            nzcv_binding_trace(
                inst,
                source,
                *cc,
                "csel-i128-shift: condition not a chain guard",
            );
            return None;
        }
        let boundary = Self::I128_SHIFT_CHAIN_GUARDS
            .iter()
            .find(|(condition, _)| condition == cc)?
            .1;
        let (producer_pos, producer, amount_width) =
            Self::reaching_flag_producer_at(func, block_insts, block_pos)?;
        // The guard compares the SHIFT AMOUNT, whose carrier is the count's own
        // type — `CMP Wn, #0` for a `u32` count (the shape `core`'s
        // `<u128>::unchecked_shl` emits, measured), `CMP Xn, #0` for a wider
        // one — and is INDEPENDENT of the chain's 64-bit limb carrier, which
        // FACT 1 pins on the CSEL's own registers. Both amount widths are
        // admitted; nothing else is.
        if !Self::is_cmp_opcode(producer) || !matches!(amount_width, 32 | 64) {
            return None;
        }
        let producer_inst = Self::inst_at_block_pos(func, block_insts, producer_pos)?;
        if Self::sole_immediate_operand(producer_inst)? != boundary {
            return None;
        }
        // FACT 5: the chain emits exactly the two boundaries and at most three
        // selects, all on the two guard conditions — and BOTH boundaries are
        // checked at the SAME amount width, which is this guard's. A chain that
        // tested `#0` at W and `#64` at X would not be one this theorem
        // describes.
        let (mut cmps, csels) = Self::i128_shift_chain_siblings(func, block_insts, block_pos)?;
        cmps.sort_unstable();
        if cmps != vec![(0, amount_width), (64, amount_width)] {
            return None;
        }
        if csels.is_empty() || csels.len() > 3 {
            return None;
        }
        if !csels.iter().all(|condition| {
            Self::I128_SHIFT_CHAIN_GUARDS
                .iter()
                .any(|(guard, _)| guard == condition)
        }) {
            return None;
        }
        // FACTS 6 and 7: the ARM WIRING. `true_arm`/`false_arm` are operands 1
        // and 2 (`encode.rs`'s Csel arm), and the defining instruction of each
        // is the last in-block writer of that register.
        let true_arm = inst.operands.get(1)?;
        let false_arm = inst.operands.get(2)?;
        if true_arm == false_arm {
            return None;
        }
        let true_def = Self::last_operand0_writer(func, block_insts, block_pos, true_arm)?;
        let false_def = Self::last_operand0_writer(func, block_insts, block_pos, false_arm)?;
        let wired = if *cc == crate::aarch64_source_condition::cc::EQ {
            // FACT 6: the `shift == 0` spill guard forces the spill term to
            // ZERO when the condition HOLDS.
            Self::is_movz_const(true_def, 0) && Self::is_register_shift(false_def.opcode)
        } else {
            // FACT 7: the `shift >= 64` selector. The `shift < 64` (FALSE) arm
            // is the funnel's combined value or a shift by the compared
            // register; the `shift >= 64` (TRUE) arm never is.
            let amount = producer_inst.operands.first()?;
            let shift_by_amount = |def: &MachInst| {
                Self::is_register_shift(def.opcode) && def.operands.get(2) == Some(amount)
            };
            let false_ok = false_def.opcode == AArch64Opcode::OrrRR || shift_by_amount(false_def);
            let true_ok = (Self::is_movz_const(true_def, 0)
                || Self::is_register_shift(true_def.opcode))
                && !shift_by_amount(true_def);
            false_ok && true_ok
        };
        if !wired {
            nzcv_binding_trace(
                inst,
                source,
                *cc,
                "csel-i128-shift: guard arms are not wired as the chain theorem states",
            );
            return None;
        }
        // FACTS 8-11: the chain's DATA FLOW, and the ends of it. Facts 1-7 are
        // per-select; every one of them survives a mutation that permutes ROLES
        // between the three selects or rewires what their arms compute, and the
        // cited theorem is about the whole funnel, so each such mutation was a
        // certified miscompile. See `aarch64_i128_chain_dataflow`.
        let direction = match &source.opcode {
            LirOpcode::Ishl => i128_chain_dataflow::ShiftDirection::Left,
            LirOpcode::Ushr => i128_chain_dataflow::ShiftDirection::LogicalRight,
            _ => i128_chain_dataflow::ShiftDirection::ArithmeticRight,
        };
        let Some(chain) =
            i128_chain_dataflow::block_of(func, block_insts, block_pos).and_then(|block| {
                i128_chain_dataflow::I128ShiftChain::identify(
                    func,
                    block,
                    block_insts,
                    block_pos,
                    direction,
                )
            })
        else {
            nzcv_binding_trace(
                inst,
                source,
                *cc,
                "csel-i128-shift: the three selects have no role assignment",
            );
            return None;
        };
        // FACT 8 (hole 4): every arm is the funnel the cited theorem builds, from
        // ONE low limb, ONE high limb and ONE amount — `hi_normal == (hi << s) |
        // guarded(lo >> (64 - s))` and its siblings, not merely "an ORR".
        if let Some(why) = chain.shape_mismatch(func) {
            nzcv_binding_trace(inst, source, *cc, why);
            return None;
        }
        // FACT 9 (hole 4): those limbs ARE the shifted operand's limbs — the
        // formal's AAPCS64 register pair on entry — not merely two values used
        // consistently. A chain that reads its limbs exchanged is internally
        // consistent and shifts a different number.
        if !chain.inputs_anchored(func, source) {
            nzcv_binding_trace(
                inst,
                source,
                *cc,
                "csel-i128-shift: the chain does not read the shifted operand's limbs",
            );
            return None;
        }
        // FACT 10 (hole 4): the amount IS the source's shift-amount operand.
        if !chain.amount_anchored(func, source) {
            nzcv_binding_trace(
                inst,
                source,
                *cc,
                "csel-i128-shift: the chain does not shift by the source amount",
            );
            return None;
        }
        // FACT 11 (hole 2): each select's destination is the result limb its
        // role names. Exchanging the `dst_lo`/`dst_hi` arm PAIRS keeps facts 1-10
        // true of every select and returns the limbs swapped.
        if !chain.outputs_anchored(func, source) {
            nzcv_binding_trace(
                inst,
                source,
                *cc,
                "csel-i128-shift: a select does not write the result limb its role names",
            );
            return None;
        }
        Some((query, ProofCategory::Arithmetic))
    }

    /// The NZCV-consumer binding for one instruction: `CSET` or `CSEL`, or
    /// `None`. Every arm fails closed independently; see the block comment
    /// above for the facts each one establishes, and
    /// [`Self::i128_variable_shift_chain_csel_query`] for the seven the i128
    /// variable-shift guard adds.
    ///
    /// ORDER IS LOAD-BEARING AND NO COUNT CAN SEE IT. The arms are tried in the
    /// order written, and the i128 variable-shift arm is LAST on purpose: the
    /// arms above cite theorems about the comparison or checked-arithmetic
    /// sequence a `CSET`/`CSEL` completes, and moving a weaker or differently
    /// scoped arm in front of them silently REPLACES those citations while
    /// every root count stays byte-identical. That is not hypothetical — moving
    /// the decoded-word CSET arm to the front of the chain took
    /// `aarch64_nzcv_consumer_binding` from 13/0 to 9 passed / 4 FAILED with
    /// the census root sets UNCHANGED. `nzcv_consumer_arm_order_is_pinned`
    /// asserts this order and fails if the i128 arm is moved earlier.
    fn nzcv_consumer_source_bound_query(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
        inst: &MachInst,
        source: Option<&LirSourceInst>,
    ) -> Option<(&'static str, ProofCategory)> {
        // Driven from `NZCV_CONSUMER_ARMS` rather than a chain of `or_else`, so
        // the ORDER is a value a test can read. A hand-written chain and a test
        // that "asserts the order" cannot actually be kept in agreement — the
        // test would be asserting its own copy.
        Self::NZCV_CONSUMER_ARMS
            .iter()
            .find_map(|(_, arm)| arm(func, block_insts, block_pos, inst, source))
    }

    /// THE ordered NZCV-consumer arms. This table IS the walk order — see
    /// [`Self::nzcv_consumer_source_bound_query`], which has no other source of
    /// it — so `nzcv_consumer_arm_order_is_pinned` asserting this list is
    /// asserting what actually runs.
    #[allow(clippy::type_complexity)]
    pub const NZCV_CONSUMER_ARMS: &'static [(
        &'static str,
        fn(
            &MachFunction,
            &[InstId],
            usize,
            &MachInst,
            Option<&LirSourceInst>,
        ) -> Option<(&'static str, ProofCategory)>,
    )] = &[
        ("cset_reaching_cmp", Self::cset_reaching_cmp_query),
        ("cset_checked_overflow", Self::cset_checked_overflow_query),
        ("csel_reaching_cmp", Self::csel_reaching_cmp_query),
        (
            "i128_variable_shift_chain_csel",
            Self::i128_variable_shift_chain_csel_query,
        ),
    ];

    /// Whether `source` is a class one of [`Self::NZCV_CONSUMER_ARMS`] is
    /// written for, for this opcode: `IntCmp` (`cset_reaching_cmp`) or
    /// `Overflow` (`cset_checked_overflow`) for a `CSET`; `Select`
    /// (`csel_reaching_cmp`) or `Shift` (`i128_variable_shift_chain_csel`) for
    /// a `CSEL`. For exactly these the source-bound binding decides whether the
    /// machine-level citation stands ([`Self::nzcv_consumer_query`]). Keep it
    /// in step with each arm's own class test.
    fn is_source_bound_nzcv_consumer(inst: &MachInst, source: &LirSourceInst) -> bool {
        match inst.opcode {
            AArch64Opcode::CSet => matches!(source.class, OpClass::IntCmp | OpClass::Overflow),
            AArch64Opcode::Csel => matches!(source.class, OpClass::Select | OpClass::Shift),
            _ => false,
        }
    }

    // ------------------------------------------------------------------
    // WHY THE DECODED-WORD `CSET` FAMILY IS NOT AN ARM HERE
    //
    // `aarch64_value_decode_proofs` carries a decoded-word value obligation per
    // (destination width, condition) `CSET` form — 28 forms, exhaustive over
    // all sixteen NZCV states, with 392 mutation-proved must-refute controls
    // and an independent third transcription of Arm Table C1-1. Those theorems
    // are not in question and they stay registered, discharged and pinned.
    //
    // What they do NOT state is anything about the PROGRAM. This codebase's own
    // refusal text for `CSet` names three requirements — "does not establish
    // this CSET's actual condition, carrier width, or reaching flag producer" —
    // and a decoded-word row satisfies the first two BY CONSTRUCTION (it is
    // keyed on them) while saying nothing at all about the third, nor about
    // which source operation the instruction completes. Binding it as a
    // last-resort promotion arm therefore promotes a partial claim as if it
    // were the whole one, and the populations it would reach are exactly the
    // ones that must not be reached:
    //
    //   * An `Icmp`-sourced `CSET` with a determinable in-block producer is
    //     already claimed, EARLIER, by the NZCV-consumer slot that
    //     `cset_reaching_cmp_query` gates, whose citation is a theorem about
    //     the whole `CMP ; CSET` sequence. The
    //     decoded-word arm can only ever take instructions that arm REFUSED —
    //     i.e. exactly those whose producer or condition is unattested.
    //   * The checked-MUL idioms (`MUL ; UMULH ; CMP #0 ; CSET NE`) are the
    //     bulk of the remaining `CSet` blame in `library/core`. The condition
    //     `NE` there means "the high half of the product is nonzero", which is
    //     a fact about WHICH REGISTER the `CMP` compares — something the
    //     decoded-word row cannot see. The whole-chain theorem that WOULD state
    //     it (`CheckedUmul_I64 -> MUL+UMULH+CMP0+CSET_NE`) is SMT
    //     capacity-bound and does not discharge: `ay_bridge` tolerates it as a
    //     known `AYResult::Timeout`. There is no row that checks this
    //     condition, so it stays refused.
    //   * An `Fcmp`-sourced `CSET` reads flags an `FCMP` set, and the
    //     decoded-word row says nothing about FP flag semantics or about the
    //     two-`CSET` combination the ordered-not-equal forms need.
    //
    // So the family is kept as a DISCLOSED obligation with no promotion
    // authority. `opcode_to_proof_query(CSet)` stays `None`, the opcode-level
    // `coverage_gate` row is covered only through the NZCV producer/consumer
    // family and never by this one, and every
    // `assert_eq!(status, Unverified)` in `aarch64_nzcv_consumer_binding`
    // stands unweakened — strengthened, in fact, by the added assertion that
    // the row is not credited a decoded-word citation either.
    // ------------------------------------------------------------------

    // ------------------------------------------------------------------
    // Precise citations (opt-in: TCG_PRECISE_CITATIONS=1)
    //
    // A bare CMP is credited by the `"cmp"` fragment, which resolves to the
    // FIRST `Icmp_*` proof in the category (Eq, 32-bit) whatever the CMP's
    // width and whatever condition its consumer reads; a conditional branch
    // likewise cites `CondBr_Eq_I32`. The registry has the full family
    // (Eq NE SGE SGT SLE SLT UGE UGT ULE ULT x I32/I64) for both. With the
    // flag on, the walk names the family member that IS this instruction's
    // lowering — the CMP's own width and the single condition its NZCV
    // consumers read — and falls back to the fragment (unchanged behaviour)
    // whenever that is not determinable: no consumer in the block, consumers
    // disagreeing on the condition, a condition with no integer family
    // member (MI/PL/VS/VC), or a branch whose flags come from something other
    // than a CMP. Verdicts never change (every family member is Valid); the
    // certificate's `rule_name` becomes the instruction's own proof.
    // ------------------------------------------------------------------

    /// `Icmp_<cond>_I<w>` / `CondBr_<cond>_I<w>` as the lowercase query that
    /// matches exactly that registry entry (pinned by
    /// `precise_citation_families_are_unique`).
    fn icmp_family_query(kind: PreciseFamily, cc: i64, width: u32) -> Option<&'static str> {
        // AArch64 condition-code encoding -> the registry's trust-ir spelling.
        // 10 conditions x 2 widths per family (UGE/HS returned with the adder
        // carry-out flag model; MI/PL/VS/VC have no integer family member).
        Some(match (kind, cc, width) {
            (PreciseFamily::Icmp, 0, 32) => "icmp_eq_i32",
            (PreciseFamily::Icmp, 0, 64) => "icmp_eq_i64",
            (PreciseFamily::Icmp, 1, 32) => "icmp_ne_i32",
            (PreciseFamily::Icmp, 2, 32) => "icmp_uge_i32",
            (PreciseFamily::Icmp, 1, 64) => "icmp_ne_i64",
            (PreciseFamily::Icmp, 2, 64) => "icmp_uge_i64",

            (PreciseFamily::Icmp, 3, 32) => "icmp_ult_i32",
            (PreciseFamily::Icmp, 3, 64) => "icmp_ult_i64",
            (PreciseFamily::Icmp, 8, 32) => "icmp_ugt_i32",
            (PreciseFamily::Icmp, 8, 64) => "icmp_ugt_i64",
            (PreciseFamily::Icmp, 9, 32) => "icmp_ule_i32",
            (PreciseFamily::Icmp, 9, 64) => "icmp_ule_i64",
            (PreciseFamily::Icmp, 10, 32) => "icmp_sge_i32",
            (PreciseFamily::Icmp, 10, 64) => "icmp_sge_i64",
            (PreciseFamily::Icmp, 11, 32) => "icmp_slt_i32",
            (PreciseFamily::Icmp, 11, 64) => "icmp_slt_i64",
            (PreciseFamily::Icmp, 12, 32) => "icmp_sgt_i32",
            (PreciseFamily::Icmp, 12, 64) => "icmp_sgt_i64",
            (PreciseFamily::Icmp, 13, 32) => "icmp_sle_i32",
            (PreciseFamily::Icmp, 13, 64) => "icmp_sle_i64",
            (PreciseFamily::CondBr, 0, 32) => "condbr_eq_i32",
            (PreciseFamily::CondBr, 0, 64) => "condbr_eq_i64",
            (PreciseFamily::CondBr, 1, 32) => "condbr_ne_i32",
            (PreciseFamily::CondBr, 2, 32) => "condbr_uge_i32",
            (PreciseFamily::CondBr, 1, 64) => "condbr_ne_i64",
            (PreciseFamily::CondBr, 2, 64) => "condbr_uge_i64",

            (PreciseFamily::CondBr, 3, 32) => "condbr_ult_i32",
            (PreciseFamily::CondBr, 3, 64) => "condbr_ult_i64",
            (PreciseFamily::CondBr, 8, 32) => "condbr_ugt_i32",
            (PreciseFamily::CondBr, 8, 64) => "condbr_ugt_i64",
            (PreciseFamily::CondBr, 9, 32) => "condbr_ule_i32",
            (PreciseFamily::CondBr, 9, 64) => "condbr_ule_i64",
            (PreciseFamily::CondBr, 10, 32) => "condbr_sge_i32",
            (PreciseFamily::CondBr, 10, 64) => "condbr_sge_i64",
            (PreciseFamily::CondBr, 11, 32) => "condbr_slt_i32",
            (PreciseFamily::CondBr, 11, 64) => "condbr_slt_i64",
            (PreciseFamily::CondBr, 12, 32) => "condbr_sgt_i32",
            (PreciseFamily::CondBr, 12, 64) => "condbr_sgt_i64",
            (PreciseFamily::CondBr, 13, 32) => "condbr_sle_i32",
            (PreciseFamily::CondBr, 13, 64) => "condbr_sle_i64",
            _ => return None,
        })
    }

    fn is_cmp_opcode(opcode: AArch64Opcode) -> bool {
        use AArch64Opcode::{CMPWri, CMPWrr, CMPXri, CMPXrr, CmpRI, CmpRR};
        matches!(opcode, CmpRR | CmpRI | CMPWrr | CMPXrr | CMPWri | CMPXri)
    }

    /// The single condition every NZCV consumer of the CMP at `block_pos`
    /// reads, scanning forward until the flags die; `None` when there is no
    /// consumer, consumers disagree, or something else reads the flags.
    fn cmp_consumer_cc(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
    ) -> Result<i64, &'static str> {
        use trust_cg_ir::target_info::{AArch64Target, TargetInfo};
        const SCAN_CAP: usize = 16;
        let mut cc: Option<i64> = None;
        let mut pos = block_pos + 1;
        while pos <= block_pos + SCAN_CAP {
            let Some(inst) = Self::inst_at_block_pos(func, block_insts, pos) else {
                break;
            };
            if let Some(cc_pos) = Self::nzcv_consumer_cc_pos(inst.opcode) {
                let Some(MachOperand::Imm(found)) = inst.operands.get(cc_pos) else {
                    return Err("cc operand not an immediate");
                };
                match cc {
                    None => cc = Some(*found),
                    Some(seen) if seen == *found => {}
                    Some(_) => return Err("consumers disagree"),
                }
                if inst.is_branch() || inst.is_terminator() {
                    break;
                }
                pos += 1;
                continue;
            }
            let op = inst.opcode;
            if <AArch64Target as TargetInfo>::writes_flags(op) {
                break;
            }
            if <AArch64Target as TargetInfo>::reads_flags(op) {
                return Err("flags read by a non-cc consumer");
            }
            // A call or an opaque pseudo ends the flags' live range: fine after
            // a consumer was seen, undeterminable before one.
            if inst.is_call() {
                return cc.ok_or("call before any consumer");
            }
            if op.is_pseudo() && op != AArch64Opcode::Nop {
                return cc.ok_or("pseudo before any consumer");
            }
            if inst.is_branch() || inst.is_terminator() {
                break;
            }
            pos += 1;
        }
        cc.ok_or("no nzcv consumer in block")
    }

    /// `Icmp_<cond>_I<w>` for the CMP at `block_pos`: its compared register's
    /// width and its consumers' single condition.
    /// `Err` carries the reason it could not refine (for the trace).
    fn precise_cmp_query_why(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
        inst: &MachInst,
    ) -> Result<&'static str, String> {
        if !Self::is_cmp_opcode(inst.opcode) {
            return Err("not a cmp".into());
        }
        let width = inst
            .operands
            .first()
            .and_then(operand_reg_width_bits)
            .ok_or_else(|| "operand width unknown".to_string())?;
        let cc = Self::cmp_consumer_cc(func, block_insts, block_pos)
            .map_err(|e| format!("w{width}: {e}"))?;
        Self::icmp_family_query(PreciseFamily::Icmp, cc, width)
            .ok_or_else(|| format!("w{width} cc{cc}: no family member"))
    }

    /// The conditional branch at `block_pos` cites the obligation of the flag
    /// writer it consumes: `CondBr_<cond>_I<w>` (Branch) after a CMP of width
    /// `w`, or the standalone-TST obligation for its condition (CmpCombine)
    /// after a TST — scanning back to the nearest flag writer; any other
    /// writer, or none in the block, keeps the fragment.
    /// `Err` carries the reason it could not refine (for the trace).
    fn precise_condbr_query_why(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
        inst: &MachInst,
    ) -> Result<(&'static str, ProofCategory), String> {
        use trust_cg_ir::target_info::{AArch64Target, TargetInfo};
        if !matches!(inst.opcode, AArch64Opcode::BCond | AArch64Opcode::Bcc) {
            return Err("not a conditional branch".into());
        }
        let Some(MachOperand::Imm(cc)) = inst.operands.first() else {
            return Err("cc operand not an immediate".into());
        };
        let mut pos = block_pos;
        while pos > 0 && block_pos - pos <= 16 {
            pos -= 1;
            let prev = Self::inst_at_block_pos(func, block_insts, pos)
                .ok_or_else(|| "block position out of range".to_string())?;
            if <AArch64Target as TargetInfo>::writes_flags(prev.opcode) {
                let width = prev
                    .operands
                    .first()
                    .and_then(operand_reg_width_bits)
                    .ok_or_else(|| "flag writer operand width unknown".to_string())?;
                if prev.opcode == AArch64Opcode::Tst {
                    return Self::tst_condition_query(width, *cc)
                        .map(|q| (q, ProofCategory::CmpCombine))
                        .ok_or_else(|| format!("tst w{width} cc{cc}: no TST obligation"));
                }
                if !Self::is_cmp_opcode(prev.opcode) {
                    return Err(format!("flags from {:?}", prev.opcode));
                }
                return Self::icmp_family_query(PreciseFamily::CondBr, *cc, width)
                    .map(|q| (q, ProofCategory::Branch))
                    .ok_or_else(|| format!("w{width} cc{cc}: no family member"));
            }
        }
        Err("no flag writer in block window".into())
    }

    /// Select a CSET theorem inside an independently checked complete scalar
    /// body. The owner binds operands and the whole source; the shared producer
    /// walk (`aarch64_flag_consumer_proofs::reaching_flag_producer`, restricted
    /// to the source-bound scalar-body instructions) identifies the actual
    /// reaching comparison and condition for formal replay: an integer CMP
    /// selects its `Icmp_<cc>_I<w>` theorem, an FCMP the FCMP -> CSET
    /// obligation of its width and condition.
    ///
    /// THE SOURCE-CONDITION BINDING (hole 1 of `2e194289f`). Both theorems are
    /// named by `cc`, read off the emitted instruction — the defect
    /// `cset_reaching_cmp_query` had. The argument that this lane is exempt
    /// because the owner's whole-body check constrains the condition was
    /// EXECUTED rather than accepted (`source_bound_diamond_tests`): for a CSET
    /// whose value the body OBSERVES it holds — every one of the fifteen other
    /// condition immediates is refused by the body check, at both widths, in
    /// both body shapes. For a CSET whose value is DEAD it is false: the body
    /// check never reads the register, so every condition with an `Icmp_*`
    /// family member built the frame and this query selected `Icmp_<that cc>`
    /// — a theorem the source does not contain, chosen by the instruction under
    /// test. The condition is therefore bound to the SOURCE exactly as the walk
    /// binds it: the CSET must be stamped with the comparison it lowers (digest
    /// checked against the owner's own source), be that stamp's ONLY `CSET`,
    /// carry the ONE condition a single-`CSET` lowering of that comparison puts
    /// on it (`from_intcc` / `from_floatcc`; the two-`CSET` FP forms, whose
    /// codes would need a role binding, are refused), and read the flags of a
    /// producer of the SAME kind (`CMP` for an `Icmp`, `FCMP` for an `Fcmp`).
    pub(crate) fn source_bound_cset_query(
        frame: &crate::source_bound_frame::SourceBoundFrame<'_>,
        id: InstId,
    ) -> Option<(&'static str, ProofCategory)> {
        use crate::aarch64_flag_consumer_proofs as flags;
        use AArch64Opcode as M;
        use trust_cg_lower::instructions::Opcode as LirOpcode;
        let machine = frame.machine();
        let inst = machine.insts.get(id.0 as usize)?;
        let [MachOperand::PReg(destination), MachOperand::Imm(cc)] = inst.operands.as_slice()
        else {
            return None;
        };
        if inst.opcode != M::CSet || !matches!(destination.encoding(), 0..=17 | 32..=49) {
            return None;
        }
        let (block, position) = machine.blocks.iter().find_map(|block| {
            block
                .insts
                .iter()
                .position(|candidate| *candidate == id)
                .map(|position| (block, position))
        })?;
        let trust_cg_ir::LoweringProvenance::SourceInst {
            id: stamp, digest, ..
        } = machine.inst_lowering_provenance(id)
        else {
            return None;
        };
        let lowered = frame
            .source()
            .blocks
            .get(&trust_cg_lower::instructions::Block(stamp.block))?
            .instructions
            .get(stamp.index as usize)?;
        let single =
            crate::aarch64_source_condition::cset_conditions_for_emission_count(&lowered.opcode, 1);
        if lowered.lowering_digest() != digest
            || !matches!(
                lowered.opcode,
                LirOpcode::Icmp { .. } | LirOpcode::Fcmp { .. }
            )
            || Self::same_source_cset_count(machine, &block.insts, position)? != 1
            || single.codes().len() != 1
            || !single.contains(*cc)
        {
            return None;
        }
        let (_, previous) = flags::reaching_flag_producer(
            machine,
            &block.insts,
            position,
            flags::TransparencyPolicy::SourceBoundScalarBody,
        )
        .ok()?;
        match (previous.opcode, &lowered.opcode) {
            (M::CmpRR | M::CmpRI, LirOpcode::Icmp { .. }) => {
                let width = previous.operands.first().and_then(operand_reg_width_bits)?;
                Self::icmp_family_query(PreciseFamily::Icmp, *cc, width)
                    .map(|query| (query, ProofCategory::Comparison))
            }
            (M::Fcmp, LirOpcode::Fcmp { .. }) => {
                flags::fcmp_cset_query(flags::fcmp_width(previous)?, u8::try_from(*cc).ok()?)
                    .map(|query| (query, flags::FLAG_CONSUMER_CATEGORY))
            }
            _ => None,
        }
    }

    /// With `TCG_PRECISE_CITATIONS` set, replace the `"cmp"` / `"condbr"`
    /// fragment by the instruction's own family member when it resolves;
    /// otherwise (or with the flag unset) return the query unchanged.
    fn refine_citation(
        &self,
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
        inst: &MachInst,
        query: &'static str,
        category: ProofCategory,
    ) -> (&'static str, ProofCategory) {
        if !precise_citations_enabled() {
            return (query, category);
        }
        let refined = match (query, category) {
            ("cmp", ProofCategory::Comparison) => {
                Self::precise_cmp_query_why(func, block_insts, block_pos, inst)
                    .map(|q| (q, category))
            }
            ("condbr", ProofCategory::Branch) => {
                Self::precise_condbr_query_why(func, block_insts, block_pos, inst)
            }
            _ => return (query, category),
        };
        match refined {
            Ok((r, cat)) if self.registry_proof_for_query(r, cat).is_some() => {
                if citation_trace_enabled() {
                    eprintln!(
                        "TCG_CITE refined opcode={:?} {query} -> {r} [{cat:?}]",
                        inst.opcode
                    );
                }
                (r, cat)
            }
            Ok((r, cat)) => {
                if citation_trace_enabled() {
                    eprintln!(
                        "TCG_CITE fallback opcode={:?} {query} ({r} not in registry [{cat:?}])",
                        inst.opcode
                    );
                }
                (query, category)
            }
            Err(why) => {
                if citation_trace_enabled() {
                    let shape: Vec<String> = block_insts
                        .iter()
                        .filter_map(|id| func.insts.get(id.0 as usize))
                        .map(|i| format!("{:?}{:?}", i.opcode, i.operands))
                        .collect();
                    eprintln!(
                        "TCG_CITE fallback opcode={:?} {query} ({why}) fn={} pos={block_pos} block=[{}]",
                        inst.opcode,
                        func.name,
                        shape.join(" ; ")
                    );
                }
                (query, category)
            }
        }
    }

    /// Map a (width, consumer condition) pair to the registered standalone-TST
    /// obligation query, or None for conditions that must FAIL CLOSED.
    ///
    /// Covered: the N/Z-derived conditions EQ/NE/MI/PL/GE/LT/GT/LE (GE/LT and
    /// GT/LE are well-defined because TST clears V; their obligations pin that
    /// V-clear). NEVER covered: the C/V-OBSERVERS HS/LO/HI/LS/VS/VC — after
    /// TST those conditions are architecturally CONSTANT, so a consumer
    /// reading one is exactly the miscompile shape `and_cmp_fuse`'s carry
    /// guard (`cond_reads_carry`) forbids; crediting the TST through the
    /// true-but-constant HI/LS model pins would stamp wrong code Verified
    /// (review, CRITICAL). Failing closed keeps it a compile error.
    fn tst_condition_query(width: u32, cc: i64) -> Option<&'static str> {
        Some(match (width, cc) {
            (64, 0) => "tst w64: eq",
            (64, 1) => "tst w64: ne",
            (64, 4) => "tst w64: mi",
            (64, 5) => "tst w64: pl",
            (64, 10) => "tst w64: ge",
            (64, 11) => "tst w64: lt",
            (64, 12) => "tst w64: gt",
            (64, 13) => "tst w64: le",
            (32, 0) => "tst w32: eq",
            (32, 1) => "tst w32: ne",
            (32, 4) => "tst w32: mi",
            (32, 5) => "tst w32: pl",
            (32, 10) => "tst w32: ge",
            (32, 11) => "tst w32: lt",
            (32, 12) => "tst w32: gt",
            (32, 13) => "tst w32: le",
            _ => return None,
        })
    }

    /// Reads and opaque effects precede definite kills: an instruction that
    /// reads and writes NZCV still observes the incoming flags. Keep calls
    /// neutral, as this verifier's existing contract requires, rather than
    /// adopting the optimizer's caller-saved kill rule.
    fn nzcv_liveness_effect(inst: &MachInst) -> NzcvLivenessEffect {
        use trust_cg_opt::effects::{definitely_writes_flags, nzcv_unknown, reads_nzcv};
        if Self::nzcv_consumer_cc_pos(inst.opcode).is_some() || reads_nzcv(inst) {
            NzcvLivenessEffect::Reads
        } else if nzcv_unknown(inst)
            || (inst.opcode.is_pseudo() && inst.opcode != AArch64Opcode::Nop)
            // MRS permits arbitrary system registers, including NZCV; the
            // opcode-level reader table cannot establish transparency here.
            || matches!(inst.opcode, AArch64Opcode::Mrs | AArch64Opcode::TailCall)
            || (Self::nzcv_control_boundary(inst)
                && !inst
                    .opcode
                    .default_flags()
                    .contains(trust_cg_ir::InstFlags::IS_BRANCH)
                && !inst
                    .opcode
                    .default_flags()
                    .contains(trust_cg_ir::InstFlags::IS_TERMINATOR))
        {
            NzcvLivenessEffect::Unknown
        } else if Self::nzcv_control_boundary(inst) {
            NzcvLivenessEffect::Neutral
        } else if definitely_writes_flags(inst.opcode) {
            NzcvLivenessEffect::Kill
        } else {
            NzcvLivenessEffect::Neutral
        }
    }

    fn nzcv_control_boundary(inst: &MachInst) -> bool {
        let flags = inst.flags.union(inst.opcode.default_flags());
        flags.contains(trust_cg_ir::InstFlags::IS_BRANCH)
            || flags.contains(trust_cg_ir::InstFlags::IS_TERMINATOR)
    }

    fn nzcv_conditional_boundary(inst: &MachInst) -> bool {
        matches!(
            inst.opcode,
            AArch64Opcode::Cbz
                | AArch64Opcode::Cbnz
                | AArch64Opcode::Tbz
                | AArch64Opcode::Tbnz
                | AArch64Opcode::BCond
                | AArch64Opcode::Bcc
        )
    }

    /// Conservatively decide whether any reachable path can read incoming
    /// NZCV before a definite non-reading writer or function exit. Reader-free
    /// cycles are safe; this does not establish termination. Opaque effects,
    /// malformed references, a non-exiting leaf or
    /// the 64-block/pending-work bound fail closed. Conditional fallthrough is
    /// still scanned, but a later writer cannot kill flags on a taken edge.
    /// Cycles and shared successors are visited once, without recursive calls.
    fn nzcv_dead_on_entry(
        func: &MachFunction,
        block_id: trust_cg_ir::BlockId,
        visited: &mut std::collections::HashSet<trust_cg_ir::BlockId>,
    ) -> bool {
        if visited.contains(&block_id) {
            return true;
        }
        let mut work = vec![block_id];
        while let Some(next) = work.pop() {
            if visited.contains(&next) {
                continue;
            }
            if visited.len() >= NZCV_LIVENESS_BLOCK_LIMIT {
                return false;
            }
            let Some(block) = func.blocks.get(next.0 as usize) else {
                return false;
            };
            visited.insert(next);
            let mut dead = false;
            let mut live_taken_edge = false;
            for &inst_id in &block.insts {
                let Some(inst) = func.insts.get(inst_id.0 as usize) else {
                    return false;
                };
                match Self::nzcv_liveness_effect(inst) {
                    NzcvLivenessEffect::Reads | NzcvLivenessEffect::Unknown => return false,
                    NzcvLivenessEffect::Kill => {
                        dead = !live_taken_edge;
                        break;
                    }
                    NzcvLivenessEffect::Neutral => {}
                }
                if matches!(inst.opcode, AArch64Opcode::Ret | AArch64Opcode::Brk) {
                    dead = !live_taken_edge;
                    break;
                }
                if Self::nzcv_control_boundary(inst) {
                    if Self::nzcv_conditional_boundary(inst) {
                        live_taken_edge = true;
                    } else {
                        break;
                    }
                }
            }
            if dead {
                continue;
            }
            if block.succs.is_empty() {
                return false;
            }
            for &successor in block.succs.iter().rev() {
                if !visited.contains(&successor) && !work.contains(&successor) {
                    if work.len() >= NZCV_LIVENESS_BLOCK_LIMIT {
                        return false;
                    }
                    work.push(successor);
                }
            }
        }
        true
    }

    /// Whether NZCV is dead after the instruction at `pos` of `block_id`:
    /// `Some(true)` dead, `Some(false)` a flag reader on some path before any
    /// writer, `None` undecided (an opaque pseudo, or a successor
    /// [`Self::nzcv_dead_on_entry`] cannot clear).
    fn nzcv_dead_after(
        func: &MachFunction,
        block_id: trust_cg_ir::BlockId,
        pos: usize,
    ) -> Option<bool> {
        let block = func.blocks.get(block_id.0 as usize)?;
        func.insts.get(block.insts.get(pos)?.0 as usize)?;
        let mut live_taken_edge = false;
        for &inst_id in block.insts.get(pos.checked_add(1)?..)? {
            let inst = func.insts.get(inst_id.0 as usize)?;
            match Self::nzcv_liveness_effect(inst) {
                NzcvLivenessEffect::Reads => return Some(false),
                NzcvLivenessEffect::Unknown => return None,
                NzcvLivenessEffect::Kill => {
                    if !live_taken_edge {
                        return Some(true);
                    }
                    break;
                }
                NzcvLivenessEffect::Neutral => {}
            }
            if matches!(inst.opcode, AArch64Opcode::Ret | AArch64Opcode::Brk) {
                if !live_taken_edge {
                    return Some(true);
                }
                break;
            }
            if Self::nzcv_control_boundary(inst) {
                if Self::nzcv_conditional_boundary(inst) {
                    live_taken_edge = true;
                } else {
                    break;
                }
            }
        }
        if block.succs.is_empty() {
            return None;
        }
        let mut visited = std::collections::HashSet::new();
        block
            .succs
            .iter()
            .all(|&s| Self::nzcv_dead_on_entry(func, s, &mut visited))
            .then_some(true)
    }

    /// L04-P12: the verdict on a trap row, or `None` for any other row.
    ///
    /// A carrier (before the expansion) and an unconditional trap are judged
    /// by their stated expansion; the `BRK` that closes an expansion recorded
    /// in `func.trap_expansions` is judged by the words of the instructions
    /// that expansion left, which must still be contiguous in its block, and
    /// a flag-setting expansion must leave NZCV dead. A refuted expansion
    /// fails the row. A holding conditional expansion is credited only under
    /// an enforced source-bound replay policy, when its register-renamed
    /// obligation, replayed through the verification request
    /// ([`TrapReplayRoute`]: the request's admitted AY, policy and refusals),
    /// gets a proof the explicit Clean checker accepts; otherwise the row
    /// stays unverified
    /// ([`crate::aarch64_trap_expansion::TRAP_EXPANSION_IS_NOT_CREDIT`]). A
    /// holding unconditional trap has no condition to bind and is skipped
    /// with that reason. A carrier outside the model is refused by name.
    ///
    /// `replay_allowed` is false where the trap-guard layer
    /// (`aarch64_trap_guard`) already fails, refuses or cannot bind the row:
    /// no replay can then credit it, so none is made.
    #[allow(clippy::too_many_arguments)]
    fn trap_row_result(
        &self,
        func: &MachFunction,
        position: (trust_cg_ir::BlockId, usize),
        inst_id: InstId,
        inst: &MachInst,
        closing: &std::collections::HashMap<InstId, usize>,
        route: &TrapReplayRoute<'_, '_>,
        replay_allowed: bool,
    ) -> Option<InstructionVerificationResult> {
        use crate::aarch64_trap_expansion::{
            self as trap, TRAP_EXPANSION_IS_NOT_CREDIT, TrapVerdict,
        };
        let (block_id, block_pos) = position;
        let (verdict, recorded) = if let Some(&index) = closing.get(&inst_id) {
            let record = &func.trap_expansions[index];
            let block = &func.blocks[block_id.0 as usize];
            let n = record.insts.len();
            let in_place = block_pos + 1 >= n
                && block.insts.get(block_pos + 1 - n..=block_pos) == Some(record.insts.as_slice());
            let members: Option<Vec<&MachInst>> = record
                .insts
                .iter()
                .map(|id| func.insts.get(id.0 as usize))
                .collect();
            let verdict = match (in_place, members) {
                (true, Some(members)) => {
                    trap::recorded_expansion_verdict(&record.carrier, &members)
                }
                _ => TrapVerdict::Refuted {
                    name: format!("A64 trap expansion {:?}", record.carrier.opcode),
                    detail: "the recorded expansion is no longer contiguous before its BRK".into(),
                },
            };
            (verdict, Some(record))
        } else if trap::is_trap_opcode(inst.opcode) {
            (trap::carrier_verdict(inst), None)
        } else {
            return None;
        };
        // A flag-setting expansion overwrites NZCV: nothing may read the
        // flags it leaves.
        let writes_flags = recorded.is_some_and(|record| {
            record.insts.iter().any(|id| {
                func.insts.get(id.0 as usize).is_some_and(|member| {
                    <trust_cg_ir::target_info::AArch64Target as trust_cg_ir::target_info::TargetInfo>::writes_flags(member.opcode)
                })
            })
        });
        let flags = if writes_flags {
            Self::nzcv_dead_after(func, block_id, block_pos)
        } else {
            Some(true)
        };
        let (name, method, replay) = match (verdict, flags) {
            (TrapVerdict::Refuted { name, detail }, _) => {
                return Some(InstructionVerificationResult::Failed {
                    proof_name: name,
                    detail,
                });
            }
            (TrapVerdict::Refused { reason }, _) => {
                return Some(InstructionVerificationResult::Unverified { reason });
            }
            (TrapVerdict::Holds { name, .. }, Some(false)) => {
                return Some(InstructionVerificationResult::Failed {
                    proof_name: name,
                    detail: "the expansion overwrites NZCV that a later instruction reads".into(),
                });
            }
            (TrapVerdict::Holds { name, .. }, None) => {
                return Some(InstructionVerificationResult::Unverified {
                    reason: format!(
                        "`{name}` holds, but NZCV is not provably dead after the expansion"
                    ),
                });
            }
            (
                TrapVerdict::Holds {
                    name,
                    method,
                    replay: None,
                    ..
                },
                Some(true),
            ) => {
                return Some(InstructionVerificationResult::Skipped {
                    reason: format!(
                        "{:?} is an unconditional trap: `{name}` holds ({method}); it has no \
                         condition to bind",
                        inst.opcode
                    ),
                });
            }
            (
                TrapVerdict::Holds {
                    name,
                    method,
                    replay: Some(replay),
                    ..
                },
                Some(true),
            ) => (name, method, replay),
        };
        if route.xcheck_mode != ProvenanceXCheckMode::Enforce
            || !self.config.replays_source_bound_obligations()
        {
            return Some(InstructionVerificationResult::Unverified {
                reason: format!(
                    "{TRAP_EXPANSION_IS_NOT_CREDIT}: `{name}` holds ({method}); no live replay \
                     (not an enforced source-bound replay policy)"
                ),
            });
        }
        if !replay_allowed {
            return Some(InstructionVerificationResult::Unverified {
                reason: format!(
                    "{TRAP_EXPANSION_IS_NOT_CREDIT}: `{name}` holds ({method}); no live replay \
                     (the trap-guard obligation fails, refuses or cannot bind this row)"
                ),
            });
        }
        Some(match route.replay(self, &replay) {
            (Some(VerificationResult::Valid), _) => InstructionVerificationResult::Verified {
                proof_name: name,
                category: ProofCategory::Branch,
                strength: VerificationStrength::Formal,
                degenerate: false,
            },
            (Some(VerificationResult::Invalid { counterexample }), _) => {
                InstructionVerificationResult::Failed {
                    proof_name: name,
                    detail: format!(
                        "the request's AY refutes an expansion decided to hold in process: \
                         {counterexample}"
                    ),
                }
            }
            (Some(VerificationResult::Unknown { reason }), _) => {
                InstructionVerificationResult::Failed {
                    proof_name: name,
                    detail: format!("Unknown: {reason}"),
                }
            }
            (None, why) => InstructionVerificationResult::Unverified {
                reason: format!(
                    "{TRAP_EXPANSION_IS_NOT_CREDIT}: `{name}` holds ({method}); live replay: {}",
                    why.as_deref().unwrap_or("no Clean-checked proof")
                ),
            },
        })
    }

    fn generated_fp_sp_relative_addressing_query(
        inst: &MachInst,
    ) -> Option<(&'static str, ProofCategory)> {
        if !matches!(inst.opcode, AArch64Opcode::AddRI | AArch64Opcode::SubRI) {
            return None;
        }

        let [MachOperand::PReg(dst), base, MachOperand::Imm(_)] = inst.operands.as_slice() else {
            return None;
        };
        if matches!(*dst, X29 | SP) || !Self::is_frame_base_operand(base) {
            return None;
        }

        Some((
            "fp/sp-relative addressing equivalence",
            ProofCategory::FrameLayout,
        ))
    }

    fn generated_frame_address_materialization_query(
        inst: &MachInst,
    ) -> Option<(&'static str, ProofCategory)> {
        let query = match inst.opcode {
            // #62: "FrameLayout: large offset materialization (ADD base, offset)"
            // was a degenerate X==X and was RETRACTED, so the ADD large-offset form
            // has no value-proof now (None). The SUB large-NEGATIVE form proof is
            // GENUINE and remains.
            AArch64Opcode::AddRR => return None,
            AArch64Opcode::SubRR => "large negative offset materialization",
            _ => return None,
        };

        let [MachOperand::PReg(dst), base, MachOperand::PReg(offset_reg)] =
            inst.operands.as_slice()
        else {
            return None;
        };
        if dst != offset_reg {
            return None;
        }
        if !Self::is_frame_materialization_scratch_reg(*dst) || !Self::is_frame_base_operand(base) {
            return None;
        }

        Some((query, ProofCategory::FrameLayout))
    }

    fn generated_stack_slot_spill_or_reload_query(
        inst: &MachInst,
    ) -> Option<(&'static str, ProofCategory)> {
        let query = match inst.opcode {
            AArch64Opcode::LdrRI => "spill/reload semantic roundtrip",
            AArch64Opcode::StrRI => "spill offset non-interference",
            _ => return None,
        };

        let Some(MachOperand::PReg(reg)) = inst.operands.first() else {
            return None;
        };
        if !Self::is_spill_scratch_reg(*reg) {
            return None;
        }

        let addr = inst.operands.get(1)?;
        if !Self::is_stack_slot_address(addr) {
            return None;
        }

        Some((query, ProofCategory::RegAlloc))
    }

    fn generated_stp_spill_scalarization_query(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
    ) -> Option<(&'static str, ProofCategory)> {
        let inst = Self::inst_at_block_pos(func, block_insts, block_pos)?;
        let offset = Self::scalarized_stp_spill_store_offset(inst)?;
        let store0_pos = match offset {
            0 => block_pos,
            8 => block_pos.checked_sub(2)?,
            _ => return None,
        };

        if !Self::matches_stp_spill_scalarization_window(func, block_insts, store0_pos) {
            return None;
        }

        // #62: "FrameLayout: stp spill scalarization preserves two stores" was a
        // degenerate X==X and was RETRACTED — no value-proof for this window now.
        // (The window is still recognized; it simply binds no proof, so the stores
        // fall through to their ordinary Memory load/store coverage.)
        None
    }

    fn scalarized_stp_spill_store_offset(inst: &MachInst) -> Option<i64> {
        if inst.opcode != AArch64Opcode::StrRI {
            return None;
        }

        let [
            MachOperand::PReg(value),
            MachOperand::PReg(base),
            MachOperand::Imm(offset),
        ] = inst.operands.as_slice()
        else {
            return None;
        };

        (*value == X17 && *base == X16 && matches!(*offset, 0 | 8)).then_some(*offset)
    }

    fn matches_stp_spill_scalarization_window(
        func: &MachFunction,
        block_insts: &[InstId],
        store0_pos: usize,
    ) -> bool {
        let Some(value0_load_pos) = store0_pos.checked_sub(1) else {
            return false;
        };
        let value1_load_pos = store0_pos + 1;
        let store1_pos = store0_pos + 2;

        Self::has_stp_spill_scalarization_base_setup(func, block_insts, value0_load_pos)
            && Self::is_spill_reload_into(func, block_insts, value0_load_pos, X17)
            && Self::is_scalarized_stp_spill_store_at(func, block_insts, store0_pos, 0)
            && Self::is_spill_reload_into(func, block_insts, value1_load_pos, X17)
            && Self::is_scalarized_stp_spill_store_at(func, block_insts, store1_pos, 8)
    }

    fn has_stp_spill_scalarization_base_setup(
        func: &MachFunction,
        block_insts: &[InstId],
        value0_load_pos: usize,
    ) -> bool {
        let Some(prev_pos) = value0_load_pos.checked_sub(1) else {
            return false;
        };
        if Self::is_spill_reload_into(func, block_insts, prev_pos, X16) {
            return true;
        }

        let Some(base_load_pos) = prev_pos.checked_sub(1) else {
            return false;
        };
        Self::is_x16_pair_offset_adjust(func, block_insts, prev_pos)
            && Self::is_spill_reload_into(func, block_insts, base_load_pos, X16)
    }

    fn is_scalarized_stp_spill_store_at(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
        expected_offset: i64,
    ) -> bool {
        Self::inst_at_block_pos(func, block_insts, block_pos)
            .and_then(Self::scalarized_stp_spill_store_offset)
            == Some(expected_offset)
    }

    fn is_spill_reload_into(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
        expected_dst: PReg,
    ) -> bool {
        let Some(inst) = Self::inst_at_block_pos(func, block_insts, block_pos) else {
            return false;
        };
        if inst.opcode != AArch64Opcode::LdrRI {
            return false;
        }
        let [MachOperand::PReg(dst), addr] = inst.operands.as_slice() else {
            return false;
        };
        *dst == expected_dst && Self::is_stack_slot_address(addr)
    }

    fn is_x16_pair_offset_adjust(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
    ) -> bool {
        let Some(inst) = Self::inst_at_block_pos(func, block_insts, block_pos) else {
            return false;
        };
        if !matches!(inst.opcode, AArch64Opcode::AddRI | AArch64Opcode::SubRI) {
            return false;
        }
        matches!(
            inst.operands.as_slice(),
            [MachOperand::PReg(dst), MachOperand::PReg(src), MachOperand::Imm(_)]
                if *dst == X16 && *src == X16
        )
    }

    fn inst_at_block_pos<'a>(
        func: &'a MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
    ) -> Option<&'a MachInst> {
        let inst_id = block_insts.get(block_pos)?;
        func.insts.get(inst_id.0 as usize)
    }

    fn generated_emergency_spill_slot_address_query(
        inst: &MachInst,
    ) -> Option<(&'static str, ProofCategory)> {
        if !matches!(inst.opcode, AArch64Opcode::LdrRI | AArch64Opcode::StrRI) {
            return None;
        }

        if !matches!(inst.operands.first(), Some(MachOperand::PReg(_))) {
            return None;
        }

        let Some(MachOperand::MemOp { base, offset }) = inst.operands.get(1) else {
            return None;
        };
        if *offset != 0 || !Self::is_frame_materialization_scratch_reg(*base) {
            return None;
        }

        // #62: "FrameLayout: emergency spill slot address via X16" was a degenerate
        // X==X and was RETRACTED — no value-proof for this form now. Returning None
        // lets the load/store fall through to its ordinary Memory effective-address
        // coverage (which is itself allowlisted pending a faithful encoder).
        None
    }

    fn is_spill_scratch_reg(reg: PReg) -> bool {
        matches!(reg, X16 | W16 | X17 | W17)
    }

    fn is_frame_materialization_scratch_reg(reg: PReg) -> bool {
        matches!(reg, X16 | X17)
    }

    fn is_frame_base_operand(operand: &MachOperand) -> bool {
        matches!(operand, MachOperand::PReg(reg) if matches!(*reg, X29 | SP))
            || matches!(operand, MachOperand::Special(SpecialReg::SP))
    }

    fn is_stack_slot_address(operand: &MachOperand) -> bool {
        match operand {
            MachOperand::StackSlot(_) | MachOperand::FrameIndex(_) => true,
            MachOperand::MemOp { base, .. } => *base == X29,
            _ => false,
        }
    }

    /// The fixed-registry proof the query mapping names for `(query, category)`:
    /// category-filtered, first name containing `query` (case-insensitive), in
    /// registration order.
    ///
    /// This is a DIAGNOSTIC resolution only (precise-citation refinement and the
    /// query-resolution golden fixture). The walk never credits an instruction
    /// with the theorem it returns: see
    /// [`InstructionVerificationResult::withdrawn_registry_credit`].
    fn registry_proof_for_query(
        &self,
        query: &'static str,
        category: ProofCategory,
    ) -> Option<&crate::proof_database::CategorizedProof> {
        let key = (category, query);
        if let Some(hit) = self
            .query_memo
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .get(&key)
        {
            return hit.map(|i| &self.db.all()[i]);
        }
        // The original resolution, in the database's category order.
        let index = self
            .db
            .all()
            .iter()
            .enumerate()
            .filter(|(_, p)| p.category == category)
            .find(|(_, p)| p.obligation.name.to_lowercase().contains(query))
            .map(|(i, _)| i);
        self.query_memo
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .insert(key, index);
        index.map(|i| &self.db.all()[i])
    }

    /// Every DISTINCT reconstruction-arm obligation the walk would discharge
    /// across `funcs`, in first-seen order, paired with its canonical theorem.
    /// Pure selection — nothing is discharged here — so the caller can fan the
    /// evaluation sweeps out before the walk reads their memo cells.
    ///
    /// Registry theorems are not enumerated: the walk no longer discharges any
    /// (substring and representative credit are withdrawn), so warming them
    /// would spend sweeps and checker processes on evidence nothing reads.
    pub fn reconstructed_obligations_for_functions(
        &self,
        funcs: &[&MachFunction],
    ) -> Vec<(ProofObligation, ProofObligation)> {
        let mut seen_recon: std::collections::HashSet<ProofObligation> =
            std::collections::HashSet::new();
        let mut recon: Vec<(ProofObligation, ProofObligation)> = Vec::new();
        let trace = std::env::var_os("TCG_TIME_SWEEP").is_some();
        let mut t_recon = std::time::Duration::ZERO;
        let (mut n_insts, mut n_recon_built) = (0usize, 0usize);
        for func in funcs {
            for block in &func.blocks {
                for &inst_id in &block.insts {
                    let Some(inst) = func.insts.get(inst_id.0 as usize) else {
                        continue;
                    };
                    if crate::aarch64_trap_expansion::is_trap_opcode(inst.opcode)
                        || inst.opcode.is_pseudo()
                    {
                        continue;
                    }
                    // Mirror the walk's reconstruction gate: EXACTLY
                    // `try_reconstruct_pilot`'s two `?`s. Its evaluation memo key
                    // is the exact reconstructed instance plus config; carrying
                    // the canonical theorem here keeps pre-warm enumeration
                    // drift-free for the day an exact source-binding token
                    // permits Formal reuse.
                    n_insts += 1;
                    if opcode_to_source_op(inst.opcode).is_some() {
                        let t0 = std::time::Instant::now();
                        let built = reconstruct_alu_obligation(inst);
                        t_recon += t0.elapsed();
                        if let Some(ob) = built {
                            n_recon_built += 1;
                            if seen_recon.insert(ob.clone()) {
                                let canonical = canonical_reconstruct_obligation(inst)
                                    .unwrap_or_else(|| ob.clone());
                                recon.push((ob, canonical));
                            }
                            continue;
                        }
                    }
                    // Mirror the walk's PAIR MEMORY arm (`try_pair_memory`, tried
                    // only when the pilot arm declines). Its obligation is
                    // reconstructed from the real operands and lands in the
                    // same content-keyed evaluation memo cell, so pre-warming
                    // it here is verdict-identical and keeps the expensive
                    // first touch off the serial walk.
                    let t0 = std::time::Instant::now();
                    let built = crate::aarch64_pair_memory_proofs::pair_memory_obligation(inst);
                    let decomposition = crate::aarch64_memory_effect::memory_effect(inst);
                    t_recon += t0.elapsed();
                    if let Some(ob) = built {
                        n_recon_built += 1;
                        if seen_recon.insert(ob.clone()) {
                            recon.push((ob.clone(), ob));
                        }
                    }
                    // Mirror `with_memory_effect`, which the walk applies to
                    // every pair and scalar memory row its lane admits: the
                    // parts it hands the sampling lane
                    // (`aarch64_memory_effect::needs_sampling`) land in the
                    // same content-keyed evaluation memo cells. A ground part,
                    // or one decided exactly, is decided in the walk without
                    // sampling.
                    for part in decomposition.into_iter().flat_map(|d| d.parts) {
                        if crate::aarch64_memory_effect::needs_sampling(&part)
                            && seen_recon.insert(part.obligation.clone())
                        {
                            recon.push((part.obligation.clone(), part.obligation));
                        }
                    }
                }
            }
        }
        if trace {
            eprintln!(
                "TCG_ENUM_SPLIT insts={n_insts} recon_built={n_recon_built} recon_distinct={} \
                 reconstruct={:.2}ms",
                recon.len(),
                t_recon.as_secs_f64() * 1000.0,
            );
        }
        recon
    }

    /// Discharge one reconstruction-arm obligation exactly as
    /// `try_reconstruct_pilot` would — same reconstructed instance and config,
    /// hence the same evaluation memo cell. The canonical theorem is retained
    /// for exact-query identity but cannot confer Formal credit without an
    /// exact source-binding token.
    pub fn discharge_reconstructed_obligation_now(
        &self,
        instance: &ProofObligation,
        canonical: &ProofObligation,
    ) {
        let _ = crate::lowering_proof::discharge_reconstructed_obligation(
            instance,
            canonical,
            &self.config,
        );
    }

    /// PAIR MEMORY (`STP`/`LDP`, signed-offset and pre/post-index writeback).
    ///
    /// Reconstructs the obligation from the REAL opcode and positional
    /// operands (see [`crate::aarch64_pair_memory_proofs`]) and discharges it
    /// on the same reconstruction lane the ALU pilot uses. The obligation
    /// asserts that the architectural pair access denoted by the instruction's
    /// own encoded word agrees with the scalarized two-access-plus-base-update
    /// denotation of its operands — both transfers at `base ± offset` and the
    /// base written back by exactly the immediate — so a displaced, mis-scaled,
    /// wrongly-sized, transposed or writeback-losing access REFUTES.
    ///
    /// That obligation is the row's REFUTATION check: a refutation is
    /// `Failed`. Its inputs include a 64-bit base and 64-bit lanes, so a
    /// holding verdict is `Statistical` and is reported
    /// (`STATISTICAL_EVIDENCE_IS_NOT_CREDIT`, naming the pair obligation),
    /// never credited. Credit is decided only by [`apply_bound_memory_rule`]
    /// (owner ruling 2026-09-29): `Formal` when this obligation held, the
    /// word it judged decodes to the row's pair FORM
    /// ([`crate::aarch64_pair_memory_forms`]), and that form theorem has a
    /// committed certificate that the independent checker replays; otherwise
    /// the sampled reason plus
    /// [`crate::bound_memory_authority::BOUND_MEMORY_FORMAL_ONLY`].
    ///
    /// `None` means the instruction is not an admitted pair shape (wrong
    /// arity, virtual or ill-classed operand, misaligned or out-of-range
    /// offset, duplicate/discarded load destination, writeback/base overlap).
    /// Those fall through to the terminal `no proof mapping for opcode` arm
    /// exactly as before: this lane widens no admission and exempts nothing.
    ///
    /// This is deliberately NOT an `opcode_to_proof_query` mapping. Opcode
    /// identity cannot authenticate a pair access, so the broad
    /// `("load", Memory)` / `("store", Memory)` searches stay refused for every
    /// pair opcode (`opcode_to_proof_query` still returns `None` for all six).
    fn try_pair_memory(
        &self,
        inst: &MachInst,
        request: Option<&crate::function_request::FunctionVerificationRequest>,
    ) -> Option<InstructionVerificationResult> {
        // The word the concrete-word obligation judges: the re-derived one,
        // or (tests only) the seam's.
        #[cfg(test)]
        let judged = pair_word_seam::word();
        #[cfg(not(test))]
        let judged: Option<u32> = None;
        let (obligation, word) = match judged {
            Some(word) => (
                crate::aarch64_pair_memory_proofs::pair_memory_obligation_from_word(inst, word)?,
                word,
            ),
            None => crate::aarch64_pair_memory_proofs::pair_memory_obligation_and_word(inst)?,
        };
        let (vresult, strength) = crate::lowering_proof::discharge_reconstructed_obligation(
            &obligation,
            &obligation,
            &self.config,
        );
        // Rule clause 2's evidence: the check ran on this row and held, over
        // this word (clause 3 decodes it).
        let refutation = crate::bound_memory_authority::BoundMemoryRefutation::pair_concrete_word(
            word, &vresult,
        );
        debug_assert!(
            obligation.is_reconstructed(),
            "pair_memory_obligation must tag Reconstructed provenance"
        );
        // The concrete-word obligation is the lane's REFUTATION check only: a
        // refutation fails the row, and its sampled `Valid` is reported, never
        // credited. Credit comes solely from the Formal-only bound-memory rule.
        let checked = InstructionVerificationResult::from_discharge(
            &obligation.name,
            ProofCategory::Memory,
            vresult,
            strength,
            // The two sides are structurally distinct by construction (`true`
            // against the conjunction), so this is not an X==X binding.
            obligation.is_degenerate(),
        );
        Some(apply_bound_memory_rule(
            inst,
            checked,
            refutation,
            &self.config,
            request,
        ))
    }

    /// WORD-BOUND MEMORY EFFECT, applied to the row an admitted memory
    /// instruction's own lane produced: the pair lane ([`Self::try_pair_memory`]),
    /// the instruction-derived lane ([`Self::try_instruction_word`]), or, for
    /// the NEON `LD1`/`ST1` post-index transfers no lane admits, the registry
    /// arm's withdrawn-credit row, each already judged by the Formal-only
    /// bound-memory rule ([`apply_bound_memory_rule`], owner ruling
    /// 2026-09-29). Every instruction
    /// [`crate::aarch64_memory_effect::memory_effect`] admits reaches one of
    /// those three, so the walk applies this to each of them; any other row,
    /// and a `Failed` or `Skipped` one, is returned unchanged.
    ///
    /// The decomposition is a second REFUTATION check and a diagnostic, never
    /// credit, and it never removes credit:
    ///
    /// * every part is decided in process
    ///   ([`crate::aarch64_memory_effect::decide_in_process`]: exactly when
    ///   the part is ground or `decide_exactly` decides it, by the sampling
    ///   lane otherwise). A refuted part FAILS the row, whatever the lane and
    ///   the rule concluded, a `Formal` credit included;
    /// * under an enforced, replaying policy, and only when the diagnostic
    ///   replay is requested ([`crate::diag::memory_effect_replay_enabled`]),
    ///   an uncredited row's parts are then replayed live, in order, until the
    ///   first without a Clean-checked certificate; a solver counterexample
    ///   fails the row;
    /// * a row the rule credited stays credited (an undecided part only means
    ///   "not refuted"), and an uncredited row keeps its reason, prefix
    ///   included, followed by [`MEMORY_EFFECT_IS_NOT_CREDIT`], how the parts
    ///   were decided and how many have a Clean-checked certificate. A checked
    ///   part is not the evidence the rule admits (a committed certificate of
    ///   the row's FORM theorem that the independent checker replays), so it
    ///   is recorded, never credited.
    ///
    /// The parts are built over the word re-derived from the operands
    /// (ENC-5 binds the emitted word to it), or, in unit tests only, over the
    /// word [`memory_effect_word_seam`] names.
    pub(crate) fn with_memory_effect(
        &self,
        inst: &MachInst,
        row: InstructionVerificationResult,
        xcheck_mode: ProvenanceXCheckMode,
        context: Option<&crate::function_request::FunctionDischargeContext<'_>>,
        owned_request: &std::cell::OnceCell<crate::FunctionVerificationRequest>,
    ) -> InstructionVerificationResult {
        use crate::aarch64_memory_effect::{InProcess, decide_in_process};
        if matches!(
            row,
            InstructionVerificationResult::Failed { .. }
                | InstructionVerificationResult::Skipped { .. }
        ) {
            return row;
        }
        #[cfg(test)]
        let decomposition = match memory_effect_word_seam::word() {
            Some(word) => crate::aarch64_memory_effect::memory_effect_for_word(inst, word),
            None => crate::aarch64_memory_effect::memory_effect(inst),
        };
        #[cfg(not(test))]
        let decomposition = crate::aarch64_memory_effect::memory_effect(inst);
        let Some(decomposition) = decomposition else {
            return row;
        };
        let label = format!(
            "A64 memory effect {:?} {:#010x}",
            inst.opcode, decomposition.word
        );
        let parts = decomposition.parts.len();
        let (mut exact, mut sampled, mut undecided) = (0usize, None, None);
        for part in &decomposition.parts {
            match decide_in_process(part, &self.config) {
                InProcess::Holds(VerificationStrength::Statistical { sample_count }) => {
                    sampled = Some(sample_count);
                }
                InProcess::Holds(_) => exact += 1,
                InProcess::Refuted(counterexample) => {
                    return InstructionVerificationResult::Failed {
                        proof_name: part.obligation.name.clone(),
                        detail: format!("memory-effect part refuted in process: {counterexample}"),
                    };
                }
                InProcess::Undecided(reason) => {
                    undecided.get_or_insert((part.part, reason));
                }
            }
        }
        let InstructionVerificationResult::Unverified { reason: previous } = row else {
            // Credited by the Formal-only rule, and no part refuted it.
            return row;
        };
        let decided = match (&undecided, sampled) {
            (Some((part, reason)), _) => {
                format!("is undecided in process: part `{part}`: {reason}")
            }
            (None, Some(samples)) => format!(
                "holds in process: {exact} part(s) exactly, {} with no counterexample in \
                 {samples} sampled inputs",
                parts - exact
            ),
            (None, None) => format!("holds in process: all {parts} parts exactly"),
        };
        let replaying_policy = xcheck_mode == ProvenanceXCheckMode::Enforce
            && self.config.replays_source_bound_obligations();
        let requested = crate::diag::memory_effect_replay_enabled();
        let replays =
            (replaying_policy && requested && undecided.is_none()).then(|| match context {
                Some(context) => context.memory_effect(&decomposition),
                None => {
                    let request =
                        owned_request.get_or_init(|| self.capture_request_with_mode(xcheck_mode));
                    crate::function_request::FunctionDischargeContext::new(request)
                        .memory_effect(&decomposition)
                }
            });
        let certificates = match replays {
            None if undecided.is_some() => format!(
                "0 of {parts} parts have a Clean-checked certificate (not replayed: a part is \
                 undecided in process)"
            ),
            None if replaying_policy => format!(
                "0 of {parts} parts have a Clean-checked certificate ({MEMORY_EFFECT_REPLAY_NOT_REQUESTED})"
            ),
            None => format!(
                "0 of {parts} parts have a Clean-checked certificate (no live replay under this \
                 verification policy)"
            ),
            Some(verdicts) => {
                if let Some((part, counterexample)) = decomposition
                    .parts
                    .iter()
                    .zip(&verdicts)
                    .find_map(|(part, (verdict, _))| match verdict {
                        Some(VerificationResult::Invalid { counterexample }) => {
                            Some((part, counterexample))
                        }
                        _ => None,
                    })
                {
                    return InstructionVerificationResult::Failed {
                        proof_name: part.obligation.name.clone(),
                        detail: format!(
                            "memory-effect part refuted by the solver: {counterexample}"
                        ),
                    };
                }
                let checked = verdicts
                    .iter()
                    .take_while(|(verdict, _)| matches!(verdict, Some(VerificationResult::Valid)))
                    .count();
                if checked == parts {
                    format!("{MEMORY_EFFECT_EVERY_PART_CHECKED} ({parts} parts)")
                } else {
                    // The solver's own text names per-run temporary files;
                    // drop every path token so the reason is reproducible.
                    let why = verdicts[checked]
                        .1
                        .as_deref()
                        .unwrap_or("no verdict")
                        .split_whitespace()
                        .filter(|token| !token.contains('/'))
                        .collect::<Vec<_>>()
                        .join(" ");
                    format!(
                        "{checked} of {parts} parts have a Clean-checked certificate; the first \
                         without one is `{}` ({why})",
                        decomposition.parts[checked].part
                    )
                }
            }
        };
        InstructionVerificationResult::Unverified {
            reason: format!(
                "{previous}; {MEMORY_EFFECT_IS_NOT_CREDIT}: `{label}` {decided}; {certificates}"
            ),
        }
    }

    /// WORD-BOUND NEON LANE EFFECT (L04-P6), applied to the registry arm's
    /// row of an admitted NEON horizontal-reduction or permute instruction:
    /// the decomposition of its re-derived word
    /// ([`crate::aarch64_neon_lane_effect::neon_lane_effect`]; ENC-5 binds the
    /// emitted word to it) is decided in process, part by part. A refuted
    /// part FAILS the row; otherwise a credited row is returned unchanged and
    /// an uncredited row keeps its reason followed by
    /// [`NEON_LANE_EFFECT_IS_NOT_CREDIT`] and how the parts were decided. The
    /// parts are never credit and are not replayed live, so the clause names
    /// no Clean-checked certificate. Any other row, and a `Failed` or
    /// `Skipped` one, is returned unchanged.
    pub(crate) fn with_neon_lane_effect(
        &self,
        inst: &MachInst,
        row: InstructionVerificationResult,
    ) -> InstructionVerificationResult {
        match crate::aarch64_neon_lane_effect::neon_lane_effect(inst) {
            Some(decomposition) => self.with_neon_lane_decomposition(&decomposition, row),
            None => row,
        }
    }

    /// [`Self::with_neon_lane_effect`] over a given decomposition (the seam
    /// the corruption controls feed a mutated word's decomposition through).
    pub(crate) fn with_neon_lane_decomposition(
        &self,
        decomposition: &crate::aarch64_neon_lane_effect::NeonLaneEffectDecomposition,
        row: InstructionVerificationResult,
    ) -> InstructionVerificationResult {
        use crate::aarch64_neon_lane_effect::{InProcess, decide_in_process};
        if matches!(
            row,
            InstructionVerificationResult::Failed { .. }
                | InstructionVerificationResult::Skipped { .. }
        ) {
            return row;
        }
        let label = format!(
            "A64 NEON lane effect {:?} {:#010x}",
            decomposition.access.opcode, decomposition.word
        );
        let parts = decomposition.parts.len();
        let (mut exact, mut sampled, mut undecided) = (0usize, None, None);
        for part in &decomposition.parts {
            match decide_in_process(part, &self.config) {
                InProcess::Holds(VerificationStrength::Statistical { sample_count }) => {
                    sampled = Some(sample_count);
                }
                InProcess::Holds(_) => exact += 1,
                InProcess::Refuted(counterexample) => {
                    return InstructionVerificationResult::Failed {
                        proof_name: part.obligation.name.clone(),
                        detail: format!(
                            "NEON lane-effect part refuted in process: {counterexample}"
                        ),
                    };
                }
                InProcess::Undecided(reason) => {
                    undecided.get_or_insert((part.part, reason));
                }
            }
        }
        let InstructionVerificationResult::Unverified { reason: previous } = row else {
            return row;
        };
        let decided = match (&undecided, sampled) {
            (Some((part, reason)), _) => {
                format!("is undecided in process: part `{part}`: {reason}")
            }
            (None, Some(samples)) => format!(
                "holds in process: {exact} part(s) exactly, {} with no counterexample in \
                 {samples} sampled inputs",
                parts - exact
            ),
            (None, None) => format!("holds in process: all {parts} parts exactly"),
        };
        InstructionVerificationResult::Unverified {
            reason: format!(
                "{previous}; {NEON_LANE_EFFECT_IS_NOT_CREDIT}: `{label}` {decided}; 0 of {parts} \
                 parts have a Clean-checked certificate (no live replay lane)"
            ),
        }
    }

    /// Replay a bound memory row's parts under the request this walk replays
    /// under (the caller's context, or the walk's own request, captured once).
    fn memory_row_receipts(
        &self,
        row: &crate::aarch64_memory_source_binding::SourceBoundMemoryRow<'_>,
        xcheck_mode: ProvenanceXCheckMode,
        context: Option<&crate::function_request::FunctionDischargeContext<'_>>,
        owned_request: &std::cell::OnceCell<crate::FunctionVerificationRequest>,
    ) -> Vec<crate::aarch64_memory_source_binding::PartReceipt> {
        match context {
            Some(context) => context.memory_row(row),
            None => {
                let request =
                    owned_request.get_or_init(|| self.capture_request_with_mode(xcheck_mode));
                crate::function_request::FunctionDischargeContext::new(request).memory_row(row)
            }
        }
    }

    /// The source-bound route's evidence for a bound memory row: every part
    /// decided in process (a refutation fails the row), then, when none is
    /// undecided, every part replayed through the source-bound route and its
    /// receipts judged ([`crate::aarch64_memory_source_binding`]). Only
    /// [`BoundMemoryEvidence::Credited`] is credit.
    fn source_bound_memory_evidence(
        &self,
        row: &crate::aarch64_memory_source_binding::SourceBoundMemoryRow<'_>,
        xcheck_mode: ProvenanceXCheckMode,
        context: Option<&crate::function_request::FunctionDischargeContext<'_>>,
        owned_request: &std::cell::OnceCell<crate::FunctionVerificationRequest>,
    ) -> BoundMemoryEvidence {
        use crate::aarch64_memory_source_binding::MemoryCredit;
        let decided = match row.decide(&self.config) {
            Ok(decided) => decided,
            Err((proof_name, counterexample)) => {
                return BoundMemoryEvidence::Refuted {
                    proof_name,
                    detail: format!("memory-effect part refuted in process: {counterexample}"),
                };
            }
        };
        let parts = row.parts().len();
        let head = format!("`{}` bound to {}; {decided}", row.label(), row.binding());
        if decided.undecided.is_some() {
            return BoundMemoryEvidence::Uncredited(format!(
                "{head}; 0 of {parts} parts have a Clean-checked certificate (not replayed: a \
                 part is undecided in process)"
            ));
        }
        let receipts = self.memory_row_receipts(row, xcheck_mode, context, owned_request);
        match row.credit(&receipts) {
            MemoryCredit::Checked => BoundMemoryEvidence::Credited,
            MemoryCredit::Refuted {
                part,
                counterexample,
            } => BoundMemoryEvidence::Refuted {
                proof_name: part,
                detail: format!("memory-effect part refuted by the solver: {counterexample}"),
            },
            other => BoundMemoryEvidence::Uncredited(format!(
                "{head}; {}",
                other
                    .uncredited_clause(parts)
                    .expect("an uncredited judgement names its clause")
            )),
        }
    }

    /// FRAME RECORD: the save or restore pair of a source-bound frame,
    /// bound to the frame theorem's record
    /// ([`crate::aarch64_memory_source_binding::ContractAccess::frame_record`]).
    ///
    /// The row is credited (it keeps the frame theorem's `Formal` row) only
    /// when the frame theorem was independently replayed AND every part of
    /// the pair word's memory-effect decomposition has a Clean-checked
    /// certificate: the theorem says what the record must do, the parts that
    /// this word does exactly that. A frame theorem that did not hold keeps
    /// its own verdict; a refuted part fails the row; a part without a
    /// certificate leaves it `Unverified` with
    /// [`crate::aarch64_memory_source_binding::SOURCE_BOUND_MEMORY_NOT_CREDITED`].
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn frame_record_row(
        &self,
        owner: &crate::source_bound_frame::SourceBoundFrame<'_>,
        function: &str,
        index: usize,
        inst_id: InstId,
        frame_result: InstructionVerificationResult,
        xcheck_mode: ProvenanceXCheckMode,
        context: Option<&crate::function_request::FunctionDischargeContext<'_>>,
        owned_request: &std::cell::OnceCell<crate::FunctionVerificationRequest>,
    ) -> InstructionVerificationResult {
        use crate::aarch64_memory_source_binding::{
            SOURCE_BOUND_MEMORY_NOT_CREDITED, SourceBoundMemoryRow, trace,
        };
        let row = match SourceBoundMemoryRow::bind_frame_record(owner, inst_id) {
            Ok(row) => row,
            Err(refusal) => {
                // The owner admitted these exact operands, so this is an
                // internal inconsistency: never credit through it.
                return match frame_result {
                    InstructionVerificationResult::Verified { .. } => {
                        InstructionVerificationResult::Unverified {
                            reason: format!(
                                "{SOURCE_BOUND_MEMORY_NOT_CREDITED}: the frame record is not bound \
                                 to the frame theorem's record: {refusal}"
                            ),
                        }
                    }
                    other => other,
                };
            }
        };
        if !matches!(
            frame_result,
            InstructionVerificationResult::Verified {
                strength: VerificationStrength::Formal,
                degenerate: false,
                ..
            }
        ) {
            trace(function, index, &row, "frame theorem not credited");
            return frame_result;
        }
        match self.source_bound_memory_evidence(&row, xcheck_mode, context, owned_request) {
            BoundMemoryEvidence::Credited => {
                trace(
                    function,
                    index,
                    &row,
                    "credited (frame theorem and every part)",
                );
                frame_result
            }
            BoundMemoryEvidence::Refuted { proof_name, detail } => {
                trace(function, index, &row, "refuted");
                InstructionVerificationResult::Failed { proof_name, detail }
            }
            BoundMemoryEvidence::Uncredited(clause) => {
                trace(function, index, &row, &format!("uncredited: {clause}"));
                InstructionVerificationResult::Unverified {
                    reason: format!(
                        "{SOURCE_BOUND_MEMORY_NOT_CREDITED}: the frame theorem has a checked \
                         proof; {clause}"
                    ),
                }
            }
        }
    }

    /// LEAF ACCESS: a scalar load or store of a source-bound memory leaf,
    /// bound to the LIR access its checker matched.
    ///
    /// `lane_row` is the instruction-derived lane's row after the
    /// Formal-only bound-memory rule. A failed row stays failed. A row that
    /// rule credited keeps its credit (the source binding adds a claim, not a
    /// verdict) and still takes the memory-effect refutation check. An
    /// uncredited row is credited at `Formal`, under
    /// [`crate::aarch64_memory_source_binding::SOURCE_BOUND_MEMORY_PROOF_PREFIX`],
    /// only when every part of its word has a Clean-checked certificate;
    /// otherwise it keeps its reason and gains
    /// [`crate::aarch64_memory_source_binding::SOURCE_BOUND_MEMORY_NOT_CREDITED`].
    #[allow(clippy::too_many_arguments)]
    fn leaf_access_row(
        &self,
        leaf: &crate::source_bound_frame::SourceBoundMemoryLeaf<'_>,
        function: &str,
        index: usize,
        inst_id: InstId,
        inst: &MachInst,
        lane_row: InstructionVerificationResult,
        xcheck_mode: ProvenanceXCheckMode,
        context: Option<&crate::function_request::FunctionDischargeContext<'_>>,
        owned_request: &std::cell::OnceCell<crate::FunctionVerificationRequest>,
    ) -> InstructionVerificationResult {
        use crate::aarch64_memory_source_binding::{
            SOURCE_BOUND_MEMORY_NOT_CREDITED, SourceBoundMemoryRow, trace,
        };
        if matches!(
            lane_row,
            InstructionVerificationResult::Failed { .. }
                | InstructionVerificationResult::Skipped { .. }
        ) {
            return lane_row;
        }
        let row = match SourceBoundMemoryRow::bind_leaf_access(leaf, inst_id) {
            Ok(row) => row,
            Err(refusal) => {
                return match self.with_memory_effect(
                    inst,
                    lane_row,
                    xcheck_mode,
                    context,
                    owned_request,
                ) {
                    InstructionVerificationResult::Unverified { reason } => {
                        InstructionVerificationResult::Unverified {
                            reason: format!(
                                "{reason}; {SOURCE_BOUND_MEMORY_NOT_CREDITED}: the access is not \
                                 bound to its source access: {refusal}"
                            ),
                        }
                    }
                    other => other,
                };
            }
        };
        if matches!(lane_row, InstructionVerificationResult::Verified { .. }) {
            let checked =
                self.with_memory_effect(inst, lane_row, xcheck_mode, context, owned_request);
            let outcome = if !matches!(checked, InstructionVerificationResult::Verified { .. }) {
                "refuted".to_owned()
            } else if crate::diag::memory_effect_replay_enabled() {
                // Diagnostic only: what the source-bound route would conclude
                // for a row the Formal-only rule already credits.
                match self.source_bound_memory_evidence(&row, xcheck_mode, context, owned_request) {
                    BoundMemoryEvidence::Credited => {
                        "form-credited; every part has a Clean-checked certificate".to_owned()
                    }
                    BoundMemoryEvidence::Refuted { detail, .. } => {
                        // A refutation fails the row, credited or not.
                        trace(function, index, &row, "refuted");
                        return InstructionVerificationResult::Failed {
                            proof_name: row.label(),
                            detail,
                        };
                    }
                    BoundMemoryEvidence::Uncredited(clause) => {
                        format!("form-credited; source route: {clause}")
                    }
                }
            } else {
                "form-credited (parts not replayed)".to_owned()
            };
            trace(function, index, &row, &outcome);
            return checked;
        }
        let InstructionVerificationResult::Unverified { reason: previous } = lane_row else {
            unreachable!("failed, skipped and verified rows returned above")
        };
        match self.source_bound_memory_evidence(&row, xcheck_mode, context, owned_request) {
            BoundMemoryEvidence::Credited => {
                trace(function, index, &row, "credited (every part)");
                InstructionVerificationResult::Verified {
                    proof_name: row.proof_name(),
                    category: ProofCategory::Memory,
                    strength: VerificationStrength::Formal,
                    degenerate: false,
                }
            }
            BoundMemoryEvidence::Refuted { proof_name, detail } => {
                trace(function, index, &row, "refuted");
                InstructionVerificationResult::Failed { proof_name, detail }
            }
            BoundMemoryEvidence::Uncredited(clause) => {
                trace(function, index, &row, &format!("uncredited: {clause}"));
                InstructionVerificationResult::Unverified {
                    reason: format!("{previous}; {SOURCE_BOUND_MEMORY_NOT_CREDITED}: {clause}"),
                }
            }
        }
    }

    /// The word-bound memory-effect decomposition of an `H`/`S`/`D`/`Q`
    /// scalar load or store, or of a NEON `LD1`/`ST1` one-register
    /// post-index transfer ([`crate::aarch64_memory_effect`]), as a walk
    /// result, with the Formal-only rule's clause-2 evidence (present exactly
    /// when every part held exactly). `None` for any other instruction: the
    /// instruction-derived lane judges every general-purpose scalar form, and
    /// an `LD1`/`ST1` the form binder refuses keeps its registry refusal.
    fn try_scalar_simd_memory(
        &self,
        inst: &MachInst,
    ) -> Option<(
        InstructionVerificationResult,
        Option<crate::bound_memory_authority::BoundMemoryRefutation>,
    )> {
        use crate::aarch64_memory_effect::{InProcess, decide_in_process, memory_effect};
        let admitted =
            match crate::aarch64_scalar_memory_proofs::bind_scalar_memory_instruction(inst) {
                Ok(binding) => {
                    binding.form.bank == crate::aarch64_scalar_memory_proofs::ScalarBank::Fpr
                }
                Err(_) => {
                    crate::aarch64_neon_structure_forms::bind_neon_structure_instruction(inst)
                        .is_ok()
                }
            };
        if !admitted {
            return None;
        }
        let decomposition = memory_effect(inst)?;
        let label = format!(
            "A64 memory effect {:?} {:#010x}",
            inst.opcode, decomposition.word
        );
        for part in &decomposition.parts {
            if let InProcess::Refuted(counterexample) = decide_in_process(part, &self.config) {
                return Some((
                    InstructionVerificationResult::Failed {
                        proof_name: part.obligation.name.clone(),
                        detail: format!("memory-effect part refuted in process: {counterexample}"),
                    },
                    None,
                ));
            }
        }
        let refutation = crate::bound_memory_authority::BoundMemoryRefutation::memory_effect(
            &decomposition,
            &self.config,
        );
        let decided = if refutation.is_some() {
            format!(
                "holds in process: all {} parts exactly",
                decomposition.parts.len()
            )
        } else {
            "is not decided exactly in process".to_string()
        };
        Some((
            InstructionVerificationResult::Unverified {
                reason: format!("{MEMORY_EFFECT_IS_NOT_CREDIT}: `{label}` {decided}"),
            },
            refutation,
        ))
    }

    /// The `SUBS #imm` decoded-word obligation as a walk row
    /// ([`crate::aarch64_subs_imm_proofs`]): `Unverified` with
    /// [`crate::aarch64_subs_imm_proofs::SUBS_IMM_DECIDED_IS_NOT_CREDIT`] when
    /// the re-derived word holds (never credit), `Failed` when it is refuted
    /// or the operands are ill-formed, `Unverified` with the reason otherwise.
    /// `None` for every other opcode.
    fn try_subs_imm(inst: &MachInst) -> Option<InstructionVerificationResult> {
        use crate::aarch64_subs_imm_proofs::{
            METHOD_BITSERIAL, SUBS_IMM_DECIDED_IS_NOT_CREDIT, SubsImmCheckError, subs_imm_verdict,
        };
        let verdict = subs_imm_verdict(inst)?;
        let label = "A64 decoded SUBS #imm";
        Some(match verdict {
            Ok(word) => InstructionVerificationResult::Unverified {
                reason: format!(
                    "{SUBS_IMM_DECIDED_IS_NOT_CREDIT}: `{label}` {word:#010x} holds \
                     ({METHOD_BITSERIAL}); it binds the re-derived word to this instruction's \
                     operands, not to a source instruction, and no independently checked \
                     certificate discharges it"
                ),
            },
            Err(error @ (SubsImmCheckError::Refuted { .. } | SubsImmCheckError::IllFormed(_))) => {
                InstructionVerificationResult::Failed {
                    proof_name: label.into(),
                    detail: error.to_string(),
                }
            }
            Err(error) => InstructionVerificationResult::Unverified {
                reason: format!("{SUBS_IMM_DECIDED_IS_NOT_CREDIT}: `{label}` {error}"),
            },
        })
    }

    /// The CRC32 decoded-word obligation of a CRC32/CRC32C instruction as a
    /// walk row ([`crate::aarch64_crc32_proofs`]): `Unverified` with
    /// [`crate::aarch64_crc32_proofs::CRC32_DECIDED_IS_NOT_CREDIT`] when the
    /// re-derived word holds against the operands' intent (an in-process
    /// decision, never credit), `Failed` when it is refuted or the operands
    /// are ill-formed, `Unverified` with the reason when the shape is outside
    /// the model or the decision refused the terms. `None` for every other
    /// opcode.
    fn try_crc32(inst: &MachInst) -> Option<InstructionVerificationResult> {
        use crate::aarch64_crc32_proofs::{
            CRC32_DECIDED_IS_NOT_CREDIT, Crc32CheckError, METHOD_GF2, crc32_verdict,
        };
        let verdict = crc32_verdict(inst)?;
        let label = format!("A64 decoded CRC32 {:?}", inst.opcode);
        Some(match verdict {
            Ok(word) => InstructionVerificationResult::Unverified {
                reason: format!(
                    "{CRC32_DECIDED_IS_NOT_CREDIT}: `{label}` {word:#010x} holds ({METHOD_GF2}); \
                     it binds the re-derived word to this instruction's operands, not to a \
                     source instruction, and no independently checked certificate discharges it"
                ),
            },
            Err(error @ (Crc32CheckError::Refuted { .. } | Crc32CheckError::IllFormed(_))) => {
                InstructionVerificationResult::Failed {
                    proof_name: label,
                    detail: error.to_string(),
                }
            }
            Err(error) => InstructionVerificationResult::Unverified {
                reason: format!("{CRC32_DECIDED_IS_NOT_CREDIT}: `{label}` {error}"),
            },
        })
    }

    /// The word-bound atomic decomposition of an admitted single-instruction
    /// atomic ([`crate::aarch64_atomic_effect`]) as a walk result, with the
    /// Formal-only rule's clause-2 evidence (present exactly when every part
    /// held). `None` for every other opcode and for a refused atomic shape.
    ///
    /// Like the instruction-derived obligation, the decomposition is built
    /// over the word RE-DERIVED from `inst`'s operands; ENC-5 binds the
    /// emitted word to it (`check_emitted_atomic_word`) when the object is
    /// encoded.
    fn try_atomic_memory(
        &self,
        inst: &MachInst,
    ) -> Option<(
        InstructionVerificationResult,
        Option<crate::bound_memory_authority::BoundMemoryRefutation>,
    )> {
        use crate::aarch64_atomic_effect::{AtomicEffectVerdict, atomic_effect, judge};
        if !crate::aarch64_atomic_forms::is_atomic_memory_opcode(inst.opcode) {
            return None;
        }
        let decomposition = atomic_effect(inst)?;
        let verdict = judge(&decomposition);
        let refutation = crate::bound_memory_authority::BoundMemoryRefutation::atomic_effect(
            &decomposition,
            &verdict,
        );
        let label = format!(
            "A64 atomic effect {:?} {:#010x}",
            inst.opcode, decomposition.word
        );
        let row = match verdict {
            AtomicEffectVerdict::Holds => InstructionVerificationResult::Unverified {
                reason: format!(
                    "{ATOMIC_EFFECT_IS_NOT_CREDIT}: `{label}` held exactly in process (every \
                     field, the returned value and the memory window)"
                ),
            },
            AtomicEffectVerdict::Refuted { part, detail } => {
                InstructionVerificationResult::Failed {
                    proof_name: format!("{label}: {part}"),
                    detail,
                }
            }
            AtomicEffectVerdict::Undecided { part, detail } => {
                InstructionVerificationResult::Unverified {
                    reason: format!(
                        "{ATOMIC_EFFECT_IS_NOT_CREDIT}: `{label}: {part}` was not decided: \
                         {detail}"
                    ),
                }
            }
        };
        Some((row, refutation))
    }

    /// The instruction-derived obligation of an admitted instruction, as a
    /// walk result ([`Self::instruction_word_row`]). `None` for every other
    /// shape.
    ///
    /// The obligation decodes the word re-derived from `inst`'s operands, not
    /// the emitted word (on the certificates-on path promotion runs before the
    /// object is encoded), so a refutation here can come only from an
    /// inconsistency inside `aarch64_instruction_word_proofs`; ENC-5 binds the
    /// emitted word when the object is encoded.
    ///
    /// The second value is the Formal-only bound-memory rule's clause-2
    /// evidence: present exactly when the obligation holds, carrying the word
    /// it judged.
    fn try_instruction_word(
        &self,
        inst: &MachInst,
    ) -> Option<(
        InstructionVerificationResult,
        Option<crate::bound_memory_authority::BoundMemoryRefutation>,
    )> {
        let row = |verdict: crate::aarch64_instruction_word_proofs::InstructionWordVerdict| {
            let refutation =
                crate::bound_memory_authority::BoundMemoryRefutation::instruction_word(&verdict);
            (Self::instruction_word_row(verdict), refutation)
        };
        #[cfg(test)]
        if let Some(word) = instruction_word_seam::word() {
            return crate::aarch64_instruction_word_proofs::instruction_word_verdict_for(
                inst,
                word,
                &self.config,
            )
            .map(row);
        }
        crate::aarch64_instruction_word_proofs::instruction_word_verdict(inst, &self.config)
            .map(row)
    }

    /// An instruction-derived verdict as a walk row: `Unverified` with
    /// [`INSTRUCTION_DERIVED_IS_NOT_CREDIT`] when it holds (naming how it was
    /// decided) or is undecided, `Failed` when the word refutes it.
    fn instruction_word_row(
        verdict: crate::aarch64_instruction_word_proofs::InstructionWordVerdict,
    ) -> InstructionVerificationResult {
        use crate::aarch64_instruction_word_proofs::Outcome;
        match verdict.outcome {
            Outcome::Holds(decision) => InstructionVerificationResult::Unverified {
                reason: format!(
                    "{INSTRUCTION_DERIVED_IS_NOT_CREDIT}: `{}` holds ({decision}); it binds the \
                     re-derived word to this instruction's operands, not to a source \
                     instruction, and no independently checked certificate discharges it",
                    verdict.name
                ),
            },
            Outcome::Undecided(detail) => InstructionVerificationResult::Unverified {
                reason: format!(
                    "{INSTRUCTION_DERIVED_IS_NOT_CREDIT}: `{}` is undecided: {detail}",
                    verdict.name
                ),
            },
            Outcome::Refuted(detail) => InstructionVerificationResult::Failed {
                proof_name: verdict.name,
                detail: format!("instruction-derived obligation refuted: {detail}"),
            },
        }
    }

    /// Phase-2 reconstruction discharge for a pilot ALU instruction (#63).
    ///
    /// Returns:
    /// - `Some(Verified { degenerate: false, .. })` when the instruction is a
    ///   pilot opcode with a reconstructable operand shape AND the reconstructed
    ///   obligation discharges `Valid` with complete (`Exhaustive`) evidence. The
    ///   proof is credited (`degenerate: false`) because its provenance is
    ///   `Reconstructed` — the machine side came from the REAL emitted
    ///   instruction, so a wrong opcode/wiring would have refuted, even though a
    ///   *correct* commutative lowering reconstructs to `bvadd == bvadd`.
    /// - `Some(Unverified { .. })` when that obligation discharges only by
    ///   sampling: statistical evidence is reported, never credited.
    /// - `Some(Failed { .. })` when the reconstructed obligation REFUTES (the
    ///   isel opcode/wiring is wrong). This is the content of the mechanism.
    /// - `None` when the opcode is NOT a pilot opcode, or the instruction has no
    ///   reconstructable operand shape (e.g. an operand-less stub).
    ///
    /// The credit rule keys on [`ProofObligation::is_reconstructed`], never on a
    /// `name.contains` lookup — the reconstructed machine side is built by a
    /// typed exhaustive opcode match plus a typed positional operand schema
    /// (anti-f81e45b; asserted by `tests/reconstruction_alu.rs`).
    fn try_reconstruct_pilot(&self, inst: &MachInst) -> Option<InstructionVerificationResult> {
        // Not a pilot opcode at all -> leave on the existing path.
        opcode_to_source_op(inst.opcode)?;
        // Pilot opcode but no reconstructable operand shape -> fall through.
        let obligation = reconstruct_alu_obligation(inst)?;

        // The `canonical` obligation frees the immediate for the RI families,
        // preserving one exact theorem/query per width. It is not yet exact
        // source-lowering authority: reconstruction infers the source family
        // and fresh operands from the target instruction. Discharge therefore
        // remains Exhaustive/Statistical until a checked source-op/type/operand
        // binding token is threaded through this boundary.
        let canonical =
            canonical_reconstruct_obligation(inst).unwrap_or_else(|| obligation.clone());
        let (vresult, strength) = crate::lowering_proof::discharge_reconstructed_obligation(
            &obligation,
            &canonical,
            &self.config,
        );
        debug_assert!(
            obligation.is_reconstructed(),
            "reconstruct_alu_obligation must tag Reconstructed provenance"
        );
        Some(InstructionVerificationResult::from_discharge(
            &obligation.name,
            ProofCategory::Arithmetic,
            vresult,
            strength,
            // Credited: a reconstructed obligation is the genuine
            // (non-degenerate) credit even when structurally X==X.
            !obligation.is_reconstructed(),
        ))
    }

    /// Verify all instructions in a MachFunction.
    ///
    /// This entry point has NO replayed LIR function, so the TV-2 provenance
    /// cross-check cannot run here; the compiler cert path uses
    /// [`Self::verify_with_lir_source`] instead.
    pub fn verify(&self, func: &MachFunction) -> FunctionVerificationReport {
        self.verify_with_lir_source(func, None)
    }

    pub fn capture_request(&self) -> crate::FunctionVerificationRequest {
        self.capture_request_with_mode(provenance_xcheck::provenance_xcheck_mode(
            AARCH64_PROVENANCE_XCHECK_DEFAULT,
        ))
    }

    pub fn capture_request_with_mode(
        &self,
        mode: ProvenanceXCheckMode,
    ) -> crate::FunctionVerificationRequest {
        crate::FunctionVerificationRequest::capture(self.config.clone(), mode)
    }

    pub fn verify_with_request(
        &self,
        func: &MachFunction,
        lir_source: Option<&trust_cg_lower::Function>,
        request: &crate::FunctionVerificationRequest,
    ) -> crate::CapturedFunctionVerificationReport {
        let context = crate::function_request::FunctionDischargeContext::new(request);
        self.verify_request_in_context(func, lir_source, request, &context)
    }

    /// Retain the caller's original and adapter-input modules during checking,
    /// then bind both identities into the resulting immutable report. This is
    /// input custody; source-sensitive theorems still require their own checks.
    pub fn verify_with_request_and_modules(
        &self,
        func: &MachFunction,
        lir_source: Option<&trust_cg_lower::Function>,
        source: &crate::FunctionSourceModules<'_>,
        request: &crate::FunctionVerificationRequest,
    ) -> crate::CapturedFunctionVerificationReport {
        let context = crate::function_request::FunctionDischargeContext::new(request)
            .with_source_modules(source);
        self.verify_request_in_context(func, lir_source, request, &context)
    }

    /// Retain exact dynamic arithmetic obligations for certified export.
    /// Ordinary verifier/cache calls do not retain another obligation graph.
    pub fn verify_with_request_for_export(
        &self,
        func: &MachFunction,
        lir_source: Option<&trust_cg_lower::Function>,
        request: &crate::FunctionVerificationRequest,
    ) -> (
        crate::CapturedFunctionVerificationReport,
        Vec<crate::SourceBoundArithmeticObligation>,
    ) {
        let context = crate::function_request::FunctionDischargeContext::for_export(request);
        let report = self.verify_request_in_context(func, lir_source, request, &context);
        let exports = context.take_exports(&report);
        (report, exports)
    }

    pub fn verify_with_request_for_export_and_modules(
        &self,
        func: &MachFunction,
        lir_source: Option<&trust_cg_lower::Function>,
        source: &crate::FunctionSourceModules<'_>,
        request: &crate::FunctionVerificationRequest,
    ) -> (
        crate::CapturedFunctionVerificationReport,
        Vec<crate::SourceBoundArithmeticObligation>,
    ) {
        let context = crate::function_request::FunctionDischargeContext::for_export(request)
            .with_source_modules(source);
        let report = self.verify_request_in_context(func, lir_source, request, &context);
        let exports = context.take_exports(&report);
        (report, exports)
    }

    /// Replay a complete checked defined-peer theorem under the original
    /// capture. This returns conditional evidence only: its sealed physical
    /// entry requirement must accompany final bytes to the runtime consumer.
    /// It creates no request, policy snapshot, budget or standalone storage fact.
    pub fn verify_checked_defined_peer(
        &self,
        machine: &MachFunction,
        lir: &trust_cg_lower::Function,
        modules: &crate::FunctionSourceModules<'_>,
        request: &crate::FunctionVerificationRequest,
        peer: crate::aarch64_affine_lowering::CheckedDefinedPeerCall<'_>,
    ) -> Result<
        crate::aarch64_affine_lowering::ConditionallyReplayedDefinedPeer,
        crate::aarch64_affine_lowering::DefinedPeerCallError,
    > {
        use crate::aarch64_affine_lowering::DefinedPeerCallError;
        if !request.config_matches(&self.config)
            || !self.config.replays_source_bound_obligations()
            || request.mode() != ProvenanceXCheckMode::Enforce
            || !peer.matches_request(request)
            || !peer.matches_inputs(modules, machine, lir)
        {
            return Err(DefinedPeerCallError::Request);
        }
        let context = crate::function_request::FunctionDischargeContext::new(request)
            .with_source_modules(modules);
        peer.replay_and_seal(&context)
    }

    fn verify_request_in_context(
        &self,
        func: &MachFunction,
        lir_source: Option<&trust_cg_lower::Function>,
        request: &crate::FunctionVerificationRequest,
        context: &crate::function_request::FunctionDischargeContext<'_>,
    ) -> crate::CapturedFunctionVerificationReport {
        let report = if !request.config_matches(&self.config) {
            FunctionVerificationReport {
                function_name: func.name.clone(),
                precondition_failure: Some(
                    FunctionVerificationPreconditionFailure::VerificationRequestConfigMismatch,
                ),
                instructions: Vec::new(),
            }
        } else {
            request.with_policy(|| {
                self.verify_with_context(func, lir_source, request.mode(), Some(context))
            })
        };
        crate::CapturedFunctionVerificationReport::finish(
            report,
            crate::function_request::aarch64_input(func, lir_source),
            0,
            context,
        )
    }

    /// [`Self::verify`], plus the TV-2 lowering-provenance cross-check when
    /// the EXACT LIR function that was handed to instruction selection is
    /// supplied (see [`crate::provenance_xcheck`]).
    ///
    /// Every emitted instruction whose TV-1 sidecar entry is
    /// [`trust_cg_ir::provenance::LoweringProvenance::SourceInst`] is checked
    /// against the replayed LIR: the stamped coordinates must resolve, the
    /// recorded digest must match, and the emitted opcode's definite class
    /// (when it has one) must be a plausible constituent of the claimed
    /// source instruction's lowering. AArch64 default is WARN-ONLY (count +
    /// report, no verdict change): the aarch64 differential corpus cannot
    /// execute on the x86 validation host, so the §2.4 warn->enforce flip is
    /// deferred to the Apple-Silicon lane. Mode override:
    /// `TCG_PROVENANCE_XCHECK` (`off`/`warn`/`enforce`).
    pub fn verify_with_lir_source(
        &self,
        func: &MachFunction,
        lir_source: Option<&trust_cg_lower::Function>,
    ) -> FunctionVerificationReport {
        self.verify_with_lir_source_and_mode(
            func,
            lir_source,
            provenance_xcheck::provenance_xcheck_mode(AARCH64_PROVENANCE_XCHECK_DEFAULT),
        )
    }

    /// Mode-explicit body of [`Self::verify_with_lir_source`].
    ///
    /// Proof-authoritative compiler boundaries must pass
    /// [`ProvenanceXCheckMode::Enforce`] directly: consulting the ordinary
    /// AArch64 rollout default (or a process environment override) at such a
    /// boundary would let warn/off behavior leak into a proof-grade artifact.
    /// Enforce also requires a present, name-matched LIR source; a missing or
    /// mis-paired source fails before any instruction can earn proof credit.
    /// This pairing check does not establish exact operand correspondence.
    /// Tests also inject the mode directly to remain independent of ambient
    /// process state.
    pub fn verify_with_lir_source_and_mode(
        &self,
        func: &MachFunction,
        lir_source: Option<&trust_cg_lower::Function>,
        xcheck_mode: ProvenanceXCheckMode,
    ) -> FunctionVerificationReport {
        self.verify_with_context(func, lir_source, xcheck_mode, None)
    }

    fn verify_with_context(
        &self,
        func: &MachFunction,
        lir_source: Option<&trust_cg_lower::Function>,
        xcheck_mode: ProvenanceXCheckMode,
        context: Option<&crate::function_request::FunctionDischargeContext<'_>>,
    ) -> FunctionVerificationReport {
        // TV-2: Enforce must not silently degrade to the source-less verifier
        // when the caller omitted or mis-zipped the exact LIR function. Warn
        // and Off retain their diagnostic behavior, but cannot supply the
        // authority of an enforced source check.
        let source_pairing_failure = if xcheck_mode == ProvenanceXCheckMode::Enforce {
            match lir_source {
                None => Some(FunctionVerificationPreconditionFailure::MissingLirSource),
                Some(lir) if lir.name != func.name => Some(
                    FunctionVerificationPreconditionFailure::LirSourceNameMismatch {
                        source_function: lir.name.clone(),
                    },
                ),
                Some(_) => None,
            }
        } else {
            None
        };
        // A missing instruction is malformed input, not an empty proof subject.
        // Check every reference before any reconstruction or discharge so no
        // partial report can silently omit it in any provenance mode.
        let precondition_failure = source_pairing_failure.or_else(|| {
            func.blocks.iter().enumerate().find_map(|(block, body)| {
                body.insts.iter().find_map(|instruction| {
                    ((instruction.0 as usize) >= func.insts.len()).then_some(
                        FunctionVerificationPreconditionFailure::InvalidInstructionReference {
                            block,
                            instruction: instruction.0,
                        },
                    )
                })
            })
        });
        if let Some(failure) = precondition_failure {
            return FunctionVerificationReport {
                function_name: func.name.clone(),
                precondition_failure: Some(failure),
                instructions: Vec::new(),
            };
        }
        // Classify the complete source/body pair before any instruction can
        // earn credit. Only the exact, name-matched source decides whether the
        // binder applies. A recognized supported shape whose machine body
        // disagrees with that source is an erroneous target: enforced source
        // checking rejects the function by name instead of reporting the
        // envelope as uncovered, and warn mode emits a named diagnostic.
        let bound_frame = match lir_source {
            Some(source)
                if xcheck_mode != ProvenanceXCheckMode::Off && source.name == func.name =>
            {
                match crate::source_bound_frame::source_bound_frame(source, func) {
                    Ok(frame) => Some(frame),
                    Err(crate::source_bound_frame::SourceBoundFrameRefusal::Mismatch(mismatch)) => {
                        if xcheck_mode == ProvenanceXCheckMode::Enforce {
                            return FunctionVerificationReport {
                                function_name: func.name.clone(),
                                precondition_failure: Some(
                                    FunctionVerificationPreconditionFailure::SourceBoundFrameMismatch(
                                        mismatch,
                                    ),
                                ),
                                instructions: Vec::new(),
                            };
                        }
                        eprintln!(
                            "[TCG-SOURCE-BOUND-FRAME-MISMATCH-WARN] arch=aarch64 fn={} \
                             erroneous supported target (not rejected in warn mode): {mismatch}",
                            func.name
                        );
                        None
                    }
                    Err(crate::source_bound_frame::SourceBoundFrameRefusal::Unsupported(_)) => None,
                }
            }
            _ => None,
        };
        // The AArch64 whole-body owner judges what the frame owner does not
        // bind: a frameless body of Boolean, bitwise, shift, select and
        // acyclic control-flow semantics (`source_bound_a64_body`). Again only
        // the exact, name-matched source decides applicability, and a
        // recognized body that disagrees with it is rejected under Enforce.
        let bound_body = match lir_source {
            Some(source)
                if bound_frame.is_none()
                    && xcheck_mode != ProvenanceXCheckMode::Off
                    && source.name == func.name =>
            {
                let trace = crate::diag::a64_body_trace_enabled();
                match crate::source_bound_a64_body::source_bound_a64_body(source, func) {
                    Ok(owner) => Some(owner),
                    Err(crate::source_bound_a64_body::A64BodyRefusal::Mismatch(mismatch)) => {
                        if trace {
                            eprintln!("[TCG-A64-BODY-TRACE] fn={} mismatch: {mismatch}", func.name);
                        }
                        if xcheck_mode == ProvenanceXCheckMode::Enforce {
                            return FunctionVerificationReport {
                                function_name: func.name.clone(),
                                precondition_failure: Some(
                                    FunctionVerificationPreconditionFailure::SourceBoundA64BodyMismatch(
                                        mismatch,
                                    ),
                                ),
                                instructions: Vec::new(),
                            };
                        }
                        eprintln!(
                            "[TCG-SOURCE-BOUND-A64-BODY-MISMATCH-WARN] arch=aarch64 fn={} \
                             erroneous supported target (not rejected in warn mode): {mismatch}",
                            func.name
                        );
                        None
                    }
                    Err(refusal @ crate::source_bound_a64_body::A64BodyRefusal::Unsupported(_)) => {
                        if trace {
                            eprintln!("[TCG-A64-BODY-TRACE] fn={} {refusal}", func.name);
                        }
                        None
                    }
                }
            }
            _ => None,
        };
        // A frame-free linear source/return check is a trusted Rust routing
        // witness, never instruction proof credit. It also checks identities
        // with no value instruction, before RET's structural coverage is used.
        let bound_frameless = match lir_source {
            Some(source)
                if bound_frame.is_none()
                    && bound_body.is_none()
                    && xcheck_mode != ProvenanceXCheckMode::Off
                    && source.name == func.name =>
            {
                match crate::source_bound_a64_control::CheckedFramelessLinear::bind(source, func) {
                    Ok(body) => Some(body),
                    Err(crate::source_bound_frame::SourceBoundFrameRefusal::Mismatch(mismatch)) => {
                        if xcheck_mode == ProvenanceXCheckMode::Enforce {
                            return FunctionVerificationReport {
                                function_name: func.name.clone(),
                                precondition_failure: Some(FunctionVerificationPreconditionFailure::SourceBoundFramelessMismatch(mismatch)),
                                instructions: Vec::new(),
                            };
                        }
                        eprintln!(
                            "[TCG-SOURCE-BOUND-FRAMELESS-MISMATCH-WARN] arch=aarch64 fn={} erroneous supported target: {mismatch}",
                            func.name
                        );
                        None
                    }
                    Err(crate::source_bound_frame::SourceBoundFrameRefusal::Unsupported(_)) => None,
                }
            }
            _ => None,
        };
        let t_index = walk_timing_enabled().then(std::time::Instant::now);
        let lir_index: Option<LirSourceIndex> = match xcheck_mode {
            ProvenanceXCheckMode::Off => None,
            _ => lir_source.and_then(|lir| {
                if lir.name == func.name {
                    Some(LirSourceIndex::build(lir))
                } else if xcheck_mode == ProvenanceXCheckMode::Warn {
                    eprintln!(
                        "[TCG-PROVENANCE-XCHECK-WARN] arch=aarch64 fn={} replayed LIR function \
                         name mismatch (got `{}`): provenance cross-check skipped",
                        func.name, lir.name
                    );
                    None
                } else {
                    None
                }
            }),
        };
        if let Some(t) = t_index {
            eprintln!(
                "TCG_TIME_WALK fn={} lir_index_build={:.2}ms",
                func.name,
                t.elapsed().as_secs_f64() * 1000.0
            );
        }
        let mut attributed_count: usize = 0;
        let mut synthetic_count: usize = 0;
        let mut mismatch_count: usize = 0;

        let mut instructions = Vec::new();

        // Bind the complete source/body before replaying the exact frame theorem.
        // Neither an opcode match nor statistical evaluation can credit this
        // envelope. The input receipt also binds all source and machine bytes.
        let frame = if xcheck_mode == ProvenanceXCheckMode::Enforce
            && self.config.replays_source_bound_obligations()
        {
            bound_frame.map(|frame| {
                let result = match context {
                    Some(context) => context.frame(&frame),
                    None => {
                        let request = self.capture_request_with_mode(xcheck_mode);
                        crate::function_request::FunctionDischargeContext::new(&request)
                            .frame(&frame)
                    }
                };
                let result = match result {
                    Some(VerificationResult::Valid) => InstructionVerificationResult::Verified {
                        proof_name: frame.obligation().name.clone(),
                        category: ProofCategory::FrameLayout,
                        strength: VerificationStrength::Formal,
                        degenerate: frame.obligation().is_degenerate(),
                    },
                    Some(VerificationResult::Invalid { counterexample }) => {
                        InstructionVerificationResult::Failed {
                            proof_name: frame.obligation().name.clone(),
                            detail: counterexample,
                        }
                    }
                    Some(VerificationResult::Unknown { reason }) => {
                        InstructionVerificationResult::Failed {
                            proof_name: frame.obligation().name.clone(),
                            detail: format!("Unknown: {reason}"),
                        }
                    }
                    None => InstructionVerificationResult::Unverified {
                        reason: "source-bound frame needs independently replayed proof".into(),
                    },
                };
                (frame.envelope_instructions(), result, frame)
            })
        } else {
            None
        };

        // A frameless leaf whose loads and stores the memory-leaf checker binds,
        // access by access, to its LIR source
        // (`source_bound_frame::source_bound_memory_leaf`). Only the replaying
        // policy consults it: its rows are credited through that replay alone
        // (`aarch64_memory_source_binding`). A refusal binds nothing and never
        // rejects the function.
        let memory_leaf = if frame.is_none()
            && xcheck_mode == ProvenanceXCheckMode::Enforce
            && self.config.replays_source_bound_obligations()
        {
            lir_source
                .filter(|source| source.name == func.name)
                .and_then(|source| {
                    crate::source_bound_frame::source_bound_memory_leaf(source, func)
                        .inspect_err(|refusal| {
                            crate::aarch64_memory_source_binding::trace_unbound(func, refusal)
                        })
                        .ok()
                })
        } else {
            None
        };

        let constant_bindings = frame.as_ref().and_then(|(_, result, owner)| {
            matches!(
                result,
                InstructionVerificationResult::Verified {
                    strength: VerificationStrength::Formal,
                    degenerate: false,
                    ..
                }
            )
            .then(|| crate::source_bound_constant::SourceBoundConstants::new(owner))
        });

        // Replay one raw body theorem per immutable frame, then reuse it only
        // for copies/comparisons in the actual return's backward slice. The Rust affine
        // match alone cannot grant these rows Formal strength.
        let body = frame.as_ref().and_then(|(_, result, owner)| {
            if !matches!(
                result,
                InstructionVerificationResult::Verified {
                    strength: VerificationStrength::Formal,
                    degenerate: false,
                    ..
                }
            ) {
                return None;
            }
            let body = crate::source_bound_body::SourceBoundBody::bind(owner)?;
            let result = match context {
                Some(context) => context.a64_body(&body),
                None => {
                    let request = self.capture_request_with_mode(xcheck_mode);
                    crate::function_request::FunctionDischargeContext::new(&request).a64_body(&body)
                }
            };
            let result = match result {
                Some(VerificationResult::Valid) => InstructionVerificationResult::Verified {
                    proof_name: body.obligation().name.clone(),
                    category: body.category(),
                    strength: VerificationStrength::Formal,
                    degenerate: body.obligation().is_degenerate(),
                },
                Some(VerificationResult::Invalid { counterexample }) => {
                    InstructionVerificationResult::Failed {
                        proof_name: body.obligation().name.clone(),
                        detail: counterexample,
                    }
                }
                Some(VerificationResult::Unknown { reason }) => {
                    InstructionVerificationResult::Failed {
                        proof_name: body.obligation().name.clone(),
                        detail: format!("Unknown: {reason}"),
                    }
                }
                None => InstructionVerificationResult::Unverified {
                    reason: "source-bound raw body needs independently replayed proof".into(),
                },
            };
            Some((body, result))
        });

        // Only a separately replayed next-PC theorem credits a branch.
        // Framed control still borrows an independently replayed frame;
        // frameless control borrows the complete checked source/return body.
        // Neither path grants identity/copy value credit.
        let control_owner = frame
            .as_ref()
            .and_then(|(_, result, frame)| {
                matches!(
                    result,
                    InstructionVerificationResult::Verified {
                        strength: VerificationStrength::Formal,
                        degenerate: false,
                        ..
                    }
                )
                .then(|| crate::source_bound_a64_control::SourceBoundA64Control::bind(frame))
                .flatten()
            })
            .or_else(|| {
                if frame.is_none()
                    && xcheck_mode == ProvenanceXCheckMode::Enforce
                    && self.config.replays_source_bound_obligations()
                {
                    bound_frameless.as_ref().and_then(
                        crate::source_bound_a64_control::SourceBoundA64Control::bind_frameless,
                    )
                } else {
                    None
                }
            });
        let control = control_owner.map(|owner| {
            let verdict = match context {
                Some(context) => context.a64_control(&owner),
                None => {
                    let request = self.capture_request_with_mode(xcheck_mode);
                    crate::function_request::FunctionDischargeContext::new(&request)
                        .a64_control(&owner)
                }
            };
            let result = match verdict {
                Some(VerificationResult::Valid) => InstructionVerificationResult::Verified {
                    proof_name: owner.obligation().name.clone(),
                    category: ProofCategory::Branch,
                    strength: VerificationStrength::Formal,
                    degenerate: owner.obligation().is_degenerate(),
                },
                Some(VerificationResult::Invalid { counterexample }) => {
                    InstructionVerificationResult::Failed {
                        proof_name: owner.obligation().name.clone(),
                        detail: counterexample,
                    }
                }
                Some(VerificationResult::Unknown { reason }) => {
                    InstructionVerificationResult::Failed {
                        proof_name: owner.obligation().name.clone(),
                        detail: format!("Unknown: {reason}"),
                    }
                }
                None => InstructionVerificationResult::Unverified {
                    reason: owner.replay_reason().into(),
                },
            };
            (owner, result)
        });

        // Replay the frameless whole-body theorem once, before any of its rows
        // is walked (it is bound only where no frame is, so never beside the
        // raw body theorem above). Only a replayed certificate credits; every
        // other outcome leaves the covered rows to the verdict
        // `a64_body_row_result` gives.
        let whole_body = if xcheck_mode == ProvenanceXCheckMode::Enforce
            && self.config.replays_source_bound_obligations()
        {
            bound_body.map(|owner| {
                let (verdict, why) = match context {
                    Some(context) => context.a64_whole_body(&owner),
                    None => {
                        let request = self.capture_request_with_mode(xcheck_mode);
                        crate::function_request::FunctionDischargeContext::new(&request)
                            .a64_whole_body(&owner)
                    }
                };
                if crate::diag::a64_body_trace_enabled() {
                    let outcome = match &verdict {
                        Some(VerificationResult::Valid) => "Valid".to_owned(),
                        Some(VerificationResult::Invalid { .. }) => "Invalid (refuted)".to_owned(),
                        Some(VerificationResult::Unknown { reason }) => {
                            format!("Unknown ({reason})")
                        }
                        None => format!(
                            "none (no independently checked proof{})",
                            why.as_deref()
                                .map(|why| format!(": {why}"))
                                .unwrap_or_default()
                        ),
                    };
                    eprintln!(
                        "[TCG-A64-BODY-TRACE] fn={} covered={} copies_and_constants={} replay={outcome}",
                        func.name,
                        owner.covered().len(),
                        owner.copies_and_constants().len()
                    );
                }
                (owner, verdict, why)
            })
        } else {
            None
        };

        // The AArch64 scalar-cell caller (`source_bound_frame::cell_caller`):
        // a non-leaf Linux caller passing one escaped scalar stack cell to a
        // direct C call, bound to its ORIGINAL TrustIR module and LIR by one
        // whole-call theorem under the AAPCS64 callee contract (ruling
        // LD-89). Only where no other
        // AArch64 owner binds the function, only under the replaying policy
        // and only with the original module in hand. Every refusal binds
        // nothing and never rejects the function; only a replayed certificate
        // of the exact theorem credits its rows.
        let scalar_cell = if frame.is_none()
            && whole_body.is_none()
            && memory_leaf.is_none()
            && xcheck_mode == ProvenanceXCheckMode::Enforce
            && self.config.replays_source_bound_obligations()
        {
            match (
                lir_source.filter(|source| source.name == func.name),
                context,
                context.and_then(|context| context.source_modules),
            ) {
                (Some(source), Some(context), Some(modules)) => {
                    match crate::source_bound_frame::source_bound_scalar_cell_caller(
                        modules.original(),
                        source,
                        func,
                    ) {
                        Ok(owner) => {
                            let (verdict, why) = context.scalar_cell_caller(&owner);
                            if crate::diag::solve_trace_enabled() {
                                use sha2::Digest;
                                let query = crate::ay_bridge::generate_smt2_query_raw(
                                    owner.obligation(),
                                    &crate::verdict_db::live_source_bound_config(),
                                );
                                let outcome = match &verdict {
                                    Some(VerificationResult::Valid) => "Valid".to_owned(),
                                    Some(VerificationResult::Invalid { .. }) => {
                                        "Invalid".to_owned()
                                    }
                                    Some(VerificationResult::Unknown { reason }) => {
                                        format!("Unknown({reason})")
                                    }
                                    None => format!("none({})", why.as_deref().unwrap_or("")),
                                };
                                // `statement_sha256` names the stated theorem;
                                // each part's own query is what AY and Clean
                                // ran (`TCG_SOLVE_TRACE promotion_result`).
                                eprintln!(
                                    "[TCG-SCALAR-CELL-CALLER] v1\tbound\tfunction={}\tcovered={}\
                                     \tparts={}\treplay={outcome}\tstatement_sha256={:x}\
                                     \tstatement_bytes={}",
                                    func.name,
                                    owner.covered().len(),
                                    owner.parts().len(),
                                    sha2::Sha256::digest(query.as_bytes()),
                                    query.len(),
                                );
                                for (k, part) in owner.parts().iter().enumerate() {
                                    let query = crate::ay_bridge::generate_smt2_query_raw(
                                        part,
                                        &crate::verdict_db::live_source_bound_config(),
                                    );
                                    eprintln!(
                                        "[TCG-SCALAR-CELL-CALLER] v1\tpart\tfunction={}\tpart={}/{}\
                                         \tquery_sha256={:x}\tquery_bytes={}",
                                        func.name,
                                        k + 1,
                                        owner.parts().len(),
                                        sha2::Sha256::digest(query.as_bytes()),
                                        query.len(),
                                    );
                                }
                            }
                            Some((owner, verdict, why))
                        }
                        Err(refusal) => {
                            if crate::diag::solve_trace_enabled() {
                                let detail = match &refusal {
                                    crate::source_bound_frame::ScalarCellCallerRefusal::Admission(
                                        crate::source_bound_frame::ScalarCellFrameError::Layout,
                                    ) => format!(
                                        "\tdetail={}",
                                        crate::source_bound_frame::scalar_cell_admission_layout_diagnosis(
                                            source, func
                                        )
                                    ),
                                    _ => String::new(),
                                };
                                eprintln!(
                                    "[TCG-SCALAR-CELL-CALLER] v1\tunbound\tfunction={}\treason={refusal}{detail}",
                                    func.name
                                );
                            }
                            None
                        }
                    }
                }
                _ => None,
            }
        } else {
            None
        };

        // The request the memory-effect arm replays under when the caller
        // supplied no discharge context: captured once per walk, on first use.
        let owned_request: std::cell::OnceCell<crate::FunctionVerificationRequest> =
            std::cell::OnceCell::new();

        // L04-P12: the trap-guard layer over the trap-expansion verdict
        // (`aarch64_trap_guard`): recorded windows bound to their stamped
        // source and shown to execute, unconditional BRKs admitted only in an
        // exactly bound role, everything else refused by name. Its decisions
        // are merged into the rows below (`aarch64_trap_guard::combine`).
        let trap_analysis =
            crate::aarch64_trap_guard::analyze(func, lir_index.as_ref(), &self.config);

        // Walk all blocks and their instructions.
        // `TCG_TIME_WALK=1`: attribute this walk's time to its arms.
        let walk_timing = walk_timing_enabled();
        let mut walk_split = [std::time::Duration::ZERO; 5]; // skip, recon, query, xcheck, push
        let mut walk_arm_counts = [0u32; 5];
        // L04-P12: the BRK closing each recorded trap expansion.
        let trap_closing: std::collections::HashMap<InstId, usize> = func
            .trap_expansions
            .iter()
            .enumerate()
            .filter_map(|(index, record)| record.insts.last().map(|&last| (last, index)))
            .collect();
        let trap_route = TrapReplayRoute {
            xcheck_mode,
            context,
            owned_request: &owned_request,
            answers: std::cell::RefCell::new(std::collections::HashMap::new()),
        };
        for (block_index, block) in func.blocks.iter().enumerate() {
            for (block_pos, &inst_id) in block.insts.iter().enumerate() {
                let idx = inst_id.0 as usize;
                let inst = &func.insts[idx];
                let t_arm = walk_timing.then(std::time::Instant::now);
                let mut arm = 0usize;

                // A row the whole-body theorem covers: semantic correspondence
                // (including if-conversion and fused compare-branches) is the
                // theorem's, so TV-2 keeps only its coordinate/digest checks.
                let body_row = whole_body
                    .as_ref()
                    .is_some_and(|(owner, _, _)| owner.covers(inst_id));
                let source_bound_alu = frame.as_ref().and_then(|(_, result, owner)| {
                    matches!(
                        result,
                        InstructionVerificationResult::Verified {
                            strength: VerificationStrength::Formal,
                            degenerate: false,
                            ..
                        }
                    )
                    .then(|| crate::source_bound_alu::SourceBoundAlu::bind(owner, inst_id))
                    .flatten()
                });

                let source_bound_constant = constant_bindings
                    .as_ref()
                    .and_then(|bindings| bindings.bind(inst_id));

                // The trap-guard layer's decision for this row, if any. A row
                // it refuses, fails or cannot bind can never be credited, so
                // its trap-expansion verdict is not replayed.
                let trap_guard_row = trap_analysis.row_for(inst_id);
                let result = if let Some(result) = self.trap_row_result(
                    func,
                    (trust_cg_ir::BlockId(block_index as u32), block_pos),
                    inst_id,
                    inst,
                    &trap_closing,
                    &trap_route,
                    trap_guard_row.is_none(),
                ) {
                    result
                } else if inst.opcode.is_pseudo() {
                    InstructionVerificationResult::Skipped {
                        reason: format!("{:?} is a pseudo-instruction", inst.opcode),
                    }
                } else if let Some(reason) = register_alu_extra_operand_refusal_reason(inst) {
                    InstructionVerificationResult::Unverified { reason }
                } else if let Some((_, result, owner)) = frame
                    .as_ref()
                    .filter(|(envelope, _, _)| envelope.contains(&inst_id))
                {
                    if owner.pair_instructions().contains(&inst_id) {
                        // FRAME RECORD (L07-P2): the save/restore pair is
                        // credited by the frame theorem AND every part of its
                        // word's memory-effect decomposition, bound to the
                        // theorem's record (`aarch64_memory_source_binding`).
                        self.frame_record_row(
                            owner,
                            &func.name,
                            idx,
                            inst_id,
                            result.clone(),
                            xcheck_mode,
                            context,
                            &owned_request,
                        )
                    } else {
                        result.clone()
                    }
                } else if let Some((_, result)) = control
                    .as_ref()
                    .filter(|(control, _)| control.credits(inst_id))
                {
                    result.clone()
                } else if let Some((_, result)) =
                    body.as_ref().filter(|(body, _)| body.credits(inst_id))
                {
                    result.clone()
                } else if let Some(constant) = source_bound_constant.as_ref() {
                    let result = match context {
                        Some(context) => context.constant(constant),
                        None => {
                            let request = self.capture_request_with_mode(xcheck_mode);
                            crate::function_request::FunctionDischargeContext::new(&request)
                                .constant(constant)
                        }
                    };
                    match result {
                        Some(VerificationResult::Valid) => {
                            InstructionVerificationResult::Verified {
                                proof_name: constant.obligation().name.clone(),
                                category: ProofCategory::Arithmetic,
                                strength: VerificationStrength::Formal,
                                degenerate: constant.obligation().is_degenerate(),
                            }
                        }
                        Some(VerificationResult::Invalid { counterexample }) => {
                            InstructionVerificationResult::Failed {
                                proof_name: constant.obligation().name.clone(),
                                detail: counterexample,
                            }
                        }
                        Some(VerificationResult::Unknown { reason }) => {
                            InstructionVerificationResult::Failed {
                                proof_name: constant.obligation().name.clone(),
                                detail: format!("Unknown: {reason}"),
                            }
                        }
                        None => InstructionVerificationResult::Unverified {
                            reason: "source-bound constant needs independently replayed proof"
                                .into(),
                        },
                    }
                } else if let Some((owner, verdict, why)) = whole_body
                    .as_ref()
                    .filter(|(owner, _, _)| owner.covers(inst_id))
                {
                    crate::source_bound_a64_body::a64_body_row_result(
                        owner.obligation(),
                        inst.opcode,
                        verdict.as_ref(),
                        why.as_deref(),
                    )
                } else if let Some((owner, verdict, why, role)) =
                    scalar_cell.as_ref().and_then(|(owner, verdict, why)| {
                        owner.role(inst_id).map(|role| (owner, verdict, why, role))
                    })
                {
                    // A row the scalar-cell caller's whole-call theorem binds
                    // and genuinely uses (its role names what it does). TV-2
                    // below keeps every check, the op-class plausibility
                    // check included.
                    crate::source_bound_frame::scalar_cell_row_result(
                        owner.obligation(),
                        role,
                        verdict.as_ref(),
                        why.as_deref(),
                    )
                } else if let Some(alu) = source_bound_alu.as_ref() {
                    let result = match context {
                        Some(context) => context.alu(alu),
                        None => {
                            let request = self.capture_request_with_mode(xcheck_mode);
                            crate::function_request::FunctionDischargeContext::new(&request)
                                .alu(alu)
                        }
                    };
                    match result {
                        Some(VerificationResult::Valid) => {
                            InstructionVerificationResult::Verified {
                                proof_name: alu.obligation().name.clone(),
                                category: ProofCategory::Arithmetic,
                                strength: VerificationStrength::Formal,
                                degenerate: alu.obligation().is_degenerate(),
                            }
                        }
                        Some(VerificationResult::Invalid { counterexample }) => {
                            InstructionVerificationResult::Failed {
                                proof_name: alu.obligation().name.clone(),
                                detail: counterexample,
                            }
                        }
                        Some(VerificationResult::Unknown { reason }) => {
                            InstructionVerificationResult::Failed {
                                proof_name: alu.obligation().name.clone(),
                                detail: format!("Unknown: {reason}"),
                            }
                        }
                        None => InstructionVerificationResult::Unverified {
                            reason: "source-bound arithmetic needs independently replayed proof"
                                .into(),
                        },
                    }
                } else if let Some(recon_result) = {
                    arm = 1;
                    self.try_reconstruct_pilot(inst)
                } {
                    // PHASE-2 OPERAND RECONSTRUCTION (PILOT, task #63).
                    //
                    // Pilot ALU opcodes (Add/Sub/Mul/Neg) with a real operand
                    // shape are routed through reconstruction. The machine side is
                    // rebuilt from the REAL emitted opcode+operands, so a wrong
                    // isel choice (e.g. SUB for Iadd) or wrong operand wiring on a
                    // non-commutative op (SUB) REFUTES. The proof is credited
                    // Verified IFF `is_reconstructed() && Valid` with complete
                    // evidence; a sampled discharge stays Unverified.
                    //
                    // `try_reconstruct_pilot` returns `None` only when the opcode
                    // is not a pilot opcode OR the instruction does not carry a
                    // reconstructable operand shape (e.g. an operand-less test
                    // stub). Such an instruction has no instruction-built
                    // obligation and cannot be credited below.
                    recon_result
                } else if let Some(pair_result) = {
                    arm = 1;
                    self.try_pair_memory(inst, context.map(|context| context.request))
                } {
                    // PAIR MEMORY RECONSTRUCTION. Admitted `STP`/`LDP` shapes
                    // discharge an operand-bound obligation over both
                    // transfers and the base writeback: a refutation fails the
                    // row, and a sampled `Valid` is reported, not credited.
                    // Credit is Formal-only (`apply_bound_memory_rule`): a
                    // replayed certificate of the row's pair form theorem. An
                    // unadmitted shape returns `None` here and keeps falling
                    // through to the terminal "no proof mapping for opcode"
                    // arm. WORD-BOUND MEMORY EFFECT (L07-P2, X-OPCODES-P1,
                    // L04-P7): the decomposition of the pair's word then
                    // refutes or annotates the row, never credits it
                    // (`with_memory_effect`).
                    self.with_memory_effect(inst, pair_result, xcheck_mode, context, &owned_request)
                } else if let Some(word_result) = {
                    arm = 1;
                    self.try_instruction_word(inst).map(|(row, refutation)| {
                        let row = apply_bound_memory_rule(
                            inst,
                            row,
                            refutation,
                            &self.config,
                            context.map(|context| context.request),
                        );
                        // A scalar immediate load/store: its memory-effect
                        // decomposition refutes or annotates, never credits,
                        // unless a source-bound memory leaf bound the access
                        // to its LIR source (`leaf_access_row`).
                        match memory_leaf.as_ref() {
                            Some(leaf) if leaf.access(inst_id).is_some() => self.leaf_access_row(
                                leaf,
                                &func.name,
                                idx,
                                inst_id,
                                inst,
                                row,
                                xcheck_mode,
                                context,
                                &owned_request,
                            ),
                            _ => self.with_memory_effect(
                                inst,
                                row,
                                xcheck_mode,
                                context,
                                &owned_request,
                            ),
                        }
                    })
                } {
                    // INSTRUCTION-DERIVED OBLIGATION (L07-P2). An admitted
                    // move-wide, register copy, add/sub immediate, compare,
                    // shifted-register add/sub/eor, UMULH, direct branch or
                    // general-purpose scalar load/store (immediate,
                    // sign-extending, writeback or register offset) is judged
                    // by the obligation
                    // built from its own re-derived word
                    // (`aarch64_instruction_word_proofs`), never by a registry
                    // theorem found by name. It is never credit: a holding
                    // obligation is reported unverified, a refutation fails
                    // the row. Other shapes fall through to the registry
                    // refusal below.
                    word_result
                } else if let Some(atomic_result) = {
                    arm = 1;
                    self.try_atomic_memory(inst).map(|(row, refutation)| {
                        apply_bound_memory_rule(
                            inst,
                            row,
                            refutation,
                            &self.config,
                            context.map(|context| context.request),
                        )
                    })
                } {
                    // SINGLE-INSTRUCTION ATOMIC (X-OPCODES-P2). An admitted
                    // LDAR/STLR/CAS/SWP/LD<op> is judged by the word-bound
                    // decomposition of its re-derived word
                    // (`aarch64_atomic_effect`), decided exactly in process: a
                    // refutation fails the row, a hold is never credit by
                    // itself. Credit is the Formal-only rule's: a replayed
                    // certificate of the row's atomic form theorem
                    // (`aarch64_atomic_forms`, `verdict_db/atomic_memory_certs/`).
                    // A refused shape returns `None` and keeps falling through
                    // to the registry refusal below.
                    atomic_result
                } else if let Some(simd_result) = {
                    arm = 1;
                    self.try_scalar_simd_memory(inst).map(|(row, refutation)| {
                        apply_bound_memory_rule(
                            inst,
                            row,
                            refutation,
                            &self.config,
                            context.map(|context| context.request),
                        )
                    })
                } {
                    // H/S/D/Q SCALAR LOAD/STORE and NEON LD1/ST1 POST-INDEX
                    // (L04-P1). The instruction-derived lane models no
                    // SIMD&FP register, so these rows are judged by the
                    // word-bound memory-effect decomposition of their
                    // re-derived word, every part decided exactly in process:
                    // a refutation fails the row, a hold is the Formal-only
                    // rule's clause-2 evidence and never credit by itself;
                    // credit is a replayed certificate of the row's form
                    // theorem (`aarch64_scalar_memory_proofs`,
                    // `aarch64_neon_structure_forms`).
                    simd_result
                } else if let Some(subs_result) = {
                    arm = 1;
                    Self::try_subs_imm(inst)
                } {
                    // SUBS #imm (L04-P1). The re-derived word's destination
                    // value and N, Z, C, V are each decided against the
                    // operands' difference and comparison for every register
                    // value (`aarch64_subs_imm_proofs`, bit-serial, in
                    // process): a refutation fails the row, a hold is never
                    // credit.
                    subs_result
                } else if let Some(crc_result) = {
                    arm = 1;
                    Self::try_crc32(inst)
                } {
                    // CRC32/CRC32C (L04-P1). The re-derived word's Arm ARM
                    // pseudocode is decided against the reflected-CRC intent
                    // of the operands for every register value
                    // (`aarch64_crc32_proofs`, GF(2)-affine, in process): a
                    // refutation fails the row, a hold is never credit.
                    crc_result
                } else if let Some((query, category)) = {
                    arm = 2;
                    // The TV-1 stamped SOURCE instruction, which only the walk
                    // has: none in `ProvenanceXCheckMode::Off`, without a
                    // `lir_source`, or for an unstamped instruction. The
                    // NZCV-consumer slot of the in-block chain reads it to
                    // bind a CSET/CSEL citation to its source
                    // (`nzcv_consumer_query`); with no source that slot keeps
                    // the machine-level reaching-producer binding.
                    let source = lir_index.as_ref().and_then(|index| {
                        match func.inst_lowering_provenance(inst_id) {
                            trust_cg_ir::LoweringProvenance::SourceInst { id, .. } => index.get(id),
                            _ => None,
                        }
                    });
                    Self::inst_to_proof_query_in_block_for_source(
                        func,
                        &block.insts,
                        block_pos,
                        inst,
                        source,
                    )
                    .or_else(|| {
                        let (_, result, owner) = frame.as_ref()?;
                        matches!(
                            result,
                            InstructionVerificationResult::Verified {
                                strength: VerificationStrength::Formal,
                                degenerate: false,
                                ..
                            }
                        )
                        .then(|| Self::source_bound_cset_query(owner, inst_id))
                        .flatten()
                    })
                } {
                    // SUBSTRING / REPRESENTATIVE CREDIT IS WITHDRAWN. The query
                    // mapping still runs so the refusal names what the instruction
                    // reached, but the registry theorem it would select is about
                    // its own representative form (e.g. `"load"` resolves to an
                    // I32 pair or byte-roundtrip theorem), never this
                    // instruction's operands. Nothing is discharged: no sweep, no
                    // tier-0 or portable replay, no live solver.
                    let (query, category) =
                        self.refine_citation(func, &block.insts, block_pos, inst, query, category);
                    // No refutation check runs on this arm: a bound row here
                    // is never credited (rule clause 2).
                    let row = apply_bound_memory_rule(
                        inst,
                        InstructionVerificationResult::withdrawn_registry_credit(query, category),
                        None,
                        &self.config,
                        context.map(|context| context.request),
                    );
                    // WORD-BOUND MEMORY EFFECT of a NEON LD1/ST1 post-index
                    // transfer the form binder refused (L04-P6; an admitted one
                    // is judged by the SIMD memory lane above, L04-P1): its
                    // decomposition refutes or annotates this arm's row, and
                    // never credits it (`with_memory_effect`). The NEON
                    // horizontal reductions and permutes get their word-bound
                    // LANE EFFECT the same way (`with_neon_lane_effect`).
                    if matches!(
                        inst.opcode,
                        AArch64Opcode::NeonLd1Post | AArch64Opcode::NeonSt1Post
                    ) {
                        self.with_memory_effect(inst, row, xcheck_mode, context, &owned_request)
                    } else if crate::aarch64_neon_lane_effect::NEON_LANE_EFFECT_OPCODES
                        .contains(&inst.opcode)
                    {
                        self.with_neon_lane_effect(inst, row)
                    } else {
                        row
                    }
                } else {
                    // A decoded-value opcode whose operands name none of its
                    // forms is refused by that exact shape, not as a generic
                    // missing mapping.
                    apply_bound_memory_rule(
                        inst,
                        InstructionVerificationResult::Unverified {
                            reason: crate::aarch64_value_decode_proofs::a64_value_unbound_reason(
                                inst,
                            )
                            .or_else(|| {
                                crate::aarch64_value_decode_proofs::neon_bitwise_unbound_reason(
                                    inst,
                                )
                            })
                            .or_else(|| tprel_add_refusal_reason(inst.opcode))
                            .unwrap_or_else(|| {
                                format!("no proof mapping for opcode {:?}", inst.opcode)
                            }),
                        },
                        None,
                        &self.config,
                        context.map(|context| context.request),
                    )
                };
                // L04-P12: merge the trap-guard layer's decision into the row.
                let result = match trap_guard_row {
                    Some(own) => {
                        let opcode = InstructionOpcode::AArch64(inst.opcode);
                        let promotable = inventory_status(opcode, &result).0.is_promotable();
                        crate::aarch64_trap_guard::combine(own, result, promotable)
                    }
                    None => result,
                };

                if let Some(t) = t_arm {
                    walk_split[arm] += t.elapsed();
                    walk_arm_counts[arm] += 1;
                }
                let t_xcheck = walk_timing.then(std::time::Instant::now);
                // TV-2: cross-check the TV-1 provenance sidecar entry against
                // the replayed LIR function. Runs for EVERY stamped
                // instruction (including Skipped pseudos/trap carriers — a
                // misattributed stamp is a misattribution regardless of the
                // proof verdict).
                let result = if let Some(index) = lir_index.as_ref() {
                    let provenance = func.inst_lowering_provenance(inst_id);
                    if provenance.is_source_attributed() {
                        attributed_count += 1;
                    } else {
                        synthetic_count += 1;
                    }
                    match provenance_xcheck::cross_check_inst(
                        &provenance,
                        // The checked complete body establishes semantic
                        // correspondence even for optimized ADD -> LSL. Keep
                        // source coordinates and digest checks mandatory.
                        if source_bound_alu.is_some() || body_row {
                            None
                        } else {
                            aarch64_emitted_op_class(inst)
                        },
                        &format!("{:?}", inst.opcode),
                        index,
                    ) {
                        Some(mismatch) => {
                            mismatch_count += 1;
                            provenance_xcheck::record_provenance_xcheck_hit(
                                "aarch64",
                                &func.name,
                                idx,
                                &mismatch,
                                xcheck_mode,
                            );
                            if xcheck_mode == ProvenanceXCheckMode::Enforce {
                                InstructionVerificationResult::Failed {
                                    proof_name: "provenance-crosscheck (TV-2)".to_string(),
                                    detail: mismatch.detail,
                                }
                            } else {
                                result
                            }
                        }
                        None => result,
                    }
                } else {
                    result
                };

                if let Some(t) = t_xcheck {
                    walk_split[3] += t.elapsed();
                    walk_arm_counts[3] += 1;
                }
                let t_push = walk_timing.then(std::time::Instant::now);
                if let (Some(context), Some(alu)) = (context, source_bound_alu.as_ref())
                    && matches!(
                        result,
                        InstructionVerificationResult::Verified {
                            strength: VerificationStrength::Formal,
                            degenerate: false,
                            ..
                        }
                    )
                {
                    context.retain_alu(idx, alu);
                }
                if let (Some(context), Some(constant)) = (context, source_bound_constant.as_ref())
                    && matches!(
                        result,
                        InstructionVerificationResult::Verified {
                            strength: VerificationStrength::Formal,
                            degenerate: false,
                            ..
                        }
                    )
                {
                    context.retain_constant(idx, constant);
                }
                if let (Some(context), Some((control, _))) = (context, control.as_ref())
                    && control.credits(inst_id)
                    && matches!(
                        result,
                        InstructionVerificationResult::Verified {
                            strength: VerificationStrength::Formal,
                            degenerate: false,
                            ..
                        }
                    )
                {
                    context.retain_a64_control(idx, control);
                }
                if let (Some(context), Some((body, _))) = (context, body.as_ref())
                    && body.credits(inst_id)
                    && matches!(
                        result,
                        InstructionVerificationResult::Verified {
                            strength: VerificationStrength::Formal,
                            degenerate: false,
                            ..
                        }
                    )
                {
                    context.retain_a64_body(idx, body);
                }
                if let (Some(context), Some((owner, _, _))) = (context, whole_body.as_ref())
                    && owner.covers(inst_id)
                    && matches!(
                        result,
                        InstructionVerificationResult::Verified {
                            strength: VerificationStrength::Formal,
                            degenerate: false,
                            ..
                        }
                    )
                {
                    context.retain_a64_whole_body(idx, inst.opcode, owner);
                }
                instructions.push(InstructionReport {
                    inst_index: idx,
                    opcode: InstructionOpcode::AArch64(inst.opcode),
                    result,
                });
                if let Some(t) = t_push {
                    walk_split[4] += t.elapsed();
                }
            }
        }
        if walk_timing {
            let ms = |d: std::time::Duration| d.as_secs_f64() * 1000.0;
            eprintln!(
                "TCG_TIME_WALK fn={} insts={} skip={:.2}ms/{} recon={:.2}ms/{} query={:.2}ms/{} xcheck={:.2}ms/{} push={:.2}ms",
                func.name,
                instructions.len(),
                ms(walk_split[0]),
                walk_arm_counts[0],
                ms(walk_split[1]),
                walk_arm_counts[1],
                ms(walk_split[2]),
                walk_arm_counts[2],
                ms(walk_split[3]),
                walk_arm_counts[3],
                ms(walk_split[4]),
            );
        }

        if lir_index.is_some() {
            provenance_xcheck::trace_function_summary(
                "aarch64",
                &func.name,
                attributed_count,
                synthetic_count,
                mismatch_count,
            );
        }

        // L04-P12: a trap the emitted function lost has no row to fail. The
        // accounting fails the function for a recorded window in no block
        // and, wherever the replayed LIR is indexed, refuses it for a source
        // trap no executing trap row that implements it accounts for; the
        // rows above stay.
        let precondition_failure = trap_analysis
            .accounting()
            .err()
            .map(FunctionVerificationPreconditionFailure::TrapGuardAccounting);

        FunctionVerificationReport {
            function_name: func.name.clone(),
            precondition_failure,
            instructions,
        }
    }
}

impl Default for FunctionVerifier {
    fn default() -> Self {
        Self::new()
    }
}

/// Test seam for the walk's instruction-derived arm: while a word is set on
/// this thread, [`FunctionVerifier::try_instruction_word`] judges every
/// admitted instruction against THAT word instead of the re-derived one, so a
/// test can drive the arm's refutation through a whole walk. Compiled only
/// into this crate's unit tests.
#[cfg(test)]
pub(crate) mod instruction_word_seam {
    use std::cell::Cell;

    thread_local! {
        static WORD: Cell<Option<u32>> = const { Cell::new(None) };
    }

    pub(crate) fn word() -> Option<u32> {
        WORD.with(Cell::get)
    }

    /// Sets the word for this thread until the guard drops.
    pub(crate) fn judge_against(word: u32) -> Guard {
        WORD.with(|cell| cell.set(Some(word)));
        Guard
    }

    pub(crate) struct Guard;

    impl Drop for Guard {
        fn drop(&mut self) {
            WORD.with(|cell| cell.set(None));
        }
    }
}

/// Test seam for the pair lane: while a guard lives, this thread's pair rows
/// build their concrete-word obligation over the given word instead of the
/// re-derived one (`pair_memory_obligation_from_word`), exactly as
/// [`instruction_word_seam`] does for the instruction-derived lane.
#[cfg(test)]
pub(crate) mod pair_word_seam {
    use std::cell::Cell;

    thread_local! {
        static WORD: Cell<Option<u32>> = const { Cell::new(None) };
    }

    pub(crate) fn word() -> Option<u32> {
        WORD.with(Cell::get)
    }

    /// Sets the word for this thread until the guard drops.
    pub(crate) fn judge_against(word: u32) -> Guard {
        WORD.with(|cell| cell.set(Some(word)));
        Guard
    }

    pub(crate) struct Guard;

    impl Drop for Guard {
        fn drop(&mut self) {
            WORD.with(|cell| cell.set(None));
        }
    }
}

/// Test seam for the memory-effect check: while a guard lives, this thread's
/// memory rows build their word-bound memory-effect decomposition over the
/// given word instead of the re-derived one
/// ([`crate::aarch64_memory_effect::memory_effect_for_word`]), leaving the
/// rows' own lanes on their own words, exactly as [`pair_word_seam`] and
/// [`instruction_word_seam`] do for those lanes.
#[cfg(test)]
pub(crate) mod memory_effect_word_seam {
    use std::cell::Cell;

    thread_local! {
        static WORD: Cell<Option<u32>> = const { Cell::new(None) };
    }

    pub(crate) fn word() -> Option<u32> {
        WORD.with(Cell::get)
    }

    /// Sets the word for this thread until the guard drops.
    pub(crate) fn judge_against(word: u32) -> Guard {
        WORD.with(|cell| cell.set(Some(word)));
        Guard
    }

    pub(crate) struct Guard;

    impl Drop for Guard {
        fn drop(&mut self) {
            WORD.with(|cell| cell.set(None));
        }
    }
}

/// Convenience function: verify all instructions in a MachFunction using
/// default configuration.
///
/// This is the primary entry point for function-level verification.
/// Creates a [`FunctionVerifier`] with default settings, walks every
/// instruction in `func`, and returns a [`FunctionVerificationReport`].
pub fn verify_function(func: &MachFunction) -> FunctionVerificationReport {
    let verifier = FunctionVerifier::new();
    verifier.verify(func)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod pair_memory_runtime_tests {
    use super::*;
    use trust_cg_ir::Signature;

    const PAIRS: [AArch64Opcode; 6] = [
        AArch64Opcode::StpRI,
        AArch64Opcode::LdpRI,
        AArch64Opcode::StpPreIndex,
        AArch64Opcode::LdpPostIndex,
        AArch64Opcode::NeonLdpQPost,
        AArch64Opcode::NeonStpQPost,
    ];

    // 22 profiles x (12 concrete shapes + 8 adversarial mutations), plus
    // six operand-less opcodes. None has a source/frame-state binding token.
    // Concrete encoding support and formal applicability are distinct gates.
    fn corpus() -> MachFunction {
        let mut function =
            MachFunction::new("unbound_pair_memory".into(), Signature::new(vec![], vec![]));
        let p = |n| MachOperand::PReg(PReg::new(n));
        for (op_index, opcode) in PAIRS.into_iter().enumerate() {
            let empty = function.push_inst(MachInst::new(opcode, vec![]));
            function.append_inst(function.entry, empty);
            for (bank, scale) in [(0, 8), (32, 4), (128, 4), (96, 8), (64, 16)] {
                if op_index >= 4 && bank != 64 {
                    continue;
                }
                let data0 = p(bank + 1);
                let data1 = p(bank + 2);
                for base in [p(3), p(29), p(31), MachOperand::Special(SpecialReg::SP)] {
                    for offset in [-scale, 0, scale] {
                        let id = function.push_inst(MachInst::new(
                            opcode,
                            vec![
                                data0.clone(),
                                data1.clone(),
                                base.clone(),
                                MachOperand::Imm(offset),
                            ],
                        ));
                        function.append_inst(function.entry, id);
                    }
                }
                for operands in [
                    vec![data0.clone()],
                    vec![
                        data0.clone(),
                        data1.clone(),
                        p(3),
                        MachOperand::Imm(0),
                        MachOperand::Imm(0),
                    ],
                    vec![data0.clone(), data1.clone(), p(3), p(4)],
                    vec![p(31), data1.clone(), p(3), MachOperand::Imm(0)],
                    vec![data0.clone(), p(63), p(3), MachOperand::Imm(0)],
                    vec![data0.clone(), data1.clone(), p(35), MachOperand::Imm(0)],
                    vec![data0.clone(), data1.clone(), p(3), MachOperand::Imm(1)],
                    // Duplicate stores are valid byte intent, unlike duplicate
                    // loads; neither is an authenticated pair proof binding.
                    vec![data0.clone(), data0.clone(), p(3), MachOperand::Imm(0)],
                ] {
                    let id = function.push_inst(MachInst::new(opcode, operands));
                    function.append_inst(function.entry, id);
                }
            }
        }
        assert_eq!(function.insts.len(), 446);
        function
    }

    #[test]
    fn pair_memory_queries_refuse_opcode_concrete_and_block_attribution() {
        let function = corpus();
        let mut wrong = Vec::new();
        for opcode in PAIRS {
            if let Some(query) = FunctionVerifier::opcode_to_proof_query(opcode) {
                wrong.push(format!("opcode {opcode:?}: {query:?}"));
            }
        }
        let block = function.block(function.entry);
        for (position, &id) in block.insts.iter().enumerate() {
            let inst = function.inst(id);
            for (route, query) in [
                ("standalone", FunctionVerifier::inst_to_proof_query(inst)),
                (
                    "in-block",
                    FunctionVerifier::inst_to_proof_query_in_block(
                        &function,
                        &block.insts,
                        position,
                        inst,
                    ),
                ),
            ] {
                if let Some(query) = query {
                    wrong.push(format!("{route} {position} {inst:?}: {query:?}"));
                }
            }
        }
        let failures = wrong.len();
        wrong.truncate(12);
        assert_eq!(
            failures, 0,
            "{failures}/898 unbound query routes inherited authority; first12={wrong:#?}"
        );
    }

    /// The runtime evidence a pair instruction earns is exactly what its
    /// OPERANDS authenticate — and only a formal proof is credit (owner ruling
    /// 2026-09-29, `bound_memory_authority`).
    ///
    /// This corpus mixes 275 well-formed pair shapes with 171 adversarially
    /// malformed ones (bad arity, an SP/WSP transfer, a mismatched bank, a
    /// 32-bit base, a misaligned immediate, a duplicate LOAD destination, an
    /// operand-less carrier). The pair-memory reconstruction lane
    /// (`aarch64_pair_memory_proofs`) builds an operand-bound, non-degenerate
    /// concrete-word obligation for every well-formed shape and discharges it
    /// as the row's REFUTATION check; its sampled `Valid` is never credit.
    /// Every well-formed shape here also binds a pair FORM theorem
    /// (`aarch64_pair_memory_forms`) whose committed certificate the
    /// independent checker replays, so each is credited `Formal`, citing the
    /// form theorem — on a host whose checker the bound-memory manifest
    /// qualifies; on any other host each keeps its sampled reason plus the
    /// Formal-only note and the checker-identity miss (fail closed; the
    /// host-qualification pin is the one red test there). Every malformed
    /// shape is refused and falls through to the
    /// terminal `no proof mapping for opcode` arm, with the Formal-only note.
    /// The malformed rows keep the corpus from promoting.
    ///
    /// Before the ruling's certificates (main 593eecc97) the 275 rows were
    /// `STATISTICAL_EVIDENCE_IS_NOT_CREDIT` and none was verified.
    ///
    /// The word-bound memory-effect decomposition of every admitted row
    /// (`aarch64_memory_effect`, X-OPCODES-P1) then runs as a second
    /// refutation check: no part refutes, a credited row stays credited, and
    /// an uncredited row keeps its reason, prefix included, followed by the
    /// [`MEMORY_EFFECT_IS_NOT_CREDIT`] clause.
    ///
    /// The prewarm enumerates exactly the obligations the walk samples — the
    /// distinct reconstructed pair obligations, plus the memory-effect parts
    /// `aarch64_memory_effect::needs_sampling` names (none here: every part of
    /// this corpus is ground or decided exactly), and nothing else (registry
    /// theorems are not enumerated) — so pre-warmed and serial runs cannot
    /// drift.
    #[test]
    fn pair_memory_runtime_inventory_credits_only_certified_forms() {
        let function = corpus();
        let verifier = FunctionVerifier::with_config(promotion_config(16));
        // Run BOTH the actual prewarm selector (reconstruction-only since
        // registry credit was withdrawn) and the full instruction walk before
        // any result assertion, preserving a complete baseline census.
        let reconstructed = verifier.reconstructed_obligations_for_functions(&[&function]);
        let report = verifier.verify(&function);
        let inventory = report.emitted_opcode_inventory();
        assert_eq!(report.total(), 446);
        assert_eq!(inventory.entries.len(), 446);

        // Partition the corpus by what the pair lane ADMITS, then require the
        // verdict of every row to match its partition exactly.
        let admitted: Vec<bool> = function
            .insts
            .iter()
            .map(|inst| crate::aarch64_pair_memory_proofs::pair_memory_intent(inst).is_some())
            .collect();
        let expected_reconstructed = admitted.iter().filter(|ok| **ok).count();
        assert_eq!(
            expected_reconstructed, 275,
            "well-formed share of the pair corpus changed"
        );

        let qualified = crate::bound_memory_authority::bound_memory_checker_qualification().is_ok();
        let mut wrong: Vec<String> = Vec::new();
        for (row, entry) in inventory.entries.iter().enumerate() {
            let report_row = &report.instructions[row];
            let ok = if admitted[entry.inst_index] && !qualified {
                entry.status == OpcodeInventoryStatus::Unverified
                    && matches!(
                        &report_row.result,
                        InstructionVerificationResult::Unverified { reason }
                            if reason.starts_with(STATISTICAL_EVIDENCE_IS_NOT_CREDIT)
                                && reason.contains(
                                    crate::bound_memory_authority::BOUND_MEMORY_FORMAL_ONLY
                                )
                                && reason.contains(
                                    crate::bound_memory_authority::CHECKER_IDENTITY_MISS
                                )
                                && reason.contains(&format!(
                                    "; {MEMORY_EFFECT_IS_NOT_CREDIT}: `A64 memory effect "
                                ))
                                && reason.contains(" holds in process: all ")
                    )
            } else if admitted[entry.inst_index] {
                entry.status == OpcodeInventoryStatus::Verified
                    && matches!(
                        &report_row.result,
                        InstructionVerificationResult::Verified {
                            proof_name,
                            strength: VerificationStrength::Formal,
                            degenerate: false,
                            ..
                        } if proof_name.starts_with("PairMem[")
                    )
            } else {
                entry.status == OpcodeInventoryStatus::Unverified
                    && report_row.result.is_unverified()
                    && entry.detail.starts_with("no proof mapping for opcode")
                    && entry
                        .detail
                        .contains(crate::bound_memory_authority::BOUND_MEMORY_FORMAL_ONLY)
            };
            if !ok {
                wrong.push(format!(
                    "{row} {:?} admitted={} -> {:?} ({})",
                    function.insts[entry.inst_index].opcode,
                    admitted[entry.inst_index],
                    entry.status,
                    entry.detail
                ));
            }
        }
        let failures = wrong.len();
        wrong.truncate(12);
        assert_eq!(
            failures, 0,
            "{failures}/446 pair rows disagreed with their admission; first12={wrong:#?}"
        );

        // The memory-effect check samples none of the admitted pairs' parts: a
        // ground part, or one decided exactly, is decided in the walk.
        let mut parts = 0usize;
        let mut sampled_parts = 0usize;
        for inst in function
            .insts
            .iter()
            .filter(|inst| crate::aarch64_pair_memory_proofs::pair_memory_intent(inst).is_some())
        {
            for part in crate::aarch64_memory_effect::memory_effect(inst)
                .expect("every admitted pair decomposes")
                .parts
            {
                parts += 1;
                sampled_parts += usize::from(crate::aarch64_memory_effect::needs_sampling(&part));
            }
        }
        // fields, two addresses, the writeback and at least two lanes each.
        assert!(parts >= 6 * 275, "{parts} parts");
        assert_eq!(sampled_parts, 0, "memory-effect parts reach the sampler");

        // So the prewarm must enumerate exactly the distinct pair obligations.
        assert_eq!(
            reconstructed.len(),
            49,
            "distinct pre-warmed pair obligations changed"
        );
        assert!(
            reconstructed
                .iter()
                .all(|(instance, canonical)| instance == canonical
                    && instance.is_reconstructed()
                    && !instance.is_degenerate()
                    && instance.name.starts_with("RECONSTRUCTED PairMemory_")),
            "pre-warmed pair obligations must be reconstructed and non-degenerate"
        );

        let credited = if qualified { 275 } else { 0 };
        assert_eq!(report.sampled_uncredited_count(), 275 - credited);
        assert_eq!(report.memory_effect_count(), 275 - credited);
        assert_eq!(report.registry_name_lookup_count(), 0);
        assert_eq!(report.verified_count(), credited);
        assert_eq!(report.genuinely_verified_count(), credited);
        assert_eq!(report.formally_credited_count(), credited);
        assert!(!report.all_verified());
        assert!(
            !inventory.is_promotable(),
            "the malformed rows are uncredited, so the corpus must block promotion"
        );
        assert_eq!(
            inventory.uncovered_non_pseudo_opcodes().len(),
            171 + (275 - credited)
        );
        assert!(inventory.promotion_rejection_reason().is_some());
    }

    /// The compiler's proof-promotion policy (which replays certificates)
    /// with a small evaluation budget for the concrete-word refutation check.
    fn promotion_config(sample_count: u64) -> VerificationConfig {
        let mut config = VerificationConfig::for_proof_promotion();
        config.sample_count = sample_count;
        config
    }

    fn noted_sampled_pair_rows(report: &FunctionVerificationReport, clause: &str) -> usize {
        report
            .instructions
            .iter()
            .filter(|row| {
                matches!(
                    &row.result,
                    InstructionVerificationResult::Unverified { reason }
                        if reason.starts_with(STATISTICAL_EVIDENCE_IS_NOT_CREDIT)
                            && reason.contains(
                                crate::bound_memory_authority::BOUND_MEMORY_FORMAL_ONLY
                            )
                            && reason.contains("PairMem[")
                            && reason.contains(clause)
                )
            })
            .count()
    }

    /// Without a replayed certificate the admitted pair rows keep exactly
    /// their previous verdict — the sampled concrete-word obligation, reported
    /// and never credited — plus the Formal-only note: under an evaluation-only
    /// walk (which replays nothing), and under the proof-promotion walk with
    /// committed certificates disabled (`TCG_CANARY_NO_CACHE`). Nothing else
    /// can credit a bound-memory row.
    #[test]
    fn pair_memory_rows_without_certificates_are_never_credited() {
        let function = corpus();
        let report = FunctionVerifier::with_config(VerificationConfig::with_sample_count(16))
            .verify(&function);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.sampled_uncredited_count(), 275);
        assert_eq!(report.memory_effect_count(), 275);
        assert_eq!(
            noted_sampled_pair_rows(
                &report,
                crate::bound_memory_authority::CERTIFICATE_REPLAY_OFF
            ),
            275
        );
        // The memory-effect clause comes last, after the Formal-only note,
        // and an evaluation-only walk replays none of its parts.
        assert_eq!(
            noted_sampled_pair_rows(
                &report,
                "parts have a Clean-checked certificate (no live replay under this verification \
                 policy)"
            ),
            275
        );
        crate::env_lock::with_env_edits(|env| {
            env.set("TCG_CANARY_NO_CACHE", "1");
            let report = FunctionVerifier::with_config(promotion_config(16)).verify(&function);
            assert_eq!(report.verified_count(), 0);
            assert_eq!(report.sampled_uncredited_count(), 275);
            assert_eq!(
                noted_sampled_pair_rows(&report, "committed certificates are disabled"),
                275
            );
        });
    }

    #[test]
    fn pair_memory_static_models_remain_diagnostic_not_deleted() {
        let db = ProofDatabase::new();
        let models = [
            crate::frame_proofs::proof_frame_sp_alignment(),
            crate::frame_proofs::proof_frame_callee_save_no_overlap(),
            crate::frame_proofs::proof_frame_callee_save_restore_identity(),
            crate::memory_proofs::proof_ldp_qf_abv_i32_offset0(),
            crate::memory_proofs::proof_ldp_qf_abv_i64_offset0(),
            crate::memory_proofs::proof_ldp_qf_abv_i64_scaled_offset2(),
            crate::memory_proofs::proof_roundtrip_i8(),
        ];
        for model in models {
            assert!(
                !model.is_degenerate(),
                "diagnostic model {} changed",
                model.name
            );
            assert_eq!(
                db.all()
                    .iter()
                    .filter(|row| row.obligation == model)
                    .count(),
                1,
                "diagnostic model {} missing or duplicated",
                model.name
            );
        }
        // Registry presence and non-degeneracy are not applicability, proof
        // discharge, or evidence for any concrete pair/frame instruction.
    }
}

#[cfg(test)]
#[path = "function_verifier_nzcv_tests.rs"]
mod nzcv_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coverage_gate::ALL_AARCH64_OPCODES;
    use trust_cg_ir::aarch64_regs::{SP, X0, X1};
    use trust_cg_ir::types::InstId;
    use trust_cg_ir::{
        AArch64Opcode, FrameIdx, MachInst, MachOperand, Signature, StackSlotId, Type,
    };

    // =======================================================================
    // Test helpers
    // =======================================================================

    fn make_empty_func() -> MachFunction {
        MachFunction::new("test_func".to_string(), Signature::new(vec![], vec![]))
    }

    pub(super) fn make_func_with_insts(insts: Vec<MachInst>) -> MachFunction {
        let mut func = make_empty_func();
        for (i, inst) in insts.into_iter().enumerate() {
            func.insts.push(inst);
            func.blocks[0].insts.push(InstId(i as u32));
        }
        func
    }

    fn inst(opcode: AArch64Opcode) -> MachInst {
        MachInst::new(opcode, vec![])
    }

    /// Review round 2 regression: a conditional-branch CONSUMER's taken edge
    /// carries the TST's NZCV out of the block even when a LATER in-block
    /// flags writer kills the fallthrough copy. If the taken-edge block reads
    /// flags again (here a `CSET HI` — a C-observer, constant after TST), the
    /// TST must FAIL CLOSED rather than earn credit from the covered `B.EQ`;
    /// with a flag-dead taken edge the same shape must still bind.
    #[test]
    fn tst_bcond_taken_edge_reader_fails_closed_despite_inblock_flags_writer() {
        use trust_cg_ir::aarch64_regs::{X0, X1, X2};

        let build = |taken_block_reads_flags: bool| {
            let mut func = make_empty_func();
            let b1 = func.create_block();
            let b2 = func.create_block();
            let entry = func.entry;

            let tst = func.push_inst(MachInst::new(
                AArch64Opcode::Tst,
                vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
            ));
            let bcond = func.push_inst(MachInst::new(
                AArch64Opcode::BCond,
                vec![MachOperand::Imm(0), MachOperand::Block(b1)], // B.EQ
            ));
            let cmp = func.push_inst(MachInst::new(
                AArch64Opcode::CmpRR,
                vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
            ));
            let b = func.push_inst(MachInst::new(
                AArch64Opcode::B,
                vec![MachOperand::Block(b2)],
            ));
            for id in [tst, bcond, cmp, b] {
                func.append_inst(entry, id);
            }
            if taken_block_reads_flags {
                let cset = func.push_inst(MachInst::new(
                    AArch64Opcode::CSet,
                    vec![MachOperand::PReg(X2), MachOperand::Imm(8)], // HI
                ));
                func.append_inst(b1, cset);
            }
            let ret1 = func.push_inst(inst(AArch64Opcode::Ret));
            func.append_inst(b1, ret1);
            let ret2 = func.push_inst(inst(AArch64Opcode::Ret));
            func.append_inst(b2, ret2);
            func.block_mut(entry).succs = vec![b1, b2];
            func
        };

        // Pass the block's OWN insts slice (as the production walk does) —
        // the binder identifies the enclosing block by slice identity.
        let adversarial = build(true);
        assert!(
            FunctionVerifier::tst_nzcv_consumer_query(
                &adversarial,
                &adversarial.blocks[0].insts,
                0
            )
            .is_none(),
            "a taken-edge CSET HI reads the TST's live NZCV: the in-block CMP \
             kills only the FALLTHROUGH copy, so the TST must fail closed"
        );

        let benign = build(false);
        assert_eq!(
            FunctionVerifier::tst_nzcv_consumer_query(&benign, &benign.blocks[0].insts, 0),
            Some(("tst w64: eq", ProofCategory::CmpCombine)),
            "with a flag-dead taken edge the B.EQ consumer must still bind"
        );
    }

    fn inst_with_operands(opcode: AArch64Opcode, operands: Vec<MachOperand>) -> MachInst {
        MachInst::new(opcode, operands)
    }

    #[test]
    fn consulted_category_manifest_covers_every_opcode_query() {
        for &opcode in ALL_AARCH64_OPCODES {
            if let Some((_, category)) = FunctionVerifier::opcode_to_proof_query(opcode) {
                assert!(
                    FunctionVerifier::CONSULTED_CATEGORIES.contains(&category),
                    "{opcode:?} queries undeclared category {}",
                    category.name(),
                );
            }
        }
    }

    #[test]
    fn aarch64_database_matches_full_database_for_consulted_categories() {
        let full = ProofDatabase::new();
        let filtered = ProofDatabase::for_categories(FunctionVerifier::CONSULTED_CATEGORIES);
        assert!(
            filtered
                .all()
                .iter()
                .all(|proof| proof.category != ProofCategory::X8664Lowering),
            "the AArch64 verifier must not construct x86-64 obligations",
        );
        for &category in FunctionVerifier::CONSULTED_CATEGORIES {
            let expected: Vec<&str> = full
                .by_category(category)
                .iter()
                .map(|proof| proof.obligation.name.as_str())
                .collect();
            let actual: Vec<&str> = filtered
                .by_category(category)
                .iter()
                .map(|proof| proof.obligation.name.as_str())
                .collect();
            assert_eq!(
                actual,
                expected,
                "filtered AArch64 database drifted in {}",
                category.name(),
            );
        }
    }

    /// The fixed-registry theorem a retired query names: the first theorem in
    /// `category` whose lowercased name contains `query`, as the withdrawn arm
    /// selected it. Diagnostic resolution only: the walk never credits an
    /// instruction with it.
    fn registry_theorem(query: &str, category: ProofCategory) -> ProofObligation {
        static VERIFIER: std::sync::OnceLock<FunctionVerifier> = std::sync::OnceLock::new();
        VERIFIER
            .get_or_init(FunctionVerifier::new)
            .db
            .all()
            .iter()
            .filter(|p| p.category == category)
            .find(|p| p.obligation.name.to_lowercase().contains(query))
            .unwrap_or_else(|| panic!("query `{query}` must still name a {category:?} theorem"))
            .obligation
            .clone()
    }

    /// The query and category a withdrawn registry refusal reports.
    fn withdrawn_registry_row(result: &InstructionVerificationResult) -> (String, ProofCategory) {
        let InstructionVerificationResult::Unverified { reason } = result else {
            panic!("expected withdrawn registry credit, got {result:?}");
        };
        assert!(
            reason.starts_with(REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT),
            "{reason}"
        );
        let (_, rest) = reason
            .split_once("query `")
            .expect("refusal names its query");
        let (query, rest) = rest
            .split_once("` in ")
            .expect("refusal names its category");
        let (category_name, _) = rest.split_once(" selects").expect("refusal shape");
        let category = *ProofCategory::all_categories()
            .iter()
            .find(|category| category.name() == category_name)
            .unwrap_or_else(|| panic!("unknown category `{category_name}`"));
        (query.to_owned(), category)
    }

    /// E0.2 honest status: the only candidate evidence was the registry theorem
    /// `query` names, so the instruction is unverified and the refusal names it.
    /// L07-P2: an admitted instruction's walk row is its instruction-derived
    /// obligation (`aarch64_instruction_word_proofs`), holding and reported
    /// unverified, never a registry refusal.
    fn assert_instruction_derived(result: &InstructionVerificationResult) {
        match result {
            InstructionVerificationResult::Unverified { reason } => assert!(
                reason.starts_with(INSTRUCTION_DERIVED_IS_NOT_CREDIT)
                    && reason.contains(" holds ("),
                "{reason}"
            ),
            other => panic!("expected an instruction-derived row, got {other:?}"),
        }
    }

    /// X-OPCODES-P1: an uncredited admitted scalar or pair memory row ends
    /// with the clause of its word-bound memory-effect decomposition
    /// (`aarch64_memory_effect`): every part held in process, and the parts'
    /// certificates are recorded, never credited.
    fn assert_memory_effect(result: &InstructionVerificationResult) {
        match result {
            InstructionVerificationResult::Unverified { reason } => {
                let clause = reason
                    .split_once(&format!(
                        "; {MEMORY_EFFECT_IS_NOT_CREDIT}: `A64 memory effect "
                    ))
                    .map(|(_, clause)| clause);
                assert!(
                    clause.is_some_and(|clause| clause.contains("` holds in process: ")
                        && clause.contains(" parts have a Clean-checked certificate")),
                    "{reason}"
                );
            }
            other => panic!("expected an uncredited memory-effect row, got {other:?}"),
        }
    }

    /// [`assert_instruction_derived`] for the row at `position` of a one-block
    /// function (and, for an admitted memory access, [`assert_memory_effect`]),
    /// returning the query the retired registry mapping still names for that
    /// instruction (a diagnostic the walk no longer reaches for it).
    fn instruction_derived_over_retired_query(
        func: &MachFunction,
        report: &FunctionVerificationReport,
        position: usize,
    ) -> (&'static str, ProofCategory) {
        assert_instruction_derived(&report.instructions[position].result);
        let block = &func.blocks[0].insts;
        let inst = &func.insts[block[position].0 as usize];
        if crate::aarch64_memory_effect::memory_effect(inst).is_some() {
            assert_memory_effect(&report.instructions[position].result);
        }
        FunctionVerifier::inst_to_proof_query_in_block(func, block, position, inst)
            .expect("the retired mapping still names a query")
    }

    fn assert_registry_withdrawn(result: &InstructionVerificationResult, query: &str) {
        match result {
            InstructionVerificationResult::Unverified { reason } => {
                assert!(
                    reason.starts_with(REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT),
                    "{reason}"
                );
                assert!(
                    reason.contains(&format!("query `{query}`")),
                    "expected query `{query}`: {reason}"
                );
            }
            other => panic!("expected withdrawn registry credit for `{query}`, got {other:?}"),
        }
    }

    /// E0.2 honest status: an instruction-built reconstruction discharged only
    /// by sampling. It is reported with its reconstructed proof name, never
    /// credited.
    fn assert_sampled_uncredited(result: &InstructionVerificationResult, proof_substring: &str) {
        match result {
            InstructionVerificationResult::Unverified { reason } => {
                assert!(
                    reason.starts_with(STATISTICAL_EVIDENCE_IS_NOT_CREDIT),
                    "{reason}"
                );
                assert!(reason.contains("RECONSTRUCTED"), "{reason}");
                assert!(
                    reason.contains(proof_substring),
                    "expected `{proof_substring}`: {reason}"
                );
            }
            other => panic!("expected an uncredited sampled reconstruction, got {other:?}"),
        }
    }

    /// E0.2 inverse of the former opcode-level credit: an operand-less `opcode`
    /// still names a registry theorem of `expected_category` whose name
    /// contains `theorem_substring`, but that theorem is about a representative
    /// form, so the instruction is unverified and nothing is discharged.
    fn assert_registry_candidate_with_theorem(
        opcode: AArch64Opcode,
        expected_category: ProofCategory,
        theorem_substring: &str,
    ) {
        let (query, category) = FunctionVerifier::opcode_to_proof_query(opcode)
            .unwrap_or_else(|| panic!("{opcode:?} must still map to a registry query"));
        assert_eq!(category, expected_category, "{opcode:?}");
        let theorem = registry_theorem(query, category);
        assert!(
            theorem.name.contains(theorem_substring),
            "{opcode:?} query `{query}` names the wrong theorem: {}",
            theorem.name
        );
        let report = verify_function(&make_func_with_insts(vec![inst(opcode)]));
        assert_eq!(report.verified_count(), 0, "{opcode:?}");
        assert_eq!(report.unverified_count(), 1, "{opcode:?}");
        assert_eq!(report.registry_name_lookup_count(), 1, "{opcode:?}");
        assert_registry_withdrawn(&report.instructions[0].result, query);
    }

    /// Assert an opcode has no runtime proof mapping. This includes retracted
    /// models and retained diagnostic models without an applicability binding.
    fn assert_unverified_no_proof(opcode: AArch64Opcode) {
        assert!(
            FunctionVerifier::opcode_to_proof_query(opcode).is_none(),
            "{opcode:?}: expected no applicable runtime proof mapping"
        );
        let func = make_func_with_insts(vec![inst(opcode)]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.unverified_count(), 1);
        assert!(
            matches!(
                report.instructions[0].result,
                InstructionVerificationResult::Unverified { .. }
            ),
            "{opcode:?}: expected Unverified (no proof), got {:?}",
            report.instructions[0].result
        );
    }

    // =======================================================================
    // 1. Empty function
    // =======================================================================

    #[test]
    fn test_empty_function() {
        let func = make_empty_func();
        let report = verify_function(&func);
        assert_eq!(report.total(), 0);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.skipped_count(), 0);
        assert_eq!(report.unverified_count(), 0);
        assert_eq!(report.coverage_percent(), 100.0);
        assert!(report.all_verified());
    }

    #[test]
    fn test_emitted_opcode_inventory_accepts_verified_and_skipped_aarch64_rows() {
        // A completely (exhaustively) discharged 8-bit extension reconstruction
        // is an honest Verified row; NOP is skipped.
        let uxtb = representative_reconstructable_inst(AArch64Opcode::Uxtb).unwrap();
        let func = make_func_with_insts(vec![uxtb, inst(AArch64Opcode::Nop)]);
        let report = verify_function(&func);
        assert!(matches!(
            &report.instructions[0].result,
            InstructionVerificationResult::Verified {
                strength: VerificationStrength::Exhaustive,
                degenerate: false,
                ..
            }
        ));
        let inventory = report.emitted_opcode_inventory();

        assert_eq!(inventory.entries.len(), 2);
        assert_eq!(
            inventory.entries[0].opcode,
            InstructionOpcode::AArch64(AArch64Opcode::Uxtb)
        );
        assert_eq!(inventory.entries[0].status, OpcodeInventoryStatus::Verified);
        assert_eq!(
            inventory.entries[1].opcode,
            InstructionOpcode::AArch64(AArch64Opcode::Nop)
        );
        assert_eq!(inventory.entries[1].status, OpcodeInventoryStatus::Skipped);
        assert!(inventory.is_promotable());
        assert_eq!(inventory.promotion_rejection_reason(), None);
    }

    /// The census lines (`opcode-inventory-trace`) carry one summary, then one
    /// row per BLOCKING entry with its full reason, tab-separated; the
    /// promotable rows (skipped, covered elsewhere) are counted, not listed.
    /// `scripts/proof_wall_census.py` parses exactly this shape.
    #[test]
    fn census_lines_list_every_blocking_row_with_its_reason() {
        let report = verify_function(&make_func_with_insts(vec![
            inst(AArch64Opcode::Bl),
            inst(AArch64Opcode::Nop),
            inst(AArch64Opcode::Ret),
            inst(AArch64Opcode::Csinv),
        ]));
        let inventory = report.emitted_opcode_inventory();
        let lines = inventory.census_lines();
        assert_eq!(
            lines[0],
            "[TCG-OPCODE-INVENTORY] v1\tsummary\tfunction=test_func\trows=4\tblocking=2\tpromotable=false"
        );
        assert_eq!(lines.len(), 3, "{lines:#?}");
        let blocking = inventory.uncovered_non_pseudo_opcodes();
        for (line, entry) in lines[1..].iter().zip(&blocking) {
            let expected = format!(
                "[TCG-OPCODE-INVENTORY] v1\trow\tfunction=test_func\tindex={}\topcode={}\tstatus={}\tdetail={}",
                entry.inst_index, entry.opcode, entry.status, entry.detail
            );
            assert_eq!(line, &expected);
            assert!(!line.contains('\n'));
        }
        assert!(
            lines[1].contains(
                "opcode=AArch64::Bl\tstatus=unverified\tdetail=no operand-exact evidence"
            )
        );
        assert!(lines[2].contains("opcode=AArch64::Csinv\tstatus=unverified\tdetail="));

        // A precondition failure is a line of its own, and tabs or newlines
        // inside any field are flattened so a line stays one record.
        let mut failed = verify_function(&make_func_with_insts(vec![inst(AArch64Opcode::Ret)]))
            .emitted_opcode_inventory();
        failed.function_name = "f\tg".into();
        failed.precondition_failure =
            Some(FunctionVerificationPreconditionFailure::MissingLirSource);
        let lines = failed.census_lines();
        assert_eq!(
            lines,
            vec![
                "[TCG-OPCODE-INVENTORY] v1\tsummary\tfunction=f g\trows=1\tblocking=0\tpromotable=false"
                    .to_string(),
                format!(
                    "[TCG-OPCODE-INVENTORY] v1\tprecondition\tfunction=f g\tdetail={}",
                    FunctionVerificationPreconditionFailure::MissingLirSource
                ),
            ]
        );
    }

    /// The walk's refutation arm, driven through a whole walk. Judged against
    /// a word whose immediate is not the operand's (the seam stands in for a
    /// disagreement between the verify-side encoder, decoder and intent), an
    /// admitted MOVZ row FAILS, its inventory row is `failed`, and the function
    /// is not promotable; judged against its own word, the same walk holds. In
    /// production the walk decodes the re-derived word, so this arm fires only
    /// on such an internal inconsistency; ENC-5 binds the emitted word.
    #[test]
    fn instruction_word_refutation_fails_the_walk_row() {
        use trust_cg_ir::aarch64_regs::X3;
        let movz = inst_with_operands(
            AArch64Opcode::Movz,
            vec![MachOperand::PReg(X3), MachOperand::Imm(0x1234)],
        );
        let own = crate::aarch64_instruction_word_proofs::instruction_word(&movz)
            .expect("admitted")
            .word;
        assert_eq!(own, 0xd282_4683, "clang: movz x3, #0x1234");
        let func = make_func_with_insts(vec![movz, inst(AArch64Opcode::Ret)]);

        // MOVZ X3, #0x1235: the low bit of imm16 (bits 20:5) flipped.
        let wrong = own ^ (1 << 5);
        let refuted = {
            let _seam = instruction_word_seam::judge_against(wrong);
            verify_function(&func)
        };
        assert_eq!(
            instruction_word_seam::word(),
            None,
            "the guard clears the seam"
        );
        match &refuted.instructions[0].result {
            InstructionVerificationResult::Failed { proof_name, detail } => {
                assert_eq!(
                    proof_name,
                    &format!("A64 instruction word Movz {wrong:#010x}")
                );
                assert!(
                    detail.starts_with("instruction-derived obligation refuted: "),
                    "{detail}"
                );
            }
            other => panic!("expected a failed row, got {other:?}"),
        }
        assert_eq!(refuted.failed_count(), 1);
        assert_eq!(refuted.instruction_derived_count(), 0);
        let inventory = refuted.emitted_opcode_inventory();
        assert_eq!(inventory.entries[0].status, OpcodeInventoryStatus::Failed);
        assert!(!inventory.is_promotable());
        let lines = inventory.census_lines();
        assert!(
            lines[1].contains("\topcode=AArch64::Movz\tstatus=failed\tdetail="),
            "{lines:#?}"
        );

        let holds = {
            let _seam = instruction_word_seam::judge_against(own);
            verify_function(&func)
        };
        assert_instruction_derived(&holds.instructions[0].result);
        assert_eq!(holds.failed_count(), 0);
        // Without the seam the walk re-derives the same word.
        assert_eq!(
            verify_function(&func).emitted_opcode_inventory(),
            holds.emitted_opcode_inventory()
        );
    }

    /// Clause 2 of the Formal-only bound-memory rule (owner ruling
    /// 2026-09-29): a row an in-process check REFUTED stays `Failed`, and a
    /// `Skipped` row stays `Skipped`, even though its form certificate
    /// replays. The refutation checks (the pair lane's concrete-word
    /// obligation, the scalar immediate's instruction-derived obligation) are
    /// the only in-walk tie between the instruction and its operands; a
    /// replayed certificate proves the FORM, never this row.
    ///
    /// Non-vacuous: the same rows, not refuted, are credited `Formal` by their
    /// certificates under the same proof-promotion policy (on a qualified
    /// host). A rule that let the certificate override the refutation turns
    /// this test red on every host: it credits the row where the checker is
    /// qualified, and reaches the rule's `unreachable!` where it is not.
    #[test]
    fn a_refuted_or_skipped_bound_memory_row_is_never_credited_by_its_certificate() {
        use trust_cg_ir::aarch64_regs::{X29, X30};
        let promotion = VerificationConfig::for_proof_promotion();
        let rows = [
            (
                inst_with_operands(
                    AArch64Opcode::StpPreIndex,
                    vec![
                        MachOperand::PReg(X29),
                        MachOperand::PReg(X30),
                        MachOperand::Special(trust_cg_ir::SpecialReg::SP),
                        MachOperand::Imm(-16),
                    ],
                ),
                "PairMem[stp.pre.gpr.w8]",
            ),
            (
                inst_with_operands(
                    AArch64Opcode::StrRI,
                    vec![
                        MachOperand::PReg(X1),
                        MachOperand::PReg(X0),
                        MachOperand::Imm(8),
                    ],
                ),
                "ScalarMem[str.ui.gpr.w8]",
            ),
        ];
        for (inst, form) in rows {
            // The row's own held refutation check: the pair lane's
            // concrete-word obligation, or the instruction-derived one.
            let check =
                match crate::aarch64_pair_memory_proofs::pair_memory_obligation_and_word(&inst) {
                    Some((_, word)) => {
                        crate::bound_memory_authority::BoundMemoryRefutation::pair_concrete_word(
                            word,
                            &VerificationResult::Valid,
                        )
                    }
                    None => crate::aarch64_instruction_word_proofs::instruction_word_verdict(
                        &inst, &promotion,
                    )
                    .as_ref()
                    .and_then(
                        crate::bound_memory_authority::BoundMemoryRefutation::instruction_word,
                    ),
                };
            assert!(check.is_some(), "{form}: its refutation check must hold");
            let held = apply_bound_memory_rule(
                &inst,
                InstructionVerificationResult::Unverified {
                    reason: STATISTICAL_EVIDENCE_IS_NOT_CREDIT.to_string(),
                },
                check,
                &promotion,
                None,
            );
            crate::bound_memory_authority::assert_form_credit_or_checker_miss(
                &held,
                form,
                &format!("{form} held"),
            );

            let refuted = apply_bound_memory_rule(
                &inst,
                InstructionVerificationResult::Failed {
                    proof_name: format!("refutation check of {form}"),
                    detail: "Invalid: counterexample".to_string(),
                },
                check,
                &promotion,
                None,
            );
            match &refuted {
                InstructionVerificationResult::Failed { proof_name, detail } => {
                    assert_eq!(proof_name, &format!("refutation check of {form}"));
                    assert_eq!(detail, "Invalid: counterexample");
                }
                other => panic!("{form}: a refuted row was not left Failed: {other:?}"),
            }

            let skipped = apply_bound_memory_rule(
                &inst,
                InstructionVerificationResult::Skipped {
                    reason: "pseudo".to_string(),
                },
                check,
                &promotion,
                None,
            );
            assert!(
                matches!(&skipped, InstructionVerificationResult::Skipped { reason } if reason == "pseudo"),
                "{form}: a skipped row was not left Skipped: {skipped:?}"
            );
        }
    }

    /// Clause 2 through a whole proof-promotion walk: a scalar immediate
    /// store whose instruction-derived obligation is REFUTED (the seam judges
    /// it against a word whose immediate is not the operand's) FAILS, although
    /// its form theorem's certificate replays; judged against its own word the
    /// same walk credits it `Formal` through that certificate.
    #[test]
    fn a_refuted_scalar_memory_row_fails_the_promotion_walk_despite_its_certificate() {
        let str_ui = inst_with_operands(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::PReg(X1),
                MachOperand::PReg(X0),
                MachOperand::Imm(8),
            ],
        );
        let own = crate::aarch64_instruction_word_proofs::instruction_word(&str_ui)
            .expect("admitted")
            .word;
        assert_eq!(own, 0xf900_0401, "clang: str x1, [x0, #8]");
        let func = make_func_with_insts(vec![str_ui, inst(AArch64Opcode::Ret)]);
        let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());

        // STR X1, [X0, #16]: the low bit of imm12 (bits 21:10) flipped.
        let wrong = own ^ (1 << 10);
        let refuted = {
            let _seam = instruction_word_seam::judge_against(wrong);
            verifier.verify(&func)
        };
        match &refuted.instructions[0].result {
            InstructionVerificationResult::Failed { proof_name, detail } => {
                assert_eq!(
                    proof_name,
                    &format!("A64 instruction word StrRI {wrong:#010x}")
                );
                assert!(
                    detail.starts_with("instruction-derived obligation refuted: "),
                    "{detail}"
                );
            }
            other => panic!("a refuted bound-memory row must fail, got {other:?}"),
        }
        assert_eq!(refuted.failed_count(), 1);
        assert_eq!(refuted.formally_credited_count(), 0);
        assert!(!refuted.emitted_opcode_inventory().is_promotable());

        let holds = {
            let _seam = instruction_word_seam::judge_against(own);
            verifier.verify(&func)
        };
        assert_eq!(holds.failed_count(), 0);
        crate::bound_memory_authority::assert_form_credit_or_checker_miss(
            &holds.instructions[0].result,
            "ScalarMem[str.ui.gpr.w8]",
            "own word",
        );
    }

    /// The word-bound memory-effect check is a refutation check of its own
    /// (X-OPCODES-P1). Judged against a word whose low immediate bit is not
    /// the operands' (the seam leaves the rows' own lanes on their own
    /// words), one of its parts refutes and the row FAILS, although the
    /// row's lane and the Formal-only rule judged it on its own word: credited
    /// `Formal` on a host whose checker the bound-memory manifest qualifies, a
    /// fail-closed checker-identity miss elsewhere. A rule that let that
    /// verdict stand over the refutation turns this red on every host. On its
    /// own word the same walk leaves the lane's verdict in place: the credit
    /// untouched, or the uncredited reason with the memory-effect clause last.
    #[test]
    fn a_refuted_memory_effect_part_fails_the_row_whatever_its_lane_concluded() {
        use trust_cg_ir::aarch64_regs::{X29, X30};
        let rows = [
            (
                inst_with_operands(
                    AArch64Opcode::StrRI,
                    vec![
                        MachOperand::PReg(X1),
                        MachOperand::PReg(X0),
                        MachOperand::Imm(8),
                    ],
                ),
                // imm12, bits 21:10.
                10,
                "ScalarMem[str.ui.gpr.w8]",
            ),
            (
                inst_with_operands(
                    AArch64Opcode::StpPreIndex,
                    vec![
                        MachOperand::PReg(X29),
                        MachOperand::PReg(X30),
                        MachOperand::Special(trust_cg_ir::SpecialReg::SP),
                        MachOperand::Imm(-16),
                    ],
                ),
                // imm7, bits 21:15.
                15,
                "PairMem[stp.pre.gpr.w8]",
            ),
        ];
        let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
        for (row, low_immediate_bit, form) in rows {
            let opcode = row.opcode;
            let own = crate::aarch64_memory_effect::memory_effect_word(&row).expect("admitted");
            let wrong = own ^ (1 << low_immediate_bit);
            let func = make_func_with_insts(vec![row, inst(AArch64Opcode::Ret)]);

            let refuted = {
                let _seam = memory_effect_word_seam::judge_against(wrong);
                verifier.verify(&func)
            };
            match &refuted.instructions[0].result {
                InstructionVerificationResult::Failed { proof_name, detail } => {
                    assert!(
                        proof_name
                            .starts_with(&format!("A64 memory effect {opcode:?} {wrong:#010x}: ")),
                        "{form}: {proof_name}"
                    );
                    assert!(
                        detail.starts_with("memory-effect part refuted in process: "),
                        "{form}: {detail}"
                    );
                }
                other => {
                    panic!("{form}: a refuted memory-effect part must fail the row, got {other:?}")
                }
            }
            assert_eq!(refuted.failed_count(), 1, "{form}");
            assert_eq!(refuted.formally_credited_count(), 0, "{form}");
            assert!(
                !refuted.emitted_opcode_inventory().is_promotable(),
                "{form}"
            );

            let holds = verifier.verify(&func);
            assert_eq!(holds.failed_count(), 0, "{form}");
            let result = &holds.instructions[0].result;
            crate::bound_memory_authority::assert_form_credit_or_checker_miss(
                result, form, "own word",
            );
            if result.is_unverified() {
                assert_memory_effect(result);
                assert!(
                    format!("{result:?}")
                        .contains(&format!("`A64 memory effect {opcode:?} {own:#010x}`")),
                    "{form}: {result:?}"
                );
            }
        }
    }

    #[test]
    fn align_nop_is_narrowly_covered_elsewhere_and_promotable() {
        let opcode = InstructionOpcode::AArch64(AArch64Opcode::AlignNop);
        assert!(is_covered_elsewhere_emission_padding(opcode));
        assert!(!is_covered_elsewhere_emission_padding(
            InstructionOpcode::AArch64(AArch64Opcode::Csinv)
        ));

        let inventory = verify_function(&make_func_with_insts(vec![inst(AArch64Opcode::AlignNop)]))
            .emitted_opcode_inventory();
        assert_eq!(inventory.entries.len(), 1);
        assert_eq!(
            inventory.entries[0].status,
            OpcodeInventoryStatus::CoveredElsewhere
        );
        assert!(inventory.is_promotable());
    }

    #[test]
    fn adrp_addpcrel_address_pair_is_not_promotable_on_registry_theorems() {
        // E0.2: ADRP/ADD lo12 used to be credited to the MachO PAGE21 /
        // PAGEOFF12 relocation theorems by name. Those theorems are about the
        // relocation formula, not these instructions' operands, so an address
        // materialization now blocks promotion again.
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::Adrp),
            inst(AArch64Opcode::AddPCRel),
            inst(AArch64Opcode::Ret),
        ]);
        let report = verify_function(&func);
        for (position, opcode) in [(0, AArch64Opcode::Adrp), (1, AArch64Opcode::AddPCRel)] {
            let (query, category) = FunctionVerifier::opcode_to_proof_query(opcode).unwrap();
            assert_eq!(category, ProofCategory::MachOEmission);
            assert_registry_withdrawn(&report.instructions[position].result, query);
        }
        let inventory = report.emitted_opcode_inventory();
        assert_eq!(
            inventory.entries[0].status,
            OpcodeInventoryStatus::Unverified
        );
        assert_eq!(
            inventory.entries[1].status,
            OpcodeInventoryStatus::Unverified
        );
        assert!(inventory.entries[2].status.is_promotable());
        assert!(!inventory.is_promotable());
    }

    #[test]
    fn direct_branch_and_call_are_not_promotable_on_registry_theorems() {
        // E0.2: B / BL used to be credited to the BRANCH26 call-relocation
        // theorem by name; the indirect Br/Blr/BLR and RET stay CoveredElsewhere.
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::Bl),
            inst(AArch64Opcode::B),
            inst(AArch64Opcode::Br),
            inst(AArch64Opcode::Ret),
        ]);
        let report = verify_function(&func);
        for (position, opcode) in [(0, AArch64Opcode::Bl), (1, AArch64Opcode::B)] {
            let (query, _) = FunctionVerifier::opcode_to_proof_query(opcode).unwrap();
            assert_registry_withdrawn(&report.instructions[position].result, query);
        }
        let inventory = report.emitted_opcode_inventory();
        assert_eq!(
            inventory.entries[0].status,
            OpcodeInventoryStatus::Unverified
        );
        assert_eq!(
            inventory.entries[1].status,
            OpcodeInventoryStatus::Unverified
        );
        assert_eq!(
            inventory.entries[2].status,
            OpcodeInventoryStatus::CoveredElsewhere
        );
        assert_eq!(
            inventory.entries[3].status,
            OpcodeInventoryStatus::CoveredElsewhere
        );
        assert!(!inventory.is_promotable());
    }

    #[test]
    fn neon_addlp_names_exact_arrangement_and_rejects_malformed_shapes() {
        let q = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, trust_cg_ir::RegClass::Fpr128));

        for (opcode, arrangement, expected_query) in [
            (
                AArch64Opcode::NeonUaddlpV,
                1,
                "uaddlpv.16b->.8h lanewise-intent",
            ),
            (
                AArch64Opcode::NeonUaddlpV,
                3,
                "uaddlpv.8h->.4s lanewise-intent",
            ),
            (
                AArch64Opcode::NeonSaddlpV,
                1,
                "saddlpv.16b->.8h lanewise-intent",
            ),
            (
                AArch64Opcode::NeonSaddlpV,
                3,
                "saddlpv.8h->.4s lanewise-intent",
            ),
        ] {
            let addlp = inst_with_operands(opcode, vec![q(0), q(1), MachOperand::Imm(arrangement)]);
            assert_eq!(
                FunctionVerifier::inst_to_proof_query(&addlp),
                Some((expected_query, ProofCategory::NeonLowering)),
                "{opcode:?} arrangement {arrangement} must name its exact theorem"
            );
            assert!(
                registry_theorem(expected_query, ProofCategory::NeonLowering)
                    .name
                    .to_lowercase()
                    .contains(expected_query),
                "{opcode:?} arrangement {arrangement} names the wrong theorem"
            );

            // E0.2: naming the exact arrangement theorem is still not a proof
            // about this instruction's operands.
            let report = verify_function(&make_func_with_insts(vec![addlp]));
            assert_registry_withdrawn(&report.instructions[0].result, expected_query);
        }

        for opcode in [AArch64Opcode::NeonUaddlpV, AArch64Opcode::NeonSaddlpV] {
            for malformed in [
                inst(opcode),
                inst_with_operands(opcode, vec![q(0), q(1)]),
                inst_with_operands(
                    opcode,
                    vec![q(0), q(1), MachOperand::Imm(1), MachOperand::Imm(3)],
                ),
                inst_with_operands(
                    opcode,
                    vec![
                        MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                        q(1),
                        MachOperand::Imm(1),
                    ],
                ),
                inst_with_operands(
                    opcode,
                    vec![q(0), MachOperand::PReg(X0), MachOperand::Imm(1)],
                ),
                inst_with_operands(opcode, vec![q(0), q(1), MachOperand::Imm(5)]),
                inst_with_operands(opcode, vec![q(0), q(1), q(2)]),
            ] {
                assert!(
                    FunctionVerifier::inst_to_proof_query(&malformed).is_none(),
                    "malformed {opcode:?} shape must not inherit an arrangement proof: {:?}",
                    malformed.operands
                );
                let inventory = verify_function(&make_func_with_insts(vec![malformed]))
                    .emitted_opcode_inventory();
                assert_eq!(
                    inventory.entries[0].status,
                    OpcodeInventoryStatus::Unverified,
                    "malformed {opcode:?} must fail closed"
                );
            }
        }
    }

    #[test]
    fn neon_bytesum_pair_memory_debt_blocks_compile_promotion() {
        // The full set of NEON opcodes a byte-widening reduction vectorizer emits.
        // Q-pair memory has no mapping at all. Since E0.2 the value opcodes
        // (MOVI/CNT/UADDLP/ADD/UMOV) only name registry theorems, which is not
        // credit either, so every non-RET row blocks promotion.
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::NeonMovi),
            inst(AArch64Opcode::NeonLdpQPost),
            inst(AArch64Opcode::NeonCntV),
            inst_with_operands(
                AArch64Opcode::NeonUaddlpV,
                vec![
                    MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Fpr128)),
                    MachOperand::VReg(trust_cg_ir::VReg::new(1, trust_cg_ir::RegClass::Fpr128)),
                    MachOperand::Imm(1),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::NeonUaddlpV,
                vec![
                    MachOperand::VReg(trust_cg_ir::VReg::new(2, trust_cg_ir::RegClass::Fpr128)),
                    MachOperand::VReg(trust_cg_ir::VReg::new(3, trust_cg_ir::RegClass::Fpr128)),
                    MachOperand::Imm(3),
                ],
            ),
            inst(AArch64Opcode::NeonAddV),
            inst(AArch64Opcode::NeonUmovGen),
            inst(AArch64Opcode::NeonStpQPost),
            inst(AArch64Opcode::Ret),
        ]);
        let report = verify_function(&func);
        let inventory = report.emitted_opcode_inventory();
        assert!(
            !inventory.is_promotable(),
            "the Q-pair memory gap must block promotion; rejection: {:?}",
            inventory.promotion_rejection_reason()
        );
        for (position, entry) in inventory.entries.iter().enumerate() {
            match position {
                1 | 7 => {
                    assert_eq!(entry.status, OpcodeInventoryStatus::Unverified);
                    assert!(
                        entry.detail.starts_with("no proof mapping for opcode"),
                        "pair memory must have no mapping at all: {entry:?}"
                    );
                }
                8 => assert!(entry.status.is_promotable(), "{entry:?}"),
                _ => {
                    assert_eq!(entry.status, OpcodeInventoryStatus::Unverified);
                    assert!(
                        entry.detail.starts_with(REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT),
                        "value opcode must be a withdrawn registry candidate: {entry:?}"
                    );
                }
            }
        }
        assert_eq!(report.registry_name_lookup_count(), 6);
    }

    #[test]
    fn fused_compare_and_branches_are_per_compile_promotable() {
        // CBZ/CBNZ/TBZ/TBNZ (fused compare-and-branch) are covered-elsewhere
        // CFG edges — a function using them (the cmp-branch-fusion shape, e.g.
        // p7_sieve's `if a[i]==0`) must promote.
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::Cbz),
            inst(AArch64Opcode::Cbnz),
            inst(AArch64Opcode::Tbz),
            inst(AArch64Opcode::Tbnz),
            inst(AArch64Opcode::Ret),
        ]);
        let inventory = verify_function(&func).emitted_opcode_inventory();
        assert!(
            inventory.is_promotable(),
            "CBZ/CBNZ/TBZ/TBNZ must be per-compile promotable; rejection: {:?}",
            inventory.promotion_rejection_reason()
        );
        for e in &inventory.entries {
            if !matches!(e.opcode, InstructionOpcode::AArch64(AArch64Opcode::Ret)) {
                assert_eq!(
                    e.status,
                    OpcodeInventoryStatus::CoveredElsewhere,
                    "{:?} must be CoveredElsewhere",
                    e.opcode
                );
            }
        }
    }

    #[test]
    fn writeback_and_literal_memory_forms_are_not_promotable_on_registry_theorems() {
        // E0.2: the scalar writeback/literal forms used to borrow the broad
        // `"load"`/`"store"` Memory theorems (an I32 LDP pair and a byte
        // roundtrip). They now block promotion like the pair forms.
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::LdrPostIndex),
            inst(AArch64Opcode::StrPreIndex),
            inst(AArch64Opcode::LdrLiteral),
            inst(AArch64Opcode::Ret),
        ]);
        let report = verify_function(&func);
        assert_registry_withdrawn(&report.instructions[0].result, "load");
        assert_registry_withdrawn(&report.instructions[1].result, "store");
        assert_registry_withdrawn(&report.instructions[2].result, "load");
        let inventory = report.emitted_opcode_inventory();
        assert!(inventory.entries[3].status.is_promotable());
        assert!(!inventory.is_promotable());
    }

    #[test]
    fn registry_mapped_and_const_mat_opcodes_do_not_promote() {
        // E0.2: this batch was wired to EXISTING registered theorems by query:
        // EorRRShift (bitwise ROR-shift), MovI (const-mat), Cas (compare-and-swap),
        // Ldar/Stlr (atomic load/store), the NEON widening/accumulate families
        // and the LSE fetch-op RMWs. Each still names its theorem, but a named
        // theorem is not a proof about the emitted instruction, so none of them
        // promotes. AddTprelHi12/Lo12 left this batch in the L04-P11 review and
        // no longer name a theorem at all: see
        // `tprel_adds_and_malformed_neon_orr_are_refused`.
        for op in [
            AArch64Opcode::EorRRShift,
            AArch64Opcode::AddRRShift,
            AArch64Opcode::SubRRShift,
            AArch64Opcode::AddRRShiftLsr,
            AArch64Opcode::NeonSmlalV,
            AArch64Opcode::NeonSmlal2V,
            AArch64Opcode::NeonUmlalV,
            AArch64Opcode::NeonUmlal2V,
            AArch64Opcode::NeonUaddwV,
            AArch64Opcode::NeonUaddw2V,
            AArch64Opcode::NeonSaddwV,
            AArch64Opcode::NeonSaddw2V,
            AArch64Opcode::NeonMlaV,
            AArch64Opcode::NeonUadalpV,
            AArch64Opcode::MovI,
            AArch64Opcode::Cas,
            AArch64Opcode::Ldar,
            AArch64Opcode::Stlr,
            AArch64Opcode::Ldadd,
            AArch64Opcode::Ldaddal,
            AArch64Opcode::Ldset,
            AArch64Opcode::Ldeor,
            AArch64Opcode::Ldclr,
        ] {
            let tested = if op == AArch64Opcode::MovI {
                inst_with_operands(
                    op,
                    vec![
                        MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                        MachOperand::Imm(1),
                    ],
                )
            } else {
                inst(op)
            };
            let (query, _) = FunctionVerifier::inst_to_proof_query(&tested)
                .unwrap_or_else(|| panic!("{op:?} must still name a registry theorem"));
            let func = make_func_with_insts(vec![tested, inst(AArch64Opcode::Ret)]);
            let report = verify_function(&func);
            assert_registry_withdrawn(&report.instructions[0].result, query);
            let inv = report.emitted_opcode_inventory();
            assert!(!inv.is_promotable(), "{op:?} must not promote");
        }
    }

    /// L04-P11 second review: the TLSLE TPREL adds have no obligation bound to
    /// the instruction or its bytes, so no instance promotes, well-formed or
    /// not; and ORR (vector) binds only the 16B register copy (decoded-word
    /// form) and the three-register 16B OR (lanewise obligation), per
    /// instruction. Every other ORR (vector) shape is refused by its shape.
    #[test]
    fn tprel_adds_and_malformed_neon_orr_are_refused() {
        use crate::aarch64_value_decode_proofs::A64ValueForm;
        use trust_cg_ir::regs::{PReg, VReg};
        use trust_cg_ir::{RegClass, aarch64_regs::X2};
        let q = |n: u16| MachOperand::PReg(PReg::new(64 + n));
        let d = |n: u16| MachOperand::PReg(PReg::new(96 + n));
        let s = |n: u16| MachOperand::PReg(PReg::new(128 + n));
        let vq = |id: u32| MachOperand::VReg(VReg::new(id, RegClass::Fpr128));
        let refused = |copy: MachInst, prefix: &str| {
            let report = verify_function(&make_func_with_insts(vec![copy.clone()]));
            match &report.instructions[0].result {
                InstructionVerificationResult::Unverified { reason } => {
                    assert!(reason.starts_with(prefix), "{copy:?}: {reason}")
                }
                other => panic!("{copy:?} must stay Unverified: {other:?}"),
            }
            assert!(
                !report.emitted_opcode_inventory().is_promotable(),
                "{copy:?}"
            );
        };
        for opcode in [AArch64Opcode::AddTprelHi12, AArch64Opcode::AddTprelLo12] {
            assert_eq!(FunctionVerifier::opcode_to_proof_query(opcode), None);
            let prefix = format!("{opcode:?} is not credited: the TLSLE");
            refused(inst(opcode), &prefix);
            refused(
                inst_with_operands(
                    opcode,
                    vec![
                        MachOperand::PReg(X0),
                        MachOperand::PReg(X2),
                        MachOperand::Symbol("tls_var".into()),
                    ],
                ),
                &prefix,
            );
            refused(inst_with_operands(opcode, vec![d(0), d(1)]), &prefix);
        }

        let orr = AArch64Opcode::NeonOrrV;
        assert_eq!(FunctionVerifier::opcode_to_proof_query(orr), None);
        // The register copy names its decoded-word form; since E0.2 that
        // registry theorem, found by name, is refused rather than credited.
        for operands in [
            vec![q(3), q(7), q(7)],
            vec![d(0), d(1), d(1), MachOperand::Imm(1)],
            vec![s(2), s(5), s(5), MachOperand::Imm(1)],
            vec![vq(0), vq(1), vq(1)],
        ] {
            let copy = inst_with_operands(orr, operands);
            assert_eq!(
                FunctionVerifier::inst_to_proof_query(&copy),
                Some((
                    A64ValueForm::MovV16B.query(),
                    A64ValueForm::MovV16B.category()
                )),
                "{copy:?}"
            );
            let report = verify_function(&make_func_with_insts(vec![copy.clone()]));
            assert_registry_withdrawn(
                &report.instructions[0].result,
                A64ValueForm::MovV16B.query(),
            );
            assert!(
                !report.emitted_opcode_inventory().is_promotable(),
                "{copy:?}"
            );
        }
        // The three-register 16B OR binds the lanewise obligation.
        for operands in [vec![q(0), q(1), q(2)], vec![vq(0), vq(1), vq(2)]] {
            let vector_or = inst_with_operands(orr, operands);
            assert_eq!(
                FunctionVerifier::inst_to_proof_query(&vector_or),
                Some(("orrv.16b lanewise-intent", ProofCategory::NeonLowering)),
                "{vector_or:?}"
            );
        }
        // A two-source OR mixing virtual and physical registers is an OR,
        // never a copy (the virtual ones are numbered apart).
        let v1 = q(1);
        let v0 = q(0);
        for operands in [
            vec![vq(10), v1.clone(), vq(20)],
            vec![v1.clone(), vq(20), v0.clone()],
        ] {
            let mixed = inst_with_operands(orr, operands);
            assert_eq!(
                FunctionVerifier::inst_to_proof_query(&mixed),
                Some(("orrv.16b lanewise-intent", ProofCategory::NeonLowering)),
                "{mixed:?}"
            );
        }
        // Everything else is refused by its shape.
        for operands in [
            vec![],
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X1),
            ],
            vec![s(0), s(1), s(2), MachOperand::Imm(1)],
            vec![d(0), d(1), d(2)],
            vec![d(0), d(1), d(1)],
            vec![q(0), q(1), q(2), MachOperand::Imm(1)],
            vec![q(0), q(1), q(1), MachOperand::Imm(7)],
        ] {
            refused(
                inst_with_operands(orr, operands),
                "no decoded-value form binds NeonOrrV ",
            );
        }
    }

    /// NEON AND/EOR/BIC/NOT (L04-P11 third review): no opcode-wide credit;
    /// the 16B shape binds its lanewise obligation and the 8B shapes (V64
    /// operands) are refused by shape, as for ORR.
    #[test]
    fn neon_bitwise_8b_shapes_are_refused_like_orr() {
        use trust_cg_ir::RegClass;
        use trust_cg_ir::regs::{PReg, VReg};
        let q = |n: u16| MachOperand::PReg(PReg::new(64 + n));
        let d = |n: u16| MachOperand::PReg(PReg::new(96 + n));
        let vd = |id: u32| MachOperand::VReg(VReg::new(id, RegClass::Fpr64));
        // The expected bindings are spelled as literals so the walk-query
        // golden keeps pinning what each query resolves to.
        for (opcode, bound) in [
            (
                AArch64Opcode::NeonAndV,
                Some(("andv.16b lanewise-intent", ProofCategory::NeonLowering)),
            ),
            (
                AArch64Opcode::NeonEorV,
                Some(("eorv.16b lanewise-intent", ProofCategory::NeonLowering)),
            ),
            (
                AArch64Opcode::NeonBicV,
                Some(("bicv.16b lanewise-intent", ProofCategory::NeonLowering)),
            ),
            (
                AArch64Opcode::NeonNotV,
                Some(("notv.16b lanewise-intent", ProofCategory::NeonLowering)),
            ),
        ] {
            assert_eq!(FunctionVerifier::opcode_to_proof_query(opcode), None);
            let wide = if opcode == AArch64Opcode::NeonNotV {
                vec![q(0), q(1)]
            } else {
                vec![q(0), q(1), q(2)]
            };
            assert_eq!(
                FunctionVerifier::inst_to_proof_query(&inst_with_operands(opcode, wide)),
                bound
            );
            let narrow: [Vec<MachOperand>; 2] = if opcode == AArch64Opcode::NeonNotV {
                [vec![d(0), d(1)], vec![vd(0), vd(1)]]
            } else {
                [vec![d(0), d(1), d(2)], vec![vd(0), vd(1), vd(2)]]
            };
            for operands in narrow {
                let shape = inst_with_operands(opcode, operands);
                assert_eq!(FunctionVerifier::inst_to_proof_query(&shape), None);
                let report = verify_function(&make_func_with_insts(vec![shape.clone()]));
                match &report.instructions[0].result {
                    InstructionVerificationResult::Unverified { reason } => assert!(
                        reason.starts_with(&format!("no bound shape for {opcode:?} ")),
                        "{shape:?}: {reason}"
                    ),
                    other => panic!("{shape:?} must stay Unverified: {other:?}"),
                }
                assert!(!report.emitted_opcode_inventory().is_promotable());
            }
        }
    }

    /// L04-P11 fifth review: ADDS/SUBS with an extra operand, NEG with one
    /// after its two registers, and an immediate-form ADD/SUB/AND/ORR/EOR/LSL/
    /// LSR/ASR with a register third operand bind nothing on any arm (not the
    /// reconstruction, not the opcode-wide query).
    #[test]
    fn malformed_alu_shapes_are_refused_on_every_arm() {
        use trust_cg_ir::aarch64_regs::X2;
        let x = |p| MachOperand::PReg(p);
        let mut shapes = vec![
            (
                AArch64Opcode::AddsRR,
                vec![x(X0), x(X1), x(X2), MachOperand::Imm(3)],
            ),
            (
                AArch64Opcode::SubsRR,
                vec![x(X0), x(X1), x(X2), MachOperand::Imm(3)],
            ),
            (AArch64Opcode::Neg, vec![x(X0), x(X1), MachOperand::Imm(3)]),
        ];
        for opcode in [
            AArch64Opcode::AddRI,
            AArch64Opcode::SubRI,
            AArch64Opcode::AndRI,
            AArch64Opcode::OrrRI,
            AArch64Opcode::EorRI,
            AArch64Opcode::LslRI,
            AArch64Opcode::LsrRI,
            AArch64Opcode::AsrRI,
        ] {
            shapes.push((opcode, vec![x(X0), x(X1), x(X2)]));
        }
        for (opcode, operands) in shapes {
            let shape = inst_with_operands(opcode, operands);
            assert_eq!(
                FunctionVerifier::inst_to_proof_query(&shape),
                None,
                "{shape:?}"
            );
            assert!(reconstruct_alu_obligation(&shape).is_none(), "{shape:?}");
            let report = verify_function(&make_func_with_insts(vec![shape.clone()]));
            match &report.instructions[0].result {
                InstructionVerificationResult::Unverified { reason } => assert!(
                    reason.starts_with(&format!("{opcode:?} with ")),
                    "{shape:?}: {reason}"
                ),
                other => panic!("{shape:?} must stay Unverified: {other:?}"),
            }
            assert!(!report.emitted_opcode_inventory().is_promotable());
        }
        // The well-formed shapes still bind their operand reconstruction. A
        // 64-bit reconstruction discharges only by sampling, so since E0.2 it
        // is reported with its obligation and sample count, not credited.
        for (opcode, operands) in [
            (
                AArch64Opcode::LslRI,
                vec![x(X0), x(X1), MachOperand::Imm(3)],
            ),
            (
                AArch64Opcode::AddRI,
                vec![x(X0), x(X1), MachOperand::Imm(3)],
            ),
            (AArch64Opcode::Neg, vec![x(X0), x(X1)]),
        ] {
            let shape = inst_with_operands(opcode, operands);
            assert!(reconstruct_alu_obligation(&shape).is_some(), "{shape:?}");
            let report = verify_function(&make_func_with_insts(vec![shape.clone()]));
            assert_sampled_uncredited(&report.instructions[0].result, &format!("-> {opcode:?}"));
        }
    }

    /// L04-P11 fourth review: a register-register ADD/SUB/AND/ORR/EOR with an
    /// operand after its three registers (a shift the encoder drops and ENC-5
    /// does not decode) binds nothing; the three-register shape still binds.
    #[test]
    fn register_alu_with_an_extra_operand_is_refused() {
        use trust_cg_ir::aarch64_regs::X2;
        for opcode in [
            AArch64Opcode::AddRR,
            AArch64Opcode::SubRR,
            AArch64Opcode::AndRR,
            AArch64Opcode::OrrRR,
            AArch64Opcode::EorRR,
        ] {
            let three = inst_with_operands(
                opcode,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                    MachOperand::PReg(X2),
                ],
            );
            // The three-register shape binds its reconstruction, which is
            // sampled at 64 bits and so reported, not credited (E0.2).
            assert!(reconstruct_alu_obligation(&three).is_some(), "{three:?}");
            let report = verify_function(&make_func_with_insts(vec![three.clone()]));
            assert_sampled_uncredited(&report.instructions[0].result, &format!("-> {opcode:?}"));
            let four = inst_with_operands(
                opcode,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                    MachOperand::PReg(X2),
                    MachOperand::Imm(3),
                ],
            );
            assert_eq!(FunctionVerifier::inst_to_proof_query(&four), None);
            let report = verify_function(&make_func_with_insts(vec![four.clone()]));
            match &report.instructions[0].result {
                InstructionVerificationResult::Unverified { reason } => assert!(
                    reason.starts_with(&format!("{opcode:?} with 4 operands is not credited")),
                    "{four:?}: {reason}"
                ),
                other => panic!("{four:?} must stay Unverified: {other:?}"),
            }
            assert!(!report.emitted_opcode_inventory().is_promotable());
        }
    }

    #[test]
    fn atomic_exclusive_and_malformed_swap_still_block_promotion() {
        // NARROWNESS. The LL/SC exclusives have no proof at all and must keep
        // blocking. SWP must keep blocking OPCODE-WIDE: the opcode alone cannot
        // say which width was emitted, and the credit has to be width-correct, so
        // `opcode_to_proof_query` leaves it unmapped and any shape the
        // operand-sensitive arm cannot classify falls closed here.
        //
        // CORRECTION: this test used to justify itself with "SWP ... have NO
        // retained proof (`all_atomic_proofs()` retracted the degenerate 'returns
        // old value' obligation)". That conflated two halves. The #62 retraction
        // removes only the `": returns old value"` names; `SWP_I{32,64}:
        // mem[addr] = operand` are registered and retained, exactly like the
        // `LDADD_I*` memory proofs. What SWP lacked was a WIDTH-CORRECT binding,
        // not a proof. See `well_formed_swap_binds_its_own_width_but_is_uncredited`.
        for op in [
            AArch64Opcode::Swp,
            AArch64Opcode::Swpal,
            AArch64Opcode::Ldaxr,
        ] {
            assert!(
                FunctionVerifier::opcode_to_proof_query(op).is_none(),
                "{op:?} must have NO opcode-WIDE proof query"
            );
            // A bare (operand-less) instruction is exactly the shape the
            // operand-sensitive arm must refuse rather than credit.
            let func = make_func_with_insts(vec![inst(op), inst(AArch64Opcode::Ret)]);
            assert!(
                !verify_function(&func)
                    .emitted_opcode_inventory()
                    .is_promotable(),
                "{op:?} with no operands must keep blocking per-compile promotion"
            );
        }
    }

    /// The positive half: a WELL-FORMED SWP binds the memory obligation FOR ITS
    /// OWN WIDTH, and every shape whose width cannot be established binds
    /// nothing.
    ///
    /// Operand shape is `encode_lse_atomic`'s: [Rs (value in), Rt (old out),
    /// Rn (address)]. The narrow byte/half forms carry a 4th access-size immediate
    /// precisely because i8/i16/i32 all use W registers — and there is no
    /// `SWP_I8`/`SWP_I16` obligation, so those must NOT bind the 32-bit theorem.
    ///
    /// E0.2: the binding is a registry query, so even the well-formed shapes
    /// are refused as registry name lookups naming their width's theorem, and
    /// no SWP promotes.
    #[test]
    fn well_formed_swap_binds_its_own_width_but_is_uncredited() {
        use trust_cg_ir::aarch64_regs::{W0, W1, W2, X0, X1, X2};

        let swap = |operands: Vec<MachOperand>| inst_with_operands(AArch64Opcode::Swpal, operands);
        let report_for = |candidate: MachInst| {
            verify_function(&make_func_with_insts(vec![
                candidate,
                inst(AArch64Opcode::Ret),
            ]))
        };

        // 64-bit: X value, X result, X address -> `swp_i64: mem`;
        // 32-bit: W value, W result, X address -> `swp_i32: mem`.
        for (operands, query) in [
            (
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                    MachOperand::PReg(X2),
                ],
                "swp_i64: mem",
            ),
            (
                vec![
                    MachOperand::PReg(W0),
                    MachOperand::PReg(W1),
                    MachOperand::PReg(X2),
                ],
                "swp_i32: mem",
            ),
        ] {
            let well_formed = swap(operands);
            assert_eq!(
                FunctionVerifier::inst_to_proof_query(&well_formed),
                Some((query, ProofCategory::AtomicOperations)),
                "a well-formed SWP must bind exactly its own width's memory obligation"
            );
            // The walk judges it by its atomic form (X-OPCODES-P2), not by the
            // registry name: under this evaluation-only walk no certificate is
            // replayed, so the held decomposition is reported, never credited.
            let report = report_for(well_formed);
            assert_eq!(report.verified_count(), 0, "{query}");
            assert_eq!(report.registry_name_lookup_count(), 0, "{query}");
            match &report.instructions[0].result {
                InstructionVerificationResult::Unverified { reason } => assert!(
                    reason.contains(ATOMIC_EFFECT_IS_NOT_CREDIT)
                        && reason.contains(crate::bound_memory_authority::CERTIFICATE_REPLAY_OFF),
                    "{query}: {reason}"
                ),
                other => panic!("{query}: {other:?}"),
            }
            assert!(
                !report.emitted_opcode_inventory().is_promotable(),
                "{query}"
            );
        }

        // NARROW (byte/half): a 4th access-size immediate. W registers, so the
        // register class alone would say "32-bit" — the binding must NOT be given.
        // Mismatched value/result widths, and a non-64-bit address, are shapes the
        // encoder never emits; neither may fall back to an opcode-wide binding.
        let mut unbindable: Vec<(Vec<MachOperand>, &str)> = [0, 1]
            .into_iter()
            .map(|size_imm| {
                (
                    vec![
                        MachOperand::PReg(W0),
                        MachOperand::PReg(W1),
                        MachOperand::PReg(X2),
                        MachOperand::Imm(size_imm),
                    ],
                    "a narrow (byte/half) SWP has no SWP_I8/I16 registry obligation; only its \
                     atomic form theorem judges it",
                )
            })
            .collect();
        unbindable.push((
            vec![
                MachOperand::PReg(W0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
            ],
            "a value/result width mismatch must fail closed",
        ));
        unbindable.push((
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(W2),
            ],
            "a non-64-bit address operand must fail closed",
        ));
        for (operands, why) in unbindable {
            let malformed = swap(operands);
            assert_eq!(
                FunctionVerifier::inst_to_proof_query(&malformed),
                None,
                "{why}"
            );
            let report = report_for(malformed);
            assert_eq!(report.verified_count(), 0, "{why}");
            assert_eq!(report.registry_name_lookup_count(), 0, "{why}");
            assert!(!report.emitted_opcode_inventory().is_promotable(), "{why}");
        }
    }

    #[test]
    fn conditional_select_valid_shapes_do_not_borrow_structural_credit() {
        use trust_cg_ir::aarch64_regs::{W0, W1, W2, X2};

        let verifier = FunctionVerifier::new();
        let mut checked = 0;
        for opcode in [
            AArch64Opcode::Csel,
            AArch64Opcode::Csinc,
            AArch64Opcode::Csneg,
        ] {
            assert!(!is_covered_elsewhere_indirect_branch(
                InstructionOpcode::AArch64(opcode)
            ));
            for regs in [[W0, W1, W2], [X0, X1, X2]] {
                for condition in 0..16 {
                    let func = make_func_with_insts(vec![inst_with_operands(
                        opcode,
                        vec![
                            MachOperand::PReg(regs[0]),
                            MachOperand::PReg(regs[1]),
                            MachOperand::PReg(regs[2]),
                            MachOperand::Imm(condition),
                        ],
                    )]);
                    let report = verifier.verify_with_lir_source_and_mode(
                        &func,
                        None,
                        ProvenanceXCheckMode::Off,
                    );
                    assert_eq!(report.instructions.len(), 1);
                    assert_eq!(report.genuinely_verified_count(), 0);
                    assert_eq!(report.unverified_count(), 1);
                    let inventory = report.emitted_opcode_inventory();
                    assert_eq!(
                        inventory.entries[0].status,
                        OpcodeInventoryStatus::Unverified
                    );
                    assert!(
                        !inventory.is_promotable(),
                        "{opcode:?} condition {condition}"
                    );
                    checked += 1;
                }
            }
        }
        assert_eq!(checked, 96);
    }

    // Constructed public-API regression inputs, not compiler-produced code or
    // certified source correspondence. Matching source stamps must not make an
    // unrelated static comparison template applicable to FCMP/CSET.
    fn fcmp_runtime_lir(
        double: bool,
        cond: trust_cg_lower::instructions::FloatCC,
    ) -> trust_cg_lower::Function {
        use trust_cg_lower::function::{BasicBlock, Signature as LirSignature};
        use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
        use trust_cg_lower::types::Type as LirType;
        let fp = if double { LirType::F64 } else { LirType::F32 };
        let mut lir = trust_cg_lower::Function::new(
            "test_func",
            LirSignature {
                params: vec![fp.clone(), fp.clone()],
                returns: vec![LirType::B1],
            },
        );
        lir.block_order.push(Block(0));
        lir.blocks.insert(
            Block(0),
            BasicBlock {
                params: vec![(Value(0), fp.clone()), (Value(1), fp)],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Fcmp { cond },
                        args: vec![Value(0), Value(1)],
                        results: vec![Value(2)],
                    },
                    Instruction {
                        opcode: Opcode::Return,
                        args: vec![Value(2)],
                        results: vec![],
                    },
                ],
                source_locs: vec![],
            },
        );
        lir
    }

    fn fcmp_runtime_stamped_function(
        insts: Vec<MachInst>,
        lir: &trust_cg_lower::Function,
    ) -> MachFunction {
        use trust_cg_ir::provenance::{LoweringProvenance, SourceInstId};
        use trust_cg_lower::instructions::Block;
        let mut func = make_func_with_insts(insts);
        let digest = lir.blocks[&Block(0)].instructions[0].lowering_digest();
        for index in 0..func.insts.len() {
            func.set_inst_lowering_provenance(
                InstId(index as u32),
                LoweringProvenance::SourceInst {
                    id: SourceInstId { block: 0, index: 0 },
                    digest,
                    trust_ir_inst: None,
                },
            );
        }
        func
    }

    fn fcmp_runtime_cset(cc: i64, dst: trust_cg_ir::PReg) -> MachInst {
        MachInst::new(
            AArch64Opcode::CSet,
            vec![MachOperand::PReg(dst), MachOperand::Imm(cc)],
        )
    }

    fn fcmp_runtime_report(
        verifier: &FunctionVerifier,
        func: &MachFunction,
        lir: &trust_cg_lower::Function,
        mode: ProvenanceXCheckMode,
    ) -> FunctionVerificationReport {
        let report = verifier.verify_with_lir_source_and_mode(func, Some(lir), mode);
        assert!(
            report.precondition_failure.is_none(),
            "{:?}",
            report.precondition_failure
        );
        assert_eq!(report.instructions.len(), func.insts.len());
        assert!(!report.instructions.is_empty());
        assert!(
            !tv2_provenance_failure(&report),
            "expected an applicability test, not a TV-2 failure"
        );
        report
    }

    fn fcmp_runtime_unbound_row_count(report: &FunctionVerificationReport) -> (usize, usize) {
        let mut checked = 0;
        let mut wrong = 0;
        let inventory = report.emitted_opcode_inventory();
        for (index, row) in report.instructions.iter().enumerate() {
            if !matches!(
                row.opcode,
                InstructionOpcode::AArch64(AArch64Opcode::Fcmp | AArch64Opcode::CSet)
            ) {
                continue;
            }
            checked += 1;
            assert!(!is_covered_elsewhere_indirect_branch(row.opcode));
            assert!(!is_covered_elsewhere_emission_padding(row.opcode));
            if !matches!(row.result, InstructionVerificationResult::Unverified { .. }) {
                wrong += 1;
            } else {
                assert_eq!(
                    inventory.entries[index].status,
                    OpcodeInventoryStatus::Unverified
                );
                assert!(!inventory.is_promotable());
            }
        }
        assert!(checked > 0, "no FCMP/CSET row was exercised");
        (checked, wrong)
    }

    /// The registered obligation name a query resolves to in the verifier's
    /// own database.
    fn fcmp_runtime_resolved(
        verifier: &FunctionVerifier,
        query: &'static str,
        category: ProofCategory,
    ) -> String {
        verifier
            .registry_proof_for_query(query, category)
            .unwrap_or_else(|| panic!("{query} must resolve"))
            .obligation
            .name
            .clone()
    }

    /// Constructed public-API inputs (not compiler-produced code). Every FCMP
    /// and CSET row names, and since E0.2 is refused on, ONLY the obligation
    /// named by its own
    /// width and condition and by its actual REACHING producer: the FCMP to its
    /// width's packed-NZCV obligation, a CSET to the FCMP -> CSET obligation of
    /// the FCMP that reaches it (the later D-width FCMP after a D clobber), or
    /// to `Icmp_<cc>_I32` when an integer CMP intervenes. No row inherits a
    /// static `Fcmp_*` template, whatever the stamped source predicate says.
    /// Per-instruction credit is machine-level: it does NOT certify that the
    /// FCMP's operand order matches the source `fcmp` (the swapped variant
    /// binds too); source correspondence is the source-bound frame's job.
    #[test]
    fn fcmp_runtime_rows_bind_only_their_reaching_producer_obligation() {
        use crate::aarch64_flag_consumer_proofs::{
            FLAG_CONSUMER_CATEGORY, fcmp_cset_query, fcmp_packed_query,
        };
        use trust_cg_ir::aarch64_regs::{D0, D1, S0, S1, W0};
        use trust_cg_lower::instructions::FloatCC;
        let verifier = FunctionVerifier::with_config(VerificationConfig::with_sample_count(16));
        let (mut reports, mut rows, mut wrong) = (0, 0, 0);
        let mut first_wrong = None;
        for double in [false, true] {
            let width = if double { 64 } else { 32 };
            for cond in [FloatCC::GreaterThanOrEqual, FloatCC::NotEqual] {
                let lir = fcmp_runtime_lir(double, cond);
                for swap in [false, true] {
                    let [a, b] = if double { [D0, D1] } else { [S0, S1] };
                    let (a, b) = if swap { (b, a) } else { (a, b) };
                    for context in 0..8 {
                        let mut insts = vec![MachInst::new(
                            AArch64Opcode::Fcmp,
                            vec![MachOperand::PReg(a), MachOperand::PReg(b)],
                        )];
                        // Bare FCMP; varied consumers; ONE's two-CSET/ORR;
                        // integer and FP flag clobbers before a consumer.
                        insts.extend(match context {
                            0 => vec![],
                            1 => vec![fcmp_runtime_cset(10, X0)],
                            2 => vec![fcmp_runtime_cset(4, X0)],
                            3 => vec![fcmp_runtime_cset(8, X0)],
                            4 => vec![fcmp_runtime_cset(1, X0)],
                            5 => vec![
                                fcmp_runtime_cset(4, X0),
                                fcmp_runtime_cset(12, X1),
                                MachInst::new(
                                    AArch64Opcode::OrrRR,
                                    vec![
                                        MachOperand::PReg(X0),
                                        MachOperand::PReg(X0),
                                        MachOperand::PReg(X1),
                                    ],
                                ),
                            ],
                            6 => vec![
                                MachInst::new(
                                    AArch64Opcode::CmpRI,
                                    vec![MachOperand::PReg(W0), MachOperand::Imm(0)],
                                ),
                                fcmp_runtime_cset(10, X0),
                            ],
                            7 => vec![
                                MachInst::new(
                                    AArch64Opcode::Fcmp,
                                    vec![MachOperand::PReg(D1), MachOperand::PReg(D0)],
                                ),
                                fcmp_runtime_cset(10, X0),
                            ],
                            _ => unreachable!(),
                        });
                        // The independently stated expectation per row: the
                        // last FCMP/CMP before each CSET is its producer.
                        let mut expected = Vec::new();
                        let mut producer: Option<(&'static str, ProofCategory, u32)> = None;
                        for inst in &insts {
                            match inst.opcode {
                                AArch64Opcode::Fcmp => {
                                    let w = if matches!(inst.operands[0], MachOperand::PReg(p) if p == D1)
                                    {
                                        64
                                    } else {
                                        width
                                    };
                                    producer = Some(("fcmp", FLAG_CONSUMER_CATEGORY, w));
                                    let query = fcmp_packed_query(w).unwrap();
                                    expected.push(Some((
                                        query,
                                        fcmp_runtime_resolved(
                                            &verifier,
                                            query,
                                            FLAG_CONSUMER_CATEGORY,
                                        ),
                                    )));
                                }
                                AArch64Opcode::CmpRI => {
                                    producer = Some(("cmp", ProofCategory::Comparison, 32));
                                    expected.push(None);
                                }
                                AArch64Opcode::CSet => {
                                    let MachOperand::Imm(cc) = inst.operands[1] else {
                                        unreachable!()
                                    };
                                    let (kind, category, w) = producer.expect("producer");
                                    let query = if kind == "fcmp" {
                                        fcmp_cset_query(w, cc as u8).unwrap()
                                    } else {
                                        assert_eq!(cc, 10);
                                        "icmp_sge_i32"
                                    };
                                    expected.push(Some((
                                        query,
                                        fcmp_runtime_resolved(&verifier, query, category),
                                    )));
                                }
                                _ => expected.push(None),
                            }
                        }
                        let func = fcmp_runtime_stamped_function(insts, &lir);
                        for mode in [ProvenanceXCheckMode::Off, ProvenanceXCheckMode::Enforce] {
                            let report = fcmp_runtime_report(&verifier, &func, &lir, mode);
                            reports += 1;
                            for (index, row) in report.instructions.iter().enumerate() {
                                let Some((query, want)) = &expected[index] else {
                                    continue;
                                };
                                rows += 1;
                                // E0.2: the row names exactly its reaching
                                // producer's query (which resolves to `want`,
                                // never a static `Fcmp_*` template), and that
                                // registry theorem found by name is refused,
                                // never credited.
                                let ok = !want.starts_with("Fcmp_")
                                    && matches!(
                                        &row.result,
                                        InstructionVerificationResult::Unverified { reason }
                                            if reason.starts_with(REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT)
                                                && reason.contains(&format!("query `{query}`"))
                                    );
                                if !ok {
                                    wrong += 1;
                                    first_wrong.get_or_insert_with(|| {
                                        format!(
                                            "double={double} {cond:?} swap={swap} \
                                             context={context} {mode:?} row {index}: {:?}, \
                                             want {want}",
                                            row.result
                                        )
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }
        assert_eq!(reports, 128);
        assert_eq!(rows, 272); // 144 FCMP, including clobbers, +128 CSET.
        assert_eq!(
            wrong, 0,
            "{wrong}/{rows} FCMP/CSET rows missed their exact (refused) binding; \
             first={first_wrong:?}"
        );
    }

    #[test]
    fn fcmp_runtime_malformed_operands_cannot_inherit_a_template() {
        use trust_cg_ir::aarch64_regs::{D0, D1, H0, S0, S1, W0, W1};
        use trust_cg_lower::instructions::FloatCC;
        let verifier = FunctionVerifier::with_config(VerificationConfig::with_sample_count(16));
        let (mut checked, mut wrong) = (0, 0);
        for double in [false, true] {
            let lir = fcmp_runtime_lir(double, FloatCC::GreaterThanOrEqual);
            let [a, b] = if double { [D0, D1] } else { [S0, S1] };
            let shapes = [
                vec![],
                vec![MachOperand::PReg(a)],
                vec![
                    MachOperand::PReg(a),
                    MachOperand::PReg(b),
                    MachOperand::Imm(0),
                ],
                vec![MachOperand::PReg(W0), MachOperand::PReg(W1)],
                vec![
                    MachOperand::PReg(a),
                    MachOperand::PReg(if double { S1 } else { D1 }),
                ],
                vec![MachOperand::PReg(SP), MachOperand::PReg(b)],
                vec![MachOperand::PReg(a), MachOperand::Imm(1)],
                vec![MachOperand::PReg(H0), MachOperand::PReg(H0)],
                vec![MachOperand::Imm(0), MachOperand::PReg(b)],
            ];
            for operands in shapes {
                let func = fcmp_runtime_stamped_function(
                    vec![MachInst::new(AArch64Opcode::Fcmp, operands)],
                    &lir,
                );
                for mode in [ProvenanceXCheckMode::Off, ProvenanceXCheckMode::Enforce] {
                    let report = fcmp_runtime_report(&verifier, &func, &lir, mode);
                    let (n, bad) = fcmp_runtime_unbound_row_count(&report);
                    checked += n;
                    wrong += bad;
                }
            }
        }
        assert_eq!(checked, 36);
        assert_eq!(
            wrong, 0,
            "{wrong}/36 malformed FCMP rows inherited a template"
        );
    }

    #[test]
    fn fcmp_runtime_standalone_cset_all_conditions_and_malformed_forms_are_unbound() {
        use trust_cg_ir::aarch64_regs::{S0, W0};
        use trust_cg_lower::instructions::FloatCC;
        let verifier = FunctionVerifier::with_config(VerificationConfig::with_sample_count(16));
        let (mut checked, mut wrong) = (0, 0);
        for double in [false, true] {
            let lir = fcmp_runtime_lir(double, FloatCC::GreaterThanOrEqual);
            let dst = if double { X0 } else { W0 };
            let mut instructions = (0..14)
                .map(|cc| fcmp_runtime_cset(cc, dst))
                .collect::<Vec<_>>();
            // Exact CSET alias supports only conditions 0..13. Keep AL/NV,
            // malformed types, and malformed arities in the refusal boundary.
            for operands in [
                vec![],
                vec![MachOperand::PReg(dst)],
                vec![
                    MachOperand::PReg(dst),
                    MachOperand::Imm(0),
                    MachOperand::Imm(0),
                ],
                vec![MachOperand::PReg(S0), MachOperand::Imm(0)],
                vec![MachOperand::PReg(SP), MachOperand::Imm(0)],
                vec![MachOperand::PReg(dst), MachOperand::Imm(-1)],
                vec![MachOperand::PReg(dst), MachOperand::Imm(14)],
                vec![MachOperand::PReg(dst), MachOperand::Imm(15)],
                vec![MachOperand::PReg(dst), MachOperand::Imm(16)],
                vec![MachOperand::Imm(0), MachOperand::Imm(0)],
                vec![MachOperand::PReg(dst), MachOperand::PReg(W0)],
            ] {
                instructions.push(MachInst::new(AArch64Opcode::CSet, operands));
            }
            assert_eq!(instructions.len(), 25);
            for inst in instructions {
                let func = fcmp_runtime_stamped_function(vec![inst], &lir);
                for mode in [ProvenanceXCheckMode::Off, ProvenanceXCheckMode::Enforce] {
                    let report = fcmp_runtime_report(&verifier, &func, &lir, mode);
                    let (n, bad) = fcmp_runtime_unbound_row_count(&report);
                    checked += n;
                    wrong += bad;
                }
            }
        }
        assert_eq!(checked, 100); // 56 valid alias forms +44 malformed forms.
        assert_eq!(
            wrong, 0,
            "{wrong}/100 standalone CSET rows inherited a template"
        );
    }

    #[test]
    fn fcmp_runtime_direct_queries_name_only_the_exact_forms_and_credit_neither() {
        use crate::aarch64_flag_consumer_proofs::FLAG_CONSUMER_CATEGORY;
        use trust_cg_ir::aarch64_regs::{S0, S1};
        let verifier = FunctionVerifier::with_config(VerificationConfig::with_sample_count(16));
        let func = make_func_with_insts(vec![
            MachInst::new(
                AArch64Opcode::Fcmp,
                vec![MachOperand::PReg(S0), MachOperand::PReg(S1)],
            ),
            fcmp_runtime_cset(10, X0),
        ]);
        let (fcmp, cset) = (&func.insts[0], &func.insts[1]);
        for inst in [fcmp, cset] {
            assert!(opcode_to_source_op(inst.opcode).is_none());
            assert!(reconstruct_alu_obligation(inst).is_none());
            // The opcode alone never selects a theorem.
            assert!(FunctionVerifier::opcode_to_proof_query(inst.opcode).is_none());
        }
        let packed = Some(("a64 nzcv fcmp f32 packed:", FLAG_CONSUMER_CATEGORY));
        let consumer = Some(("a64 nzcv fcmp f32 -> cset ge:", FLAG_CONSUMER_CATEGORY));
        // FCMP binds without context; CSET only through its reaching producer.
        assert_eq!(FunctionVerifier::inst_to_proof_query(fcmp), packed);
        assert_eq!(FunctionVerifier::inst_to_proof_query(cset), None);
        let block = &func.blocks[0].insts;
        assert_eq!(
            FunctionVerifier::inst_to_proof_query_in_block(&func, block, 0, fcmp),
            packed
        );
        assert_eq!(
            FunctionVerifier::inst_to_proof_query_in_block(&func, block, 1, cset),
            consumer
        );
        // The prewarm selector enumerates reconstruction obligations only
        // (registry theorems are never warmed since registry credit was
        // withdrawn, E0.2), and neither instruction reconstructs.
        assert!(
            verifier
                .reconstructed_obligations_for_functions(&[&func])
                .is_empty()
        );
        // The exact form names the refusal; it is never credit.
        let report = verifier.verify(&func);
        assert_eq!(report.instructions.len(), 2);
        for (row, expected) in report.instructions.iter().zip([packed, consumer]) {
            let (query, _) = expected.expect("both rows name their exact form");
            match &row.result {
                InstructionVerificationResult::Unverified { reason } => assert!(
                    reason.starts_with(REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT)
                        && reason.contains(&format!("`{query}`")),
                    "{reason}"
                ),
                other => panic!("{query}: a named form is not credit: {other:?}"),
            }
        }
    }

    #[test]
    fn fcmp_runtime_missing_or_mismatched_source_still_refuses_before_rows() {
        use trust_cg_ir::aarch64_regs::{D0, D1, S0, S1};
        use trust_cg_lower::instructions::FloatCC;
        let verifier = FunctionVerifier::with_config(VerificationConfig::with_sample_count(16));
        let mut checked = 0;
        for double in [false, true] {
            let mut lir = fcmp_runtime_lir(double, FloatCC::GreaterThanOrEqual);
            let [a, b] = if double { [D0, D1] } else { [S0, S1] };
            for inst in [
                MachInst::new(
                    AArch64Opcode::Fcmp,
                    vec![MachOperand::PReg(a), MachOperand::PReg(b)],
                ),
                fcmp_runtime_cset(10, X0),
            ] {
                let func = make_func_with_insts(vec![inst]);
                let missing = verifier.verify_with_lir_source_and_mode(
                    &func,
                    None,
                    ProvenanceXCheckMode::Enforce,
                );
                assert!(matches!(
                    missing.precondition_failure,
                    Some(FunctionVerificationPreconditionFailure::MissingLirSource)
                ));
                assert!(missing.instructions.is_empty());
                lir.name = "wrong_source".into();
                let mismatch = verifier.verify_with_lir_source_and_mode(
                    &func,
                    Some(&lir),
                    ProvenanceXCheckMode::Enforce,
                );
                assert!(matches!(
                    mismatch.precondition_failure,
                    Some(FunctionVerificationPreconditionFailure::LirSourceNameMismatch { .. })
                ));
                assert!(mismatch.instructions.is_empty());
                checked += 2;
            }
        }
        assert_eq!(checked, 8);
    }

    #[test]
    fn fcmp_runtime_consumer_denial_preserves_contextual_producer_queries() {
        use AArch64Opcode::{Adcs, AddsRR, CmpRI, Sbcs, SubsRR, Tst};
        let tst = make_func_with_insts(vec![
            MachInst::new(Tst, vec![MachOperand::PReg(X0), MachOperand::PReg(X1)]),
            fcmp_runtime_cset(1, X0),
            MachInst::new(CmpRI, vec![MachOperand::PReg(X0), MachOperand::Imm(0)]),
        ]);
        assert_eq!(
            FunctionVerifier::tst_nzcv_consumer_query(&tst, &tst.blocks[0].insts, 0),
            Some(("tst w64: ne", ProofCategory::CmpCombine))
        );
        let mut checked = 1;
        for (low, high, cc, query) in [
            (AddsRR, Adcs, 6, "checkedsadd_i128 overflow bit"),
            (AddsRR, Adcs, 2, "checkeduadd_i128 overflow bit"),
            (SubsRR, Sbcs, 6, "checkedssub_i128 overflow bit"),
            (SubsRR, Sbcs, 3, "checkedusub_i128 overflow bit"),
        ] {
            let operands = vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
            ];
            let func = make_func_with_insts(vec![
                MachInst::new(low, operands.clone()),
                MachInst::new(high, operands),
                fcmp_runtime_cset(cc, X0),
            ]);
            assert_eq!(
                FunctionVerifier::checked_i128_carry_chain_high_limb_query(
                    &func,
                    &func.blocks[0].insts,
                    1
                ),
                Some((query, ProofCategory::Arithmetic))
            );
            checked += 1;
        }
        assert_eq!(checked, 5); // Existing producer query selection only, not proof credit.
        assert!(FunctionVerifier::opcode_to_proof_query(CmpRI).is_some());
    }

    /// Adversarial (review of X-OPCODES-P3): a CSET's producer binding is an
    /// exact truth table over the REACHING producer's opcode, width, condition
    /// and adjacency, not a pattern match. An X-width ADDS/SUBS names its i64
    /// idiom only for the idiom's own condition; a W-width or mixed-width
    /// producer, a wrong condition (HS after SUBS is not the unsigned borrow
    /// LO), a non-adjacent or orphan ADCS/SBCS high limb, and an unmodeled or
    /// opaque NZCV writer between a CMP and its consumer all refuse. Dropping the
    /// width, condition, adjacency or opaque-writer check in
    /// `cset_producer_query` / `reaching_flag_producer` turns a `None` below
    /// into a citation of an obligation about DIFFERENT flags.
    #[test]
    fn cset_and_select_producer_bindings_are_exact_and_fail_closed() {
        use crate::aarch64_flag_consumer_proofs::{TransparencyPolicy, select_query};
        use AArch64Opcode::{
            Adcs, AddsRR, CMPXrr, CmpRR, Csel, MOVXrr, Sbcs, SubsRR, TrapBoundsCheck,
        };
        use trust_cg_ir::aarch64_regs::{W0, W1, W2, X2, X3, X4};
        let regs = |r: [trust_cg_ir::PReg; 3]| r.map(MachOperand::PReg).to_vec();
        let pair = |a, b| vec![MachOperand::PReg(a), MachOperand::PReg(b)];
        let x3 = || regs([X0, X1, X2]);
        let w3 = || regs([W0, W1, W2]);
        let cset_query = |insts: Vec<MachInst>| {
            let func = make_func_with_insts(insts);
            let block = func.blocks[0].insts.clone();
            FunctionVerifier::cset_producer_query(
                &func,
                &block,
                block.len() - 1,
                TransparencyPolicy::TargetFlagModel,
            )
        };
        let arithmetic = |query: &'static str| Some((query, ProofCategory::Arithmetic));
        let mut refused = 0;
        for (producer, cc, want) in [
            (AddsRR, 6, arithmetic("checkedsadd_i64")),
            (AddsRR, 2, arithmetic("checkeduadd_i64")),
            (SubsRR, 6, arithmetic("checkedssub_i64")),
            (SubsRR, 3, arithmetic("checkedusub_i64")),
            (AddsRR, 3, None),
            (SubsRR, 2, None),
            (AddsRR, 7, None),
            (SubsRR, 0, None),
            (AddsRR, 11, None),
        ] {
            let bound = cset_query(vec![
                MachInst::new(producer, x3()),
                fcmp_runtime_cset(cc, X0),
            ]);
            assert_eq!(bound, want, "{producer:?} cc={cc}");
            refused += usize::from(want.is_none());
            // A W-width or mixed-width producer never names the i64 idiom.
            for operands in [w3(), regs([X0, W1, X2])] {
                assert_eq!(
                    cset_query(vec![
                        MachInst::new(producer, operands.clone()),
                        fcmp_runtime_cset(cc, X0)
                    ]),
                    None,
                    "{producer:?} {operands:?} cc={cc}"
                );
                refused += 1;
            }
        }
        for (low, high, cc, query) in [
            (AddsRR, Adcs, 6, "checkedsadd_i128 overflow bit"),
            (SubsRR, Sbcs, 3, "checkedusub_i128 overflow bit"),
        ] {
            assert_eq!(
                cset_query(vec![
                    MachInst::new(low, x3()),
                    MachInst::new(high, x3()),
                    fcmp_runtime_cset(cc, X0),
                ]),
                arithmetic(query)
            );
            // The high limb must be adjacent to the CSET and follow its own
            // low limb; a flag-transparent move in between or an orphan high
            // limb refuses.
            assert_eq!(
                cset_query(vec![
                    MachInst::new(low, x3()),
                    MachInst::new(high, x3()),
                    MachInst::new(MOVXrr, pair(X3, X4)),
                    fcmp_runtime_cset(cc, X0),
                ]),
                None
            );
            assert_eq!(
                cset_query(vec![MachInst::new(high, x3()), fcmp_runtime_cset(cc, X0)]),
                None
            );
            refused += 2;
        }
        // A CMP binds CSET and CSEL only while nothing that may write NZCV
        // sits in between: an unmodeled flag writer (W-width ADDS, the legacy
        // CMPXrr spelling) is the reaching producer and refuses, and an opaque
        // pseudo (a bounds-check trap that expands into its own CMP) refuses.
        let cmp = || MachInst::new(CmpRR, pair(X0, X1));
        let select = || {
            MachInst::new(
                Csel,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                    MachOperand::PReg(X2),
                    MachOperand::Imm(0),
                ],
            )
        };
        let select_bound = |insts: Vec<MachInst>| {
            let func = make_func_with_insts(insts);
            let block = func.blocks[0].insts.clone();
            select_query(&func, &block, block.len() - 1)
        };
        // (Built through a helper so the walk-query golden, which scans this
        // file for literal `Some((query, category))` pairs, is unaffected.)
        let comparison = |query: &'static str| Some((query, ProofCategory::Comparison));
        assert_eq!(
            cset_query(vec![cmp(), fcmp_runtime_cset(0, X0)]),
            comparison("icmp_eq_i64")
        );
        assert!(select_bound(vec![cmp(), select()]).is_some());
        for between in [
            MachInst::new(AddsRR, w3()),
            MachInst::new(CMPXrr, pair(X3, X4)),
            MachInst::new(TrapBoundsCheck, pair(X3, X4)),
        ] {
            let opcode = between.opcode;
            assert_eq!(
                cset_query(vec![cmp(), between.clone(), fcmp_runtime_cset(0, X0)]),
                None,
                "CSET past {opcode:?}"
            );
            assert_eq!(
                select_bound(vec![cmp(), between, select()]),
                None,
                "CSEL past {opcode:?}"
            );
            refused += 2;
        }
        assert_eq!(refused, 5 + 9 * 2 + 2 * 2 + 3 * 2);
    }

    fn fcsel_runtime_lir(double: bool) -> trust_cg_lower::Function {
        use trust_cg_lower::function::{BasicBlock, Signature as LirSignature};
        use trust_cg_lower::instructions::{Block, Instruction, IntCC, Opcode, Value};
        use trust_cg_lower::types::Type as LirType;
        let fp = if double { LirType::F64 } else { LirType::F32 };
        let mut lir = trust_cg_lower::Function::new(
            "test_func",
            LirSignature {
                params: vec![LirType::I32, fp.clone(), fp.clone()],
                returns: vec![fp.clone()],
            },
        );
        lir.block_order.push(Block(0));
        lir.blocks.insert(
            Block(0),
            BasicBlock {
                params: vec![
                    (Value(0), LirType::I32),
                    (Value(1), fp.clone()),
                    (Value(2), fp),
                ],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Select {
                            cond: IntCC::NotEqual,
                        },
                        args: vec![Value(0), Value(1), Value(2)],
                        results: vec![Value(3)],
                    },
                    Instruction {
                        opcode: Opcode::Return,
                        args: vec![Value(3)],
                        results: vec![],
                    },
                ],
                source_locs: vec![],
            },
        );
        lir
    }

    fn fcsel_runtime_inst(double: bool, cc: i64, swap: bool) -> MachInst {
        use trust_cg_ir::aarch64_regs::{D0, D1, D2, S0, S1, S2};
        let [dst, a, b] = if double { [D0, D1, D2] } else { [S0, S1, S2] };
        let (a, b) = if swap { (b, a) } else { (a, b) };
        inst_with_operands(
            AArch64Opcode::FcselRR,
            vec![
                MachOperand::PReg(dst),
                MachOperand::PReg(a),
                MachOperand::PReg(b),
                MachOperand::Imm(cc),
            ],
        )
    }

    #[test]
    fn fcsel_runtime_queries_require_correspondence_not_a_template_name() {
        let mut wrongly_mapped = Vec::new();
        let mut checked = 0;
        for double in [false, true] {
            for cc in 0..16 {
                for swap in [false, true] {
                    let instruction = fcsel_runtime_inst(double, cc, swap);
                    assert!(reconstruct_alu_obligation(&instruction).is_none());
                    if let Some(query) = FunctionVerifier::inst_to_proof_query(&instruction) {
                        wrongly_mapped.push((double, cc, swap, query));
                    }
                    checked += 1;
                }
            }
        }
        assert_eq!(checked, 64);
        assert!(
            wrongly_mapped.is_empty(),
            "opcode-only FCSEL queries: {wrongly_mapped:?}"
        );
        assert_eq!(
            FunctionVerifier::opcode_to_proof_query(AArch64Opcode::FcselRR),
            None
        );
    }

    #[test]
    fn fcsel_runtime_actual_verifier_refuses_even_with_matching_source_and_cmp() {
        use trust_cg_ir::aarch64_regs::{W0, W1};
        use trust_cg_ir::provenance::{LoweringProvenance, SourceInstId};
        use trust_cg_lower::instructions::Block;
        // Small evaluator configuration bounds this REGRESSION test's legacy
        // before-fix path. Refusal must come from missing applicability, never
        // from AY failing to prove the unrelated static template.
        let verifier = FunctionVerifier::with_config(VerificationConfig::with_sample_count(16));
        let (mut checked, mut wrongly_credited) = (0, 0);
        let mut first_wrong = None;
        for double in [false, true] {
            let lir = fcsel_runtime_lir(double);
            let digest = lir.blocks[&Block(0)].instructions[0].lowering_digest();
            for cc in 0..16 {
                for swap in [false, true] {
                    for producer in 0..5 {
                        // Absent flags; exact CMP Wsel,#0; wrong X selector
                        // width; wrong nonzero immediate; intervening clobber.
                        let mut insts = Vec::new();
                        if producer != 0 {
                            insts.push(inst_with_operands(
                                AArch64Opcode::CmpRI,
                                vec![
                                    MachOperand::PReg(if producer == 2 { X0 } else { W0 }),
                                    MachOperand::Imm(if producer == 3 { 1 } else { 0 }),
                                ],
                            ));
                        }
                        if producer == 4 {
                            insts.push(inst_with_operands(
                                AArch64Opcode::CmpRI,
                                vec![MachOperand::PReg(W1), MachOperand::Imm(0)],
                            ));
                        }
                        let fcsel_index = insts.len();
                        insts.push(fcsel_runtime_inst(double, cc, swap));
                        let mut func = make_func_with_insts(insts);
                        for index in 0..func.insts.len() {
                            func.set_inst_lowering_provenance(
                                InstId(index as u32),
                                LoweringProvenance::SourceInst {
                                    id: SourceInstId { block: 0, index: 0 },
                                    digest,
                                    trust_ir_inst: None,
                                },
                            );
                        }
                        for mode in [ProvenanceXCheckMode::Off, ProvenanceXCheckMode::Enforce] {
                            let report =
                                verifier.verify_with_lir_source_and_mode(&func, Some(&lir), mode);
                            assert!(report.precondition_failure.is_none());
                            assert!(
                                !tv2_provenance_failure(&report),
                                "this is NOT a TV-2 mismatch test"
                            );
                            let row = &report.instructions[fcsel_index];
                            if !matches!(
                                row.result,
                                InstructionVerificationResult::Unverified { .. }
                            ) {
                                wrongly_credited += 1;
                                first_wrong.get_or_insert_with(|| format!(
                                    "double={double} cc={cc} swap={swap} producer={producer} mode={mode:?}: {:?}", row.result));
                            } else {
                                let inventory = report.emitted_opcode_inventory();
                                assert_eq!(
                                    inventory.entries[fcsel_index].status,
                                    OpcodeInventoryStatus::Unverified
                                );
                                assert!(!inventory.is_promotable());
                            }
                            checked += 1;
                        }
                    }
                }
            }
        }
        assert_eq!(checked, 640);
        assert_eq!(
            wrongly_credited, 0,
            "{wrongly_credited}/640 received unrelated credit; first={first_wrong:?}"
        );
    }

    #[test]
    fn fcsel_runtime_malformed_shapes_cannot_borrow_registry_credit() {
        use trust_cg_ir::aarch64_regs::{D0, S0, W0};
        let verifier = FunctionVerifier::with_config(VerificationConfig::with_sample_count(16));
        let (mut checked, mut wrongly_credited) = (0, 0);
        for double in [false, true] {
            let valid = fcsel_runtime_inst(double, 1, false).operands;
            let mut shapes = vec![Vec::new(), valid[..3].to_vec()];
            let mut extra = valid.clone();
            extra.push(MachOperand::Imm(0));
            shapes.push(extra);
            for (index, replacement) in [
                (0, MachOperand::PReg(W0)),
                (1, MachOperand::PReg(if double { S0 } else { D0 })),
                (2, MachOperand::PReg(SP)),
                (3, MachOperand::Imm(-1)),
                (3, MachOperand::Imm(16)),
                (3, MachOperand::PReg(X0)),
            ] {
                let mut malformed = valid.clone();
                malformed[index] = replacement;
                shapes.push(malformed);
            }
            for operands in shapes {
                let instruction = inst_with_operands(AArch64Opcode::FcselRR, operands);
                let has_query = FunctionVerifier::inst_to_proof_query(&instruction).is_some();
                let func = make_func_with_insts(vec![instruction]);
                let report = verifier.verify_with_lir_source_and_mode(
                    &func,
                    None,
                    ProvenanceXCheckMode::Off,
                );
                assert_eq!(report.instructions.len(), 1);
                if has_query
                    || !matches!(
                        report.instructions[0].result,
                        InstructionVerificationResult::Unverified { .. }
                    )
                {
                    wrongly_credited += 1;
                } else {
                    assert!(!report.emitted_opcode_inventory().is_promotable());
                }
                checked += 1;
            }
        }
        assert_eq!(checked, 18);
        assert_eq!(
            wrongly_credited, 0,
            "malformed FCSEL inherited unrelated registry evidence"
        );
    }

    #[test]
    fn conditional_select_malformed_shapes_do_not_borrow_structural_credit() {
        use trust_cg_ir::aarch64_regs::{D0, W0, X2};

        let verifier = FunctionVerifier::new();
        let mut checked = 0;
        for opcode in [
            AArch64Opcode::Csel,
            AArch64Opcode::Csinc,
            AArch64Opcode::Csneg,
        ] {
            let valid = vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
                MachOperand::Imm(0),
            ];
            let mut shapes = vec![Vec::new(), valid[..3].to_vec()];
            let mut extra = valid.clone();
            extra.push(MachOperand::Imm(0));
            shapes.push(extra);
            for (index, replacement) in [
                (0, MachOperand::PReg(W0)),
                (1, MachOperand::PReg(D0)),
                (2, MachOperand::PReg(SP)),
                (3, MachOperand::Imm(-1)),
                (3, MachOperand::Imm(16)),
                (3, MachOperand::PReg(X0)),
            ] {
                let mut malformed = valid.clone();
                malformed[index] = replacement;
                shapes.push(malformed);
            }
            for operands in shapes {
                let func = make_func_with_insts(vec![inst_with_operands(opcode, operands)]);
                let report = verifier.verify_with_lir_source_and_mode(
                    &func,
                    None,
                    ProvenanceXCheckMode::Off,
                );
                assert_eq!(report.instructions.len(), 1);
                assert_eq!(report.unverified_count(), 1);
                let inventory = report.emitted_opcode_inventory();
                assert_eq!(
                    inventory.entries[0].status,
                    OpcodeInventoryStatus::Unverified
                );
                assert!(!inventory.is_promotable(), "malformed {opcode:?}");
                checked += 1;
            }
        }
        assert_eq!(checked, 27);
    }

    #[test]
    fn conditional_select_unverified_row_blocks_mixed_report_promotion() {
        // Synthetic transport-only control: the anchor is NOT a discharged
        // theorem and earns no compiler-proof evidence. It isolates inventory
        // accounting when an otherwise credited function also has a proof gap.
        let anchor = InstructionReport {
            inst_index: 0,
            opcode: InstructionOpcode::AArch64(AArch64Opcode::Movn),
            result: InstructionVerificationResult::Verified {
                proof_name: "synthetic transport-only exhaustive anchor".to_string(),
                category: ProofCategory::ConstantMaterialization,
                strength: VerificationStrength::Exhaustive,
                degenerate: false,
            },
        };
        for opcode in [
            AArch64Opcode::Csel,
            AArch64Opcode::Csinc,
            AArch64Opcode::Csneg,
        ] {
            let mut report = FunctionVerificationReport {
                function_name: "synthetic_transport_only".to_string(),
                precondition_failure: None,
                instructions: vec![anchor.clone()],
            };
            assert!(report.emitted_opcode_inventory().is_promotable());
            report.instructions.push(InstructionReport {
                inst_index: 1,
                opcode: InstructionOpcode::AArch64(opcode),
                result: InstructionVerificationResult::Unverified {
                    reason: "no validated conditional-select instruction binding".to_string(),
                },
            });
            assert_eq!(report.genuinely_verified_count(), 1);
            assert_eq!(report.failed_count(), 0);
            assert_eq!(report.sampled_uncredited_count(), 0);
            assert_eq!(report.registry_name_lookup_count(), 0);
            assert!(!report.all_verified());
            let inventory = report.emitted_opcode_inventory();
            assert_eq!(
                inventory.entries[1].status,
                OpcodeInventoryStatus::Unverified
            );
            assert!(!inventory.is_promotable());
            assert!(inventory.promotion_rejection_reason().is_some());
        }
    }

    #[test]
    fn csinv_still_blocks_promotion() {
        // NARROWNESS: CSINV has NO proof at all (a genuine value gap the gate
        // deliberately keeps blocking) — crediting the compare-and-branches must
        // NOT leak to it.
        assert!(
            !is_covered_elsewhere_indirect_branch(InstructionOpcode::AArch64(AArch64Opcode::Csinv)),
            "Csinv must NOT be covered-elsewhere"
        );
        assert!(FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Csinv).is_none());
        let func = make_func_with_insts(vec![inst(AArch64Opcode::Csinv), inst(AArch64Opcode::Ret)]);
        assert!(
            !verify_function(&func)
                .emitted_opcode_inventory()
                .is_promotable(),
            "Csinv must keep blocking per-compile promotion (fail-closed)"
        );
    }

    #[test]
    fn neon_lane_select_permutes_name_per_lane_theorems_but_do_not_promote() {
        // NeonDupElem and NeonInsGen carry per-(arrangement, LANE) registry
        // obligations whose wrong-LANE negative controls refute. Before E0.2
        // their query credited the instruction; a named theorem is not a proof
        // about this instruction's lane operand, so they block promotion again.
        for op in [AArch64Opcode::NeonDupElem, AArch64Opcode::NeonInsGen] {
            let (query, _) = FunctionVerifier::opcode_to_proof_query(op)
                .unwrap_or_else(|| panic!("{op:?} must still name its per-lane theorem family"));
            let func = make_func_with_insts(vec![inst(op), inst(AArch64Opcode::Ret)]);
            let report = verify_function(&func);
            assert_registry_withdrawn(&report.instructions[0].result, query);
            assert!(!report.emitted_opcode_inventory().is_promotable(), "{op:?}");
        }
    }

    #[test]
    fn neon_rbitv_and_unbound_pair_memory_do_not_promote() {
        // NeonRbitV names the RBIT.16B registry theorem (reported, not credited
        // since E0.2); the surrounding Q-pair loads/stores have no mapping.
        let (query, _) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::NeonRbitV)
            .expect("NeonRbitV must still name the RBIT.16B theorem");
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::NeonLdpQPost),
            inst(AArch64Opcode::NeonRbitV),
            inst(AArch64Opcode::NeonStpQPost),
            inst(AArch64Opcode::Ret),
        ]);
        let report = verify_function(&func);
        assert_registry_withdrawn(&report.instructions[1].result, query);
        let inventory = report.emitted_opcode_inventory();
        assert!(
            !inventory.is_promotable(),
            "bit-reverse function must not promote; rejection: {:?}",
            inventory.promotion_rejection_reason()
        );
        for position in [0, 1, 2] {
            assert_eq!(
                inventory.entries[position].status,
                OpcodeInventoryStatus::Unverified
            );
        }
        assert!(inventory.entries[3].status.is_promotable());
    }

    #[test]
    fn neon_dup_gen_broadcast_is_not_promotable_on_registry_identity() {
        // NeonDupGen used to promote via the disclosed `NeonEncoding: DUP
        // broadcast` identity found by name. E0.2: named, not credited.
        let (query, _) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::NeonDupGen)
            .expect("NeonDupGen must still name its registry identity");
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::NeonDupGen),
            inst(AArch64Opcode::Ret),
        ]);
        let report = verify_function(&func);
        assert_registry_withdrawn(&report.instructions[0].result, query);
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }

    /// L04-P11: register copies are no longer covered-elsewhere. Each concrete
    /// MOV / typed MOVWrr/MOVXrr / FMOV copy names its decoded-word form's
    /// registered obligation (the obligation the coverage gate credits the
    /// opcode by). Since E0.2 that theorem, found by name, is refused rather
    /// than credited, so no copy promotes today; every shape outside the forms stays
    /// Unverified, names its exact shape in its reason, and blocks promotion
    /// instead of inheriting opcode-wide credit. The zero-source copies and the
    /// W<->H FMOVs the lowering emits (a zero-sized aggregate argument's
    /// `MOVXrr Xn, XZR`; the f16 select, bitcast and constant FMOVs) bind
    /// their own forms.
    #[test]
    fn register_copies_name_their_decoded_word_forms_and_refuse_other_shapes() {
        use crate::aarch64_value_decode_proofs::A64ValueForm as F;
        use AArch64Opcode::{FmovFprFpr, FmovFprGpr, FmovGprFpr, MOVWrr, MOVXrr, MovR};
        use trust_cg_ir::RegClass;
        use trust_cg_ir::aarch64_regs::{W0, W1, WZR, XZR};
        use trust_cg_ir::regs::{PReg, SpecialReg, VReg};
        let p = MachOperand::PReg;
        let special = MachOperand::Special;
        let fpr = |base: u16, n: u16| MachOperand::PReg(PReg::new(base + n));
        let (d, s, h) = (|n| fpr(96, n), |n| fpr(128, n), |n| fpr(165, n));
        let vreg = |id, class| MachOperand::VReg(VReg::new(id, class));

        let mut bound = 0;
        let mut derived = 0;
        for (opcode, operands, form) in [
            (MovR, vec![p(X0), p(X1)], F::MovX),
            (MovR, vec![p(W0), p(W1)], F::MovW),
            (MovR, vec![p(X0), special(SpecialReg::SP)], F::MovXFromSp),
            (
                MovR,
                vec![vreg(0, RegClass::Gpr64), vreg(1, RegClass::Gpr64)],
                F::MovX,
            ),
            (MOVWrr, vec![p(W0), p(W1)], F::MovWrr),
            // The allocator's view does not change the typed opcode's width.
            (MOVWrr, vec![p(X0), p(X1)], F::MovWrr),
            (MOVXrr, vec![p(X0), p(X1)], F::MovXrr),
            (MOVXrr, vec![p(W0), p(W1)], F::MovXrr),
            (FmovFprFpr, vec![s(0), s(1)], F::FmovS),
            (FmovFprFpr, vec![d(0), d(1)], F::FmovD),
            (FmovFprGpr, vec![p(W0), s(1)], F::FmovWFromS),
            (FmovFprGpr, vec![p(X0), d(1)], F::FmovXFromD),
            (FmovGprFpr, vec![s(0), p(W1)], F::FmovSFromW),
            (FmovGprFpr, vec![d(0), p(X1)], F::FmovDFromX),
            // Zero-register sources, in both spellings of the zero register.
            (MovR, vec![p(X0), special(SpecialReg::XZR)], F::MovXFromZr),
            (MovR, vec![p(W0), p(WZR)], F::MovWFromZr),
            (MOVXrr, vec![p(X0), p(XZR)], F::MovXrrFromZr),
            (
                MOVXrr,
                vec![p(W0), special(SpecialReg::WZR)],
                F::MovXrrFromZr,
            ),
            (MOVWrr, vec![p(W0), p(WZR)], F::MovWrrFromZr),
            (MOVWrr, vec![p(X0), p(XZR)], F::MovWrrFromZr),
            // FEAT_FP16 transfers between W and H.
            (FmovFprGpr, vec![p(W0), h(1)], F::FmovWFromH),
            (FmovGprFpr, vec![h(0), p(W1)], F::FmovHFromW),
            (
                FmovGprFpr,
                vec![vreg(0, RegClass::Fpr16), vreg(1, RegClass::Gpr32)],
                F::FmovHFromW,
            ),
        ] {
            assert!(!is_covered_elsewhere_indirect_branch(
                InstructionOpcode::AArch64(opcode)
            ));
            let copy = inst_with_operands(opcode, operands);
            assert_eq!(
                FunctionVerifier::inst_to_proof_query(&copy),
                Some((form.query(), form.category())),
                "{copy:?} must bind exactly {form:?}"
            );
            // E0.2: the form's registry theorem is found by name, so it is
            // never credited. L07-P2: a GPR copy between hardware registers is
            // judged by its instruction-derived obligation instead; the FMOVs
            // and virtual-register copies still name exactly their form.
            let report = verify_function(&make_func_with_insts(vec![copy.clone()]));
            if crate::aarch64_instruction_word_proofs::instruction_word(&copy).is_some() {
                assert_instruction_derived(&report.instructions[0].result);
                derived += 1;
            } else {
                assert_registry_withdrawn(&report.instructions[0].result, form.query());
            }
            let inventory = report.emitted_opcode_inventory();
            assert_eq!(
                inventory.entries[0].status,
                OpcodeInventoryStatus::Unverified
            );
            assert!(!inventory.is_promotable(), "{copy:?}");
            bound += 1;
        }
        assert_eq!(bound, 23);
        assert_eq!(derived, 13);

        // L07-P2: the GPR copies to SP or ZR, and from SP at W width, are
        // outside the decoded-value forms but are admitted instruction-word
        // shapes (`ADD Rd, Rn, #0` or `ORR Rd, ZR, Rm`).
        for (opcode, operands) in [
            (MovR, vec![special(SpecialReg::SP), p(X1)]),
            (MovR, vec![special(SpecialReg::XZR), p(X1)]),
            (MOVXrr, vec![special(SpecialReg::SP), p(X1)]),
            (MOVXrr, vec![p(XZR), p(X1)]),
            (MOVWrr, vec![p(W0), special(SpecialReg::SP)]),
        ] {
            let copy = inst_with_operands(opcode, operands);
            assert_eq!(
                FunctionVerifier::inst_to_proof_query(&copy),
                None,
                "{copy:?}"
            );
            let report = verify_function(&make_func_with_insts(vec![copy.clone()]));
            assert_instruction_derived(&report.instructions[0].result);
            assert!(
                !report.emitted_opcode_inventory().is_promotable(),
                "{copy:?}"
            );
        }

        let mut refused = 0;
        for (opcode, operands) in [
            // Operand-less and malformed copies.
            (MovR, vec![]),
            (MOVXrr, vec![p(X0)]),
            // Half-precision register moves, X<->H and cross-width FMOVs, and
            // FMOVs naming the zero register (none is emitted) are outside.
            (FmovFprFpr, vec![h(0), h(1)]),
            (FmovFprFpr, vec![s(0), d(1)]),
            (FmovFprGpr, vec![p(X0), h(1)]),
            (FmovGprFpr, vec![h(0), p(X1)]),
            (FmovFprGpr, vec![p(X0), s(1)]),
            (FmovGprFpr, vec![d(0), p(W1)]),
            (FmovGprFpr, vec![d(0), p(XZR)]),
            (FmovFprGpr, vec![p(XZR), d(1)]),
            // A GPR copy spelled on FP registers, and the reverse.
            (MovR, vec![d(0), d(1)]),
            (FmovFprFpr, vec![p(X0), p(X1)]),
        ] {
            let copy = inst_with_operands(opcode, operands);
            assert_eq!(
                FunctionVerifier::inst_to_proof_query(&copy),
                None,
                "{copy:?} must not bind any form"
            );
            let report = verify_function(&make_func_with_insts(vec![copy.clone()]));
            match &report.instructions[0].result {
                InstructionVerificationResult::Unverified { reason } => assert!(
                    reason.starts_with(&format!("no decoded-value form binds {opcode:?} ")),
                    "{copy:?} must be refused by its shape, not generically: {reason}"
                ),
                other => panic!("{copy:?} must stay Unverified: {other:?}"),
            }
            let inventory = report.emitted_opcode_inventory();
            assert_eq!(
                inventory.entries[0].status,
                OpcodeInventoryStatus::Unverified,
                "{copy:?} must stay Unverified, never covered-elsewhere"
            );
            assert!(!inventory.is_promotable(), "{copy:?}");
            refused += 1;
        }
        assert_eq!(refused, 12);
        // The refusal names the exact shape.
        let to_sp = inst_with_operands(MOVXrr, vec![special(SpecialReg::SP), p(X1)]);
        assert_eq!(
            crate::aarch64_value_decode_proofs::a64_value_unbound_reason(&to_sp).as_deref(),
            Some(
                "no decoded-value form binds MOVXrr SP <- X1: ENC-5 still decides its word, \
                 but no registered obligation covers this shape"
            )
        );

        // CONTROL: an unrelated genuinely-uncovered opcode (CSINV — no proof, NOT
        // covered-elsewhere) stays Unverified and BLOCKS promotion.
        let csinv = make_func_with_insts(vec![inst(AArch64Opcode::Csinv)]);
        let csinv_inv = verify_function(&csinv).emitted_opcode_inventory();
        assert_eq!(
            csinv_inv.entries[0].status,
            OpcodeInventoryStatus::Unverified,
            "CSINV control must stay Unverified (genuine gap, not covered-elsewhere)"
        );
        assert!(
            !csinv_inv.is_promotable(),
            "CSINV control must keep blocking promotion"
        );
    }

    #[test]
    fn common_aarch64_function_shape_is_not_promotable_without_operand_exact_evidence() {
        // E0.2 CAPSTONE INVERSE: this common shape (integer ALU, frame
        // load/store, ADRP+ADD, BL, conditional + unconditional branches, RET)
        // used to promote entirely on registry theorems found by opcode query.
        // None of those theorems is about these operand-less instructions, so
        // every non-RET row is an uncredited registry candidate.
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::AddRR),
            inst(AArch64Opcode::LdrRI),
            inst(AArch64Opcode::StrRI),
            inst(AArch64Opcode::Adrp),
            inst(AArch64Opcode::AddPCRel),
            inst(AArch64Opcode::Bl),
            inst(AArch64Opcode::BCond),
            inst(AArch64Opcode::B),
            inst(AArch64Opcode::Ret),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.registry_name_lookup_count(), 8);
        let inventory = report.emitted_opcode_inventory();
        assert!(!inventory.is_promotable());
        assert_eq!(inventory.uncovered_non_pseudo_opcodes().len(), 8);
        assert!(inventory.entries[8].status.is_promotable());
    }

    #[test]
    fn test_emitted_opcode_inventory_reports_uncovered_aarch64_opcode() {
        // CSINV is emittable and non-pseudo but has NO value-proof mapping
        // (unlike CSEL/CSINC/CSNEG and FABS/FSQRT/FDIV, which are now wired), so
        // it is the canonical "uncovered non-pseudo opcode" shape here.
        let func = make_func_with_insts(vec![inst(AArch64Opcode::Csinv)]);
        let report = verify_function(&func);
        let inventory = report.emitted_opcode_inventory();
        let uncovered = inventory.uncovered_non_pseudo_opcodes();

        assert_eq!(uncovered.len(), 1);
        assert_eq!(
            uncovered[0].opcode,
            InstructionOpcode::AArch64(AArch64Opcode::Csinv)
        );
        assert_eq!(uncovered[0].status, OpcodeInventoryStatus::Unverified);
        let reason = inventory
            .promotion_rejection_reason()
            .expect("uncovered opcode should reject promotion");
        assert!(reason.contains("AArch64::Csinv"), "{reason}");
        assert!(reason.contains("uncovered non-pseudo opcode"), "{reason}");
    }

    // =======================================================================
    // 2-9. Single operand-less instructions: registry candidates, not credit
    // (E0.2). Each still names its theorem family; none is verified.
    // =======================================================================

    #[test]
    fn test_single_add_is_uncredited_registry_candidate() {
        assert_registry_candidate_with_theorem(AArch64Opcode::AddRR, ProofCategory::Arithmetic, "");
    }

    #[test]
    fn test_single_sub_is_uncredited_registry_candidate() {
        assert_registry_candidate_with_theorem(AArch64Opcode::SubRR, ProofCategory::Arithmetic, "");
    }

    #[test]
    fn test_single_mul_is_uncredited_registry_candidate() {
        assert_registry_candidate_with_theorem(AArch64Opcode::MulRR, ProofCategory::Arithmetic, "");
    }

    #[test]
    fn test_single_madd_is_uncredited_registry_candidate() {
        assert_registry_candidate_with_theorem(
            AArch64Opcode::Madd,
            ProofCategory::Arithmetic,
            "AArch64 MADD_RR generic",
        );
    }

    #[test]
    fn test_single_msub_is_uncredited_registry_candidate() {
        assert_registry_candidate_with_theorem(
            AArch64Opcode::Msub,
            ProofCategory::Arithmetic,
            "AArch64 MSUB_RR generic",
        );
    }

    #[test]
    fn test_single_neg_is_uncredited_registry_candidate() {
        assert_registry_candidate_with_theorem(AArch64Opcode::Neg, ProofCategory::Arithmetic, "");
    }

    #[test]
    fn test_sdiv_is_uncredited_registry_candidate() {
        assert_registry_candidate_with_theorem(AArch64Opcode::SDiv, ProofCategory::Division, "");
    }

    #[test]
    fn test_udiv_is_uncredited_registry_candidate() {
        assert_registry_candidate_with_theorem(AArch64Opcode::UDiv, ProofCategory::Division, "");
    }

    // =======================================================================
    // 8-9. Comparison and branch
    // =======================================================================

    #[test]
    fn test_cmp_is_uncredited_registry_candidate() {
        assert_registry_candidate_with_theorem(AArch64Opcode::CmpRR, ProofCategory::Comparison, "");
    }

    #[test]
    fn test_bcond_is_uncredited_registry_candidate() {
        assert_registry_candidate_with_theorem(AArch64Opcode::BCond, ProofCategory::Branch, "");
    }

    // =======================================================================
    // 10-11. Memory: E0.2 inverse tests (substring/representative credit
    // withdrawn). An operand-less LDR/STR used to be credited `Verified`
    // because the query `"load"`/`"store"` returned the first Memory theorem
    // whose name contains it: a pair or byte-roundtrip theorem about another
    // form entirely.
    // =======================================================================

    /// Assert the only candidate evidence was a registry name lookup: the
    /// instruction is `Unverified`, names its query, discharged nothing, and
    /// blocks promotion.
    fn assert_withdrawn_registry_credit(
        opcode: AArch64Opcode,
        expected_query: &str,
        expected_category: ProofCategory,
    ) {
        assert_eq!(
            FunctionVerifier::opcode_to_proof_query(opcode),
            Some((expected_query, expected_category)),
            "{opcode:?}: the retired mapping still names its query (diagnostic only)"
        );
        let report = verify_function(&make_func_with_insts(vec![inst(opcode)]));
        assert_eq!(report.verified_count(), 0, "{opcode:?}: {report:?}");
        assert_eq!(report.registry_name_lookup_count(), 1, "{opcode:?}");
        match &report.instructions[0].result {
            InstructionVerificationResult::Unverified { reason } => {
                assert!(
                    reason.starts_with(REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT),
                    "{opcode:?}: {reason}"
                );
                assert!(
                    reason.contains(&format!("`{expected_query}`")),
                    "{opcode:?}: {reason}"
                );
            }
            other => panic!("{opcode:?}: expected withdrawn registry credit, got {other:?}"),
        }
        let inventory = report.emitted_opcode_inventory();
        assert_eq!(
            inventory.entries[0].status,
            OpcodeInventoryStatus::Unverified
        );
        assert!(!inventory.is_promotable());
    }

    /// The theorem a retired Memory query selects: first registered name
    /// containing it (case-insensitive), exactly as the withdrawn arm did.
    fn memory_query_representative(query: &'static str) -> String {
        FunctionVerifier::new()
            .registry_proof_for_query(query, ProofCategory::Memory)
            .expect("a Memory theorem still matches the retired query")
            .obligation
            .name
            .clone()
    }

    #[test]
    fn operand_less_ldrri_is_not_verified() {
        // What `"load"` used to credit an LDR with: a theorem about two
        // adjacent I32 loads forming an LDP at offset 0, never this LDR.
        assert_eq!(
            memory_query_representative("load"),
            "LDP_QF_ABV_I32_offset0: two adjacent Load_I32 == LDP [Xn, #0]"
        );
        for opcode in [
            AArch64Opcode::LdrRI,
            AArch64Opcode::LdrbRI,
            AArch64Opcode::LdrhRI,
            AArch64Opcode::LdrsbRI,
            AArch64Opcode::LdrshRI,
            AArch64Opcode::LdrRO,
            AArch64Opcode::LdrbRO,
            AArch64Opcode::LdrhRO,
        ] {
            assert_withdrawn_registry_credit(opcode, "load", ProofCategory::Memory);
        }
    }

    #[test]
    fn operand_less_strri_is_not_verified() {
        // What `"store"` used to credit an STR with: a byte store/load
        // roundtrip, never this STR.
        assert_eq!(
            memory_query_representative("store"),
            "Roundtrip_I8: store then load"
        );
        for opcode in [
            AArch64Opcode::StrRI,
            AArch64Opcode::StrbRI,
            AArch64Opcode::StrhRI,
            AArch64Opcode::StrRO,
            AArch64Opcode::StrbRO,
            AArch64Opcode::StrhRO,
        ] {
            assert_withdrawn_registry_credit(opcode, "store", ProofCategory::Memory);
        }
    }

    /// L07-P2: the sign-extending, writeback and register-offset scalar forms
    /// with real operands are judged on the walk by their instruction-derived
    /// obligations (`aarch64_instruction_word_proofs`), never by the retired
    /// `"load"`/`"store"` queries the operand-less forms above still reach.
    /// None is credited and the function does not promote.
    #[test]
    fn scalar_sign_extending_writeback_and_register_offset_rows_are_instruction_derived() {
        let x = |n: u16| MachOperand::PReg(PReg::new(n));
        let w = |n: u16| MachOperand::PReg(PReg::new(32 + n));
        let sp = MachOperand::Special(SpecialReg::SP);
        let rows = [
            (
                AArch64Opcode::LdrsbRI,
                vec![x(1), x(2), MachOperand::Imm(5)],
            ),
            (
                AArch64Opcode::LdrshRI,
                vec![w(3), x(4), MachOperand::Imm(-3)],
            ),
            (
                AArch64Opcode::StrPreIndex,
                vec![x(0), sp.clone(), MachOperand::Imm(-16)],
            ),
            (
                AArch64Opcode::LdrPostIndex,
                vec![x(0), sp.clone(), MachOperand::Imm(16)],
            ),
            (
                AArch64Opcode::LdrRO,
                vec![x(0), x(1), x(2), MachOperand::Imm(7)],
            ),
            (
                AArch64Opcode::StrRO,
                vec![w(3), x(4), w(5), MachOperand::Imm(12)],
            ),
            (AArch64Opcode::LdrbRO, vec![w(6), x(7), x(8)]),
            (AArch64Opcode::LdrswRO, vec![x(9), x(10), x(11)]),
        ];
        let func = make_func_with_insts(
            rows.iter()
                .map(|(opcode, operands)| inst_with_operands(*opcode, operands.clone()))
                .collect(),
        );
        let report = verify_function(&func);
        assert_eq!(report.total(), rows.len());
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.registry_name_lookup_count(), 0);
        assert_eq!(report.instruction_derived_count(), rows.len());
        for row in &report.instructions {
            assert_instruction_derived(&row.result);
        }
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }

    /// E0.2, statistical inverse on AArch64: a real 64-bit ADD reconstructs
    /// from its operands but discharges only by sampling, so it is reported
    /// with its sample count and never verified or promoted.
    #[test]
    fn sampled_64_bit_add_is_reported_not_verified() {
        use trust_cg_ir::aarch64_regs::X2;
        let add = inst_with_operands(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
                MachOperand::PReg(X2),
            ],
        );
        let report = verify_function(&make_func_with_insts(vec![add]));
        assert_eq!(report.verified_count(), 0, "{report:?}");
        assert_eq!(report.sampled_uncredited_count(), 1, "{report:?}");
        match &report.instructions[0].result {
            InstructionVerificationResult::Unverified { reason } => {
                assert!(
                    reason.starts_with(STATISTICAL_EVIDENCE_IS_NOT_CREDIT),
                    "{reason}"
                );
                assert!(reason.contains("RECONSTRUCTED"), "{reason}");
            }
            other => panic!("sampled evidence must not be credited: {other:?}"),
        }
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }

    // =======================================================================
    // 12. Floating-point
    // =======================================================================

    #[test]
    fn test_fadd_is_uncredited_registry_candidate() {
        assert_registry_candidate_with_theorem(
            AArch64Opcode::FaddRR,
            ProofCategory::FloatingPoint,
            "",
        );
    }

    // =======================================================================
    // 13. Pseudo-op skipping
    // =======================================================================

    #[test]
    fn test_pseudo_op_skipped() {
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::Phi),
            inst(AArch64Opcode::Nop),
            inst(AArch64Opcode::Copy),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 3);
        assert_eq!(report.skipped_count(), 3);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.unverified_count(), 0);
        assert!(report.all_verified());
        assert_eq!(report.coverage_percent(), 100.0);
    }

    // =======================================================================
    // 14. Mixed function
    // =======================================================================

    #[test]
    fn test_mixed_function() {
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::AddRR), // registry candidate: unverified (E0.2)
            inst(AArch64Opcode::Phi),   // skipped
            inst(AArch64Opcode::Ret),   // unverified (#62: RET proof retracted)
            inst(AArch64Opcode::SubRR), // registry candidate: unverified (E0.2)
            inst(AArch64Opcode::Nop),   // skipped
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 5);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.skipped_count(), 2);
        assert_eq!(report.unverified_count(), 3);
        assert_eq!(report.registry_name_lookup_count(), 2);
    }

    // =======================================================================
    // 15. 100% coverage
    // =======================================================================

    #[test]
    fn test_coverage_100_percent() {
        // Coverage counts only credited rows: exhaustively discharged 8-bit
        // extension reconstructions reach 100%, registry candidates reach 0%.
        let func = make_func_with_insts(vec![
            representative_reconstructable_inst(AArch64Opcode::Uxtb).unwrap(),
            representative_reconstructable_inst(AArch64Opcode::Sxtb).unwrap(),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 2, "{report:?}");
        assert_eq!(report.coverage_percent(), 100.0);
        assert!(report.all_verified());

        let registry = verify_function(&make_func_with_insts(vec![
            inst(AArch64Opcode::AddRR),
            inst(AArch64Opcode::SubRR),
            inst(AArch64Opcode::MulRR),
        ]));
        assert_eq!(registry.verified_count(), 0);
        assert_eq!(registry.coverage_percent(), 0.0);
        assert!(!registry.all_verified());
    }

    // =======================================================================
    // 16. RET no longer contributes to verified coverage (#62: proof retracted).
    // =======================================================================

    #[test]
    fn test_extension_verified_ret_unverified_after_retraction() {
        let func = make_func_with_insts(vec![
            // verified (exhaustively discharged reconstruction)
            representative_reconstructable_inst(AArch64Opcode::Uxtb).unwrap(),
            inst(AArch64Opcode::Ret), // unverified (#62: RET X==X proof retracted)
        ]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 1);
        assert_eq!(report.unverified_count(), 1);
        assert_eq!(report.coverage_percent(), 50.0);
    }

    // =======================================================================
    // 17. Partial coverage for unmapped branches (RET + Br both unverified now).
    // =======================================================================

    #[test]
    fn test_unmapped_branch_partial_coverage() {
        let func = make_func_with_insts(vec![
            // verified (exhaustively discharged reconstruction)
            representative_reconstructable_inst(AArch64Opcode::Sxtb).unwrap(),
            inst(AArch64Opcode::Br), // unverified (branch target)
        ]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 1);
        assert_eq!(report.unverified_count(), 1);
        assert_eq!(report.coverage_percent(), 50.0);
    }

    // =======================================================================
    // 18. Display formatting
    // =======================================================================

    #[test]
    fn test_report_display() {
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::AddRR),
            inst(AArch64Opcode::Br),
            inst(AArch64Opcode::Phi),
        ]);
        let report = verify_function(&func);
        let text = format!("{}", report);
        assert!(text.contains("Function Verification Report"));
        assert!(text.contains("test_func"));
        assert!(text.contains("Coverage:"));
        assert!(text.contains("verified"));
        assert!(text.contains("Unverified instructions:"));
    }

    // =======================================================================
    // 19. Default trait
    // =======================================================================

    #[test]
    fn test_verifier_default() {
        let verifier = FunctionVerifier::default();
        let func = make_empty_func();
        let report = verifier.verify(&func);
        assert_eq!(report.total(), 0);
        assert!(report.all_verified());
    }

    // =======================================================================
    // 20. Multiple blocks
    // =======================================================================

    #[test]
    fn test_multiple_blocks() {
        let mut func = make_empty_func();

        // Add instructions to block 0
        func.insts
            .push(representative_reconstructable_inst(AArch64Opcode::Uxtb).unwrap());
        func.blocks[0].insts.push(InstId(0));

        // Create block 1
        let mut block1 = trust_cg_ir::MachBlock::new();
        func.insts
            .push(representative_reconstructable_inst(AArch64Opcode::Sxtb).unwrap());
        block1.insts.push(InstId(1));
        func.blocks.push(block1);

        let report = verify_function(&func);
        assert_eq!(report.total(), 2);
        assert_eq!(report.verified_count(), 2);
        assert_eq!(report.coverage_percent(), 100.0);
    }

    // =======================================================================
    // 21. All pseudo-ops = 100% coverage (vacuous)
    // =======================================================================

    #[test]
    fn test_all_pseudo_ops_skipped() {
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::Phi),
            inst(AArch64Opcode::Nop),
            inst(AArch64Opcode::Copy),
            inst(AArch64Opcode::StackAlloc),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 4);
        assert_eq!(report.skipped_count(), 4);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.coverage_percent(), 100.0);
        assert!(report.all_verified());
    }

    // =======================================================================
    // 22. Logical ops verified
    // =======================================================================

    #[test]
    fn test_and_or_eor_name_bitwise_theorems_but_are_uncredited() {
        // Logical ops name the GENERAL bitwise theorems (BitwiseShift), NOT
        // degenerate Peephole rewrite identities; E0.2: named, not credited.
        for opcode in [
            AArch64Opcode::AndRR,
            AArch64Opcode::OrrRR,
            AArch64Opcode::EorRR,
        ] {
            assert_registry_candidate_with_theorem(opcode, ProofCategory::BitwiseShift, "");
        }
    }

    // =======================================================================
    // 23. Shift ops verified
    // =======================================================================

    #[test]
    fn test_shift_ops_reconstruct_but_sampling_is_uncredited() {
        // #62: the static degenerate Ishl/Ushr/Sshr -> SHL/LSL/LSR/ASR proofs were
        // RETRACTED. Shift opcodes route through OPERAND RECONSTRUCTION (the
        // machine side is rebuilt from the REAL opcode+operands with the faithful
        // hardware-amount-masked encoder under the #57 amount<width precondition).
        // E0.2: these register-width instances discharge only by sampling, which
        // is reported and never credited.
        let func = make_func_with_insts(vec![
            representative_reconstructable_inst(AArch64Opcode::LslRR).unwrap(),
            representative_reconstructable_inst(AArch64Opcode::LsrRR).unwrap(),
            representative_reconstructable_inst(AArch64Opcode::AsrRR).unwrap(),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.sampled_uncredited_count(), 3);
        for ir in &report.instructions {
            assert_sampled_uncredited(&ir.result, "");
        }
    }

    // =======================================================================
    // 24. RET: degenerate "RET branches to LR" proof RETRACTED (#62) — now
    //     Unverified (no value-proof), FailClosedAllowlisted in the coverage gate.
    // =======================================================================

    #[test]
    fn test_ret_unverified_after_proof_retraction() {
        assert_unverified_no_proof(AArch64Opcode::Ret);
    }

    // =======================================================================
    // 25. Copy-lowered moves: degenerate "COPY(x)==x" proof RETRACTED (#62)
    //     — now Unverified (no value-proof), FailClosedAllowlisted in the gate.
    // =======================================================================

    #[test]
    fn test_movr_unverified_after_copy_proof_retraction() {
        assert_unverified_no_proof(AArch64Opcode::MovR);
    }

    #[test]
    fn test_fmov_fpr_fpr_unverified_after_copy_proof_retraction() {
        assert_unverified_no_proof(AArch64Opcode::FmovFprFpr);
    }

    #[test]
    fn test_fmov_cross_class_bitcasts_unverified_no_proof() {
        // FmovFprGpr / FmovGprFpr (the f64::to_bits / from_bits / copysign
        // reinterpret moves) have NO opcode-wide value-proof: the shared
        // single-bitvector-domain identity would be the degenerate X==X. An
        // operand-less instance names no decoded-word form either, so it stays
        // Unverified; a well-formed instance binds its form — see
        // `register_copies_name_their_decoded_word_forms_and_refuse_other_shapes`.
        for opcode in [AArch64Opcode::FmovFprGpr, AArch64Opcode::FmovGprFpr] {
            assert_unverified_no_proof(opcode);
        }
    }

    #[test]
    fn test_typed_mov_aliases_unverified_after_copy_proof_retraction() {
        for opcode in [AArch64Opcode::MOVWrr, AArch64Opcode::MOVXrr] {
            assert_unverified_no_proof(opcode);
        }
    }

    // =======================================================================
    // 26. Generated scalar extension instructions are verified
    // =======================================================================

    #[test]
    fn test_generated_scalar_extensions_name_theorems_but_are_uncredited() {
        for (opcode, theorem) in [
            (AArch64Opcode::Sxtb, "Sextend_I8_to_I32 -> SXTB"),
            (AArch64Opcode::Sxth, "Sextend_I16_to_I32 -> SXTH"),
            (AArch64Opcode::Sxtw, "Sextend_I32_to_I64 -> SXTW"),
            (AArch64Opcode::Uxtb, "Uextend_I8_to_I32 -> UXTB"),
            (AArch64Opcode::Uxth, "Uextend_I16_to_I32 -> UXTH"),
        ] {
            assert_registry_candidate_with_theorem(
                opcode,
                ProofCategory::ExtensionTruncation,
                theorem,
            );
        }
    }

    #[test]
    fn test_uxtw_names_generated_zero_extend_but_is_uncredited() {
        assert_registry_candidate_with_theorem(
            AArch64Opcode::Uxtw,
            ProofCategory::ExtensionTruncation,
            "Uextend_I32_to_I64 -> UXTW",
        );
    }

    #[test]
    fn test_uxtw_mapping_resolves_typed_check_kind() {
        let db = ProofDatabase::new();
        let (query, category) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Uxtw)
            .expect("Uxtw must map to a proof query");
        let query = query.to_lowercase();
        let proof = db
            .by_category(category)
            .into_iter()
            .find(|p| p.obligation.name.to_lowercase().contains(&query))
            .unwrap_or_else(|| panic!("no proof matching {query:?} for Uxtw"));
        assert_eq!(
            proof.obligation.category,
            Some(category.transval_check_kind())
        );
    }

    #[test]
    fn test_generated_scalar_extension_mappings_resolve_typed_check_kind() {
        let db = ProofDatabase::new();
        for opcode in [
            AArch64Opcode::Sxtb,
            AArch64Opcode::Sxth,
            AArch64Opcode::Sxtw,
            AArch64Opcode::Uxtb,
            AArch64Opcode::Uxth,
            AArch64Opcode::Uxtw,
        ] {
            let (query, category) = FunctionVerifier::opcode_to_proof_query(opcode)
                .expect("generated extension opcode must map to a proof query");
            let query = query.to_lowercase();
            let proof = db
                .by_category(category)
                .into_iter()
                .find(|p| p.obligation.name.to_lowercase().contains(&query))
                .unwrap_or_else(|| panic!("no proof matching {query:?} for {opcode:?}"));
            assert_eq!(
                proof.obligation.category,
                Some(category.transval_check_kind())
            );
        }
    }

    #[test]
    fn test_generated_scalar_extension_sequence_has_no_registry_credit() {
        // Operand-less extensions only name registry theorems (E0.2); the
        // trailing RET (proof retracted #62) is tested separately.
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::Sxtb),
            inst(AArch64Opcode::Sxth),
            inst(AArch64Opcode::Sxtw),
            inst(AArch64Opcode::Uxtb),
            inst(AArch64Opcode::Uxth),
            inst(AArch64Opcode::Uxtw),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 6);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.unverified_count(), 6);
        assert_eq!(report.registry_name_lookup_count(), 6);
        assert!(!report.all_verified());
    }

    #[test]
    fn test_generated_cli_add_sequence_has_no_operand_exact_credit() {
        // #62: MovR (degenerate CopyProp X==X) and RET (degenerate RET X==X) proofs
        // were retracted, so those forms are excluded. E0.2: ADD/UXTW here are
        // operand-less registry candidates, so they are uncredited alongside the
        // six unbound pair opcodes (which have no mapping at all). Pair evidence
        // is operand-bound (`aarch64_pair_memory_proofs`), so these bare carriers
        // build no obligation either — see
        // `test_generated_frame_sequence_with_real_operands_is_sampled_not_credited`
        // for the frame shape WITH operands.
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::StpPreIndex),
            inst(AArch64Opcode::AddRR),
            inst(AArch64Opcode::StpRI),
            inst(AArch64Opcode::StpRI),
            inst(AArch64Opcode::AddRR),
            inst(AArch64Opcode::Uxtw),
            inst(AArch64Opcode::LdpRI),
            inst(AArch64Opcode::LdpRI),
            inst(AArch64Opcode::LdpPostIndex),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 9);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.unverified_count(), 9);
        assert_eq!(report.registry_name_lookup_count(), 3);
        assert!(!report.all_verified());
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }

    // =======================================================================
    // 27. Pair evidence comes from the OPERANDS, never from opcode identity
    // =======================================================================
    //
    // `aarch64_pair_memory_proofs` builds, for an emitted pair access, an
    // operand-bound obligation over both transfers and the base writeback.
    // What must NOT happen is an opcode-only or otherwise unbound pair carrier
    // reaching any obligation or query, because opcode identity carries
    // neither the transfer width, the address, nor whether the base is
    // written back. The tests below pin both halves: the operand-less carrier
    // binds nothing, and the real frame prologue/epilogue binds exactly its
    // own non-degenerate obligations — whose sampled discharge is reported,
    // not credited (E0.2).

    #[test]
    fn test_stp_preindex_has_no_unbound_frame_prologue_credit() {
        assert_unverified_no_proof(AArch64Opcode::StpPreIndex);
    }

    #[test]
    fn test_stp_ri_has_no_unbound_callee_save_store_credit() {
        assert_unverified_no_proof(AArch64Opcode::StpRI);
    }

    #[test]
    fn test_ldp_pair_loads_refuse_frame_and_data_shape_credit() {
        use trust_cg_ir::aarch64_regs::{SP, X0, X1, X2};
        // A frame-base spelling alone does not establish a prior matching save,
        // and no pair instruction may reach the broad `("load", Memory)` query:
        // the only pair evidence is the operand-bound pair obligation, never a
        // DB substring search.
        for opcode in [AArch64Opcode::LdpRI, AArch64Opcode::LdpPostIndex] {
            let frame = MachInst::new(
                opcode,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                    MachOperand::PReg(SP),
                    MachOperand::Imm(16),
                ],
            );
            assert_eq!(
                FunctionVerifier::inst_to_proof_query(&frame),
                None,
                "{opcode:?} off a frame base must not borrow a query-route binding"
            );
            assert!(
                crate::aarch64_pair_memory_proofs::pair_memory_obligation(&frame).is_some(),
                "{opcode:?} off a frame base is a well-formed pair and must be operand-bound"
            );
        }
        // DATA SHAPE (any other base): the frame roundtrip models one slot THIS
        // code stored, which is false for an array load that mem-pair-formation
        // folded. A broad load-query match is not an alternative binding — the
        // operand-bound obligation applies to this shape exactly as it does to
        // the frame spelling, because it reasons about the operands and not
        // about a presumed frame story.
        for opcode in [AArch64Opcode::LdpRI, AArch64Opcode::LdpPostIndex] {
            let data = MachInst::new(
                opcode,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                    MachOperand::PReg(X2),
                    MachOperand::Imm(16),
                ],
            );
            assert_eq!(
                FunctionVerifier::inst_to_proof_query(&data),
                None,
                "{opcode:?} off a non-frame base must not borrow frame or representative load credit"
            );
            assert!(
                crate::aarch64_pair_memory_proofs::pair_memory_obligation(&data).is_some(),
                "{opcode:?} off a non-frame base must be operand-bound like any other pair"
            );
        }
    }

    #[test]
    fn test_generated_frame_sequence_retains_unbound_pair_debt() {
        // An opcode-only frame story is not proof of both pair transfers, their
        // addresses or writeback. E0.2: the operand-less ADD/SUB are registry
        // candidates, so no row of this sequence is credited.
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::StpPreIndex),
            inst(AArch64Opcode::AddRI),
            inst(AArch64Opcode::StpRI),
            inst(AArch64Opcode::SubRI),
            inst(AArch64Opcode::LdpRI),
            inst(AArch64Opcode::LdpPostIndex),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 6);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.unverified_count(), 6);
        assert_eq!(report.registry_name_lookup_count(), 2);
        assert!(!report.all_verified());
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }

    /// The real frame prologue/epilogue — WITH operands — binds each pair
    /// access to exactly its own obligation, and that is still not credit.
    ///
    /// This is the shape `frame.rs` emits: save FP/LR with a pre-index STP,
    /// establish FP, spill a callee-save pair, reload it, restore with a
    /// post-index LDP. Each of the four pair accesses reconstructs an
    /// operand-bound, NON-DEGENERATE obligation naming its mode, width and
    /// byte offset, and the walk discharges it. That discharge is sampled
    /// (64-bit base and lanes), so each pair row is reported with its
    /// obligation name and stays `Unverified` (E0.2; this evaluation-only walk
    /// replays no bound-memory certificate). The word-bound memory-effect
    /// decomposition of each row's own word then holds in every part and is
    /// recorded after that reason, never credited (X-OPCODES-P1). The
    /// operand-less ADD/SUB carriers are registry candidates. Nothing here
    /// promotes. `test_generated_frame_sequence_retains_unbound_pair_debt` is
    /// the same sequence with the operands stripped.
    #[test]
    fn test_generated_frame_sequence_with_real_operands_is_sampled_not_credited() {
        use trust_cg_ir::aarch64_regs::{SP, X19, X20, X29, X30};
        let pair = |opcode, rt, rt2, base, imm| {
            MachInst::new(
                opcode,
                vec![
                    MachOperand::PReg(rt),
                    MachOperand::PReg(rt2),
                    MachOperand::PReg(base),
                    MachOperand::Imm(imm),
                ],
            )
        };
        let func = make_func_with_insts(vec![
            pair(AArch64Opcode::StpPreIndex, X29, X30, SP, -32),
            inst(AArch64Opcode::AddRI),
            pair(AArch64Opcode::StpRI, X19, X20, SP, 16),
            inst(AArch64Opcode::SubRI),
            pair(AArch64Opcode::LdpRI, X19, X20, SP, 16),
            pair(AArch64Opcode::LdpPostIndex, X29, X30, SP, 32),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 6);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.unverified_count(), 6);
        assert_eq!(report.sampled_uncredited_count(), 4);
        assert_eq!(report.memory_effect_count(), 4);
        assert_eq!(report.registry_name_lookup_count(), 2);
        assert!(!report.all_verified());
        // Each of the four pair accesses names its own operand-bound,
        // NON-DEGENERATE obligation in its sampled refusal, then its own
        // word's decomposition, in order.
        let pair_rows: Vec<&InstructionVerificationResult> = report
            .instructions
            .iter()
            .filter(|row| {
                matches!(
                    row.opcode,
                    InstructionOpcode::AArch64(
                        AArch64Opcode::StpPreIndex
                            | AArch64Opcode::StpRI
                            | AArch64Opcode::LdpRI
                            | AArch64Opcode::LdpPostIndex,
                    )
                )
            })
            .map(|row| &row.result)
            .collect();
        // clang: stp x29, x30, [sp, #-32]! / stp x19, x20, [sp, #16] /
        // ldp x19, x20, [sp, #16] / ldp x29, x30, [sp], #32.
        let expected = [
            (
                "RECONSTRUCTED PairMemory_STP_pre_8B_off-32 -> StpPreIndex \
                 (real-operand, decoded-word: both transfers and base writeback)",
                "A64 memory effect StpPreIndex 0xa9be7bfd",
            ),
            (
                "RECONSTRUCTED PairMemory_STP_offset_8B_off16 -> StpRI \
                 (real-operand, decoded-word: both transfers and base writeback)",
                "A64 memory effect StpRI 0xa90153f3",
            ),
            (
                "RECONSTRUCTED PairMemory_LDP_offset_8B_off16 -> LdpRI \
                 (real-operand, decoded-word: both transfers and base writeback)",
                "A64 memory effect LdpRI 0xa94153f3",
            ),
            (
                "RECONSTRUCTED PairMemory_LDP_post_8B_off32 -> LdpPostIndex \
                 (real-operand, decoded-word: both transfers and base writeback)",
                "A64 memory effect LdpPostIndex 0xa8c27bfd",
            ),
        ];
        assert_eq!(pair_rows.len(), expected.len());
        for (result, (name, word)) in pair_rows.into_iter().zip(expected) {
            assert_sampled_uncredited(result, &format!("`{name}`"));
            assert_memory_effect(result);
            assert!(
                format!("{result:?}").contains(&format!("`{word}`")),
                "{result:?}"
            );
        }
        let inventory = report.emitted_opcode_inventory();
        assert!(
            !inventory.is_promotable(),
            "sampled pair evidence must not promote the frame sequence"
        );
    }

    /// Pair opcodes still have NO opcode-level query mapping, and must not
    /// acquire one: the operand-bound lane is the only route to pair evidence.
    #[test]
    fn test_generated_frame_pairs_have_no_runtime_model_mapping() {
        for opcode in [
            AArch64Opcode::StpPreIndex,
            AArch64Opcode::StpRI,
            AArch64Opcode::LdpRI,
            AArch64Opcode::LdpPostIndex,
        ] {
            assert!(FunctionVerifier::opcode_to_proof_query(opcode).is_none());
        }
    }

    #[test]
    fn test_generated_large_frame_offset_materialization_reconstructs_but_is_sampled() {
        let func = make_func_with_insts(vec![
            inst_with_operands(
                AArch64Opcode::AddRR,
                vec![
                    MachOperand::PReg(X16),
                    MachOperand::PReg(X29),
                    MachOperand::PReg(X16),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::SubRR,
                vec![
                    MachOperand::PReg(X17),
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::PReg(X17),
                ],
            ),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 2);

        // task #63: AddRR/SubRR are PILOT opcodes, so a frame-address
        // materialization `ADD X16, FP, X16` / `SUB X17, SP, X17` routes through
        // OPERAND RECONSTRUCTION (a genuine Iadd/Isub over the real operands),
        // never the degenerate FrameLayout DB binding. E0.2: the 64-bit instance
        // discharges only by sampling, which is reported, not credited.
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.sampled_uncredited_count(), 2);
        assert_sampled_uncredited(&report.instructions[0].result, "Iadd");
        assert_sampled_uncredited(&report.instructions[1].result, "Isub");
    }

    #[test]
    fn test_regular_add_with_non_frame_materialization_operands_stays_arithmetic() {
        let func = make_func_with_insts(vec![inst_with_operands(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::PReg(X16),
                MachOperand::PReg(X0),
                MachOperand::PReg(X16),
            ],
        )]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 1);
        // Routed through the arithmetic reconstruction (not a frame form);
        // sampled, so uncredited (E0.2).
        assert_eq!(report.verified_count(), 0);
        assert_sampled_uncredited(&report.instructions[0].result, "Iadd");
    }

    #[test]
    fn test_generated_large_frame_offset_mapping_resolves_typed_check_kind() {
        let db = ProofDatabase::new();

        // #62: the ADD large-POSITIVE-offset materialization proof was a degenerate
        // X==X and was RETRACTED, so the ADD frame-materialization shape now falls
        // through to its ordinary arithmetic mapping ("add", Arithmetic).
        let add = inst_with_operands(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::PReg(X16),
                MachOperand::PReg(X29),
                MachOperand::PReg(X16),
            ],
        );
        let (q, cat) = FunctionVerifier::inst_to_proof_query(&add)
            .expect("ADD frame-materialization must fall through to its arithmetic proof");
        assert_eq!(q, "add");
        assert_eq!(cat, ProofCategory::Arithmetic);

        // The SUB large-NEGATIVE-offset materialization proof is GENUINE and remains.
        let sub = inst_with_operands(
            AArch64Opcode::SubRR,
            vec![
                MachOperand::PReg(X17),
                MachOperand::Special(SpecialReg::SP),
                MachOperand::PReg(X17),
            ],
        );
        let (query, category) = FunctionVerifier::inst_to_proof_query(&sub)
            .expect("SUB large-negative frame materialization must map to a proof query");
        assert_eq!(query, "large negative offset materialization");
        assert_eq!(category, ProofCategory::FrameLayout);
        let proof = db
            .by_category(category)
            .into_iter()
            .find(|p| p.obligation.name.to_lowercase().contains(query))
            .unwrap_or_else(|| {
                panic!("no proof matching {query:?} for frame address materialization")
            });
        assert_eq!(
            proof.obligation.category,
            Some(category.transval_check_kind())
        );
    }

    #[test]
    fn test_generated_fp_sp_relative_addressing_reconstructs_but_is_sampled() {
        let func = make_func_with_insts(vec![
            inst_with_operands(
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::Imm(32),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::SubRI,
                vec![
                    MachOperand::PReg(X1),
                    MachOperand::PReg(X29),
                    MachOperand::Imm(512),
                ],
            ),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 2);

        // task #63: AddRI/SubRI are PILOT opcodes, so `ADD X0, SP, #32` /
        // `SUB X1, FP, #512` route through OPERAND RECONSTRUCTION (genuine
        // Iadd/Isub with the real immediate bound as a bv_const) rather than the
        // degenerate FrameLayout DB binding. E0.2: sampled, so uncredited.
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.sampled_uncredited_count(), 2);
        assert_sampled_uncredited(&report.instructions[0].result, "Iadd");
        assert_sampled_uncredited(&report.instructions[1].result, "Isub");
    }

    #[test]
    fn test_generated_fp_sp_relative_addressing_mapping_resolves_typed_check_kind() {
        let db = ProofDatabase::new();
        let inst = inst_with_operands(
            AArch64Opcode::SubRI,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X29),
                MachOperand::Imm(512),
            ],
        );
        let (query, category) = FunctionVerifier::inst_to_proof_query(&inst)
            .expect("generated FP/SP-relative address must map to a proof query");
        assert_eq!(query, "fp/sp-relative addressing equivalence");
        assert_eq!(category, ProofCategory::FrameLayout);

        let proof = db
            .by_category(category)
            .into_iter()
            .find(|p| p.obligation.name.to_lowercase().contains(query))
            .unwrap_or_else(|| panic!("no proof matching {query:?} for FP/SP address"));
        assert_eq!(
            proof.obligation.category,
            Some(category.transval_check_kind())
        );
    }

    #[test]
    fn test_sp_adjust_and_fp_setup_stay_arithmetic() {
        let func = make_func_with_insts(vec![
            inst_with_operands(
                AArch64Opcode::SubRI,
                vec![
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::Imm(32),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::PReg(X29),
                    MachOperand::Special(SpecialReg::SP),
                    MachOperand::Imm(0),
                ],
            ),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 2);
        // Both stay arithmetic, never a frame query. The SP-writing SUB has no
        // reconstructable shape; it is judged by its instruction-derived
        // obligation (L07-P2), and the retired mapping would have named the
        // generic Arithmetic `"sub"` theorem. The FP setup reconstructs but is
        // sampled. Neither is credited (E0.2).
        assert_eq!(report.verified_count(), 0);
        assert_eq!(
            instruction_derived_over_retired_query(&func, &report, 0),
            ("sub", ProofCategory::Arithmetic)
        );
        assert_sampled_uncredited(&report.instructions[1].result, "Iadd");
    }

    // =======================================================================
    // 28. Generated constant materialization moves are verified
    // =======================================================================

    /// A materialization move names exactly one registry theorem (reported,
    /// never credited since E0.2): returns that theorem after checking the
    /// refusal names its query.
    fn assert_const_mat_candidate(inst: MachInst) -> ProofObligation {
        let (query, category) = FunctionVerifier::inst_to_proof_query(&inst)
            .unwrap_or_else(|| panic!("{:?} must name a theorem", inst.opcode));
        assert_eq!(category, ProofCategory::ConstantMaterialization);
        let report = verify_function(&make_func_with_insts(vec![inst]));
        assert_eq!(report.verified_count(), 0);
        assert_registry_withdrawn(&report.instructions[0].result, query);
        registry_theorem(query, category)
    }

    #[test]
    fn test_generated_const_materialization_moves_name_their_own_theorems() {
        let movz = inst_with_operands(
            AArch64Opcode::Movz,
            vec![
                MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::Imm(42),
            ],
        );
        assert!(
            assert_const_mat_candidate(movz)
                .name
                .contains("MOVZ #imm16, LSL #0")
        );

        for (opcode, class) in [
            (AArch64Opcode::MOVZWi, trust_cg_ir::RegClass::Gpr32),
            (AArch64Opcode::MOVZXi, trust_cg_ir::RegClass::Gpr64),
        ] {
            let alias = inst_with_operands(
                opcode,
                vec![
                    MachOperand::VReg(trust_cg_ir::VReg::new(0, class)),
                    MachOperand::Imm(42),
                ],
            );
            assert!(
                assert_const_mat_candidate(alias)
                    .name
                    .contains("MOVZ #imm16, LSL #0")
            );
        }

        let movn = inst_with_operands(
            AArch64Opcode::Movn,
            vec![
                MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::Imm(7),
            ],
        );
        assert!(
            assert_const_mat_candidate(movn)
                .name
                .contains("MOVN Xd #imm16, LSL #0")
        );

        // MOVK names a faithful PER-FORM halfword-splice theorem: one per
        // architecturally legal (width, shift), with an independent
        // concat/extract reference side (non-degenerate), each for ITS OWN slot.
        for shift in [0i64, 16, 32, 48] {
            let movk = inst_with_operands(
                AArch64Opcode::Movk,
                vec![
                    MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                    MachOperand::Imm(1),
                    MachOperand::Imm(shift),
                ],
            );
            let theorem = assert_const_mat_candidate(movk);
            let expected = format!("MOVK Xd #imm16, LSL #{shift} splices halfword");
            assert!(
                theorem.name.contains(&expected) && theorem.name.contains("Xd"),
                "X-form MOVK LSL #{shift} names the wrong theorem: {}",
                theorem.name
            );
            assert!(
                !theorem.is_degenerate(),
                "X-form MOVK LSL #{shift} splice theorem must be non-degenerate"
            );
        }

        // W-form MOVK admits only LSL #0/#16; #32/#48 are architecturally illegal
        // and name nothing.
        for (shift, legal) in [(0i64, true), (16, true), (32, false), (48, false)] {
            let movk = inst_with_operands(
                AArch64Opcode::Movk,
                vec![
                    MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr32)),
                    MachOperand::Imm(1),
                    MachOperand::Imm(shift),
                ],
            );
            if legal {
                let theorem = assert_const_mat_candidate(movk);
                assert!(theorem.name.contains("Wd"), "W-form MOVK LSL #{shift}");
                assert!(!theorem.is_degenerate());
            } else {
                assert!(FunctionVerifier::inst_to_proof_query(&movk).is_none());
                let report = verify_function(&make_func_with_insts(vec![movk]));
                assert_eq!(report.verified_count(), 0);
                assert_eq!(report.unverified_count(), 1);
                assert_eq!(report.registry_name_lookup_count(), 0);
            }
        }
    }

    #[test]
    fn movn_per_form_binding_names_all_legal_forms_and_refuses_illegal_w_shifts() {
        // MOVN names a faithful PER-FORM inverted-field theorem: one per
        // architecturally legal (width, shift), whose reference side is an
        // independent concat/XOR inverted-field algebra. Every legal X-form slot
        // names the theorem for ITS OWN slot (never another's). E0.2: named, not
        // credited.
        for shift in [0i64, 16, 32, 48] {
            let movn = inst_with_operands(
                AArch64Opcode::Movn,
                vec![
                    MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                    MachOperand::Imm(1),
                    MachOperand::Imm(shift),
                ],
            );
            let theorem = assert_const_mat_candidate(movn);
            let expected = format!("LSL #{shift} inverts halfword");
            assert!(
                theorem.name.contains(&expected) && theorem.name.contains("Xd"),
                "X-form MOVN LSL #{shift} names the wrong theorem: {}",
                theorem.name
            );
            assert!(
                !theorem.is_degenerate(),
                "X-form MOVN LSL #{shift} inverted-field theorem must be non-degenerate"
            );
        }

        // W-form MOVN admits only LSL #0/#16, and its theorem pins the 32-bit
        // complement + zero-extension (upper 32 bits zero). #32/#48 are
        // architecturally illegal and must NOT name an X-form slot's theorem.
        for (shift, legal) in [(0i64, true), (16, true), (32, false), (48, false)] {
            let movn = inst_with_operands(
                AArch64Opcode::Movn,
                vec![
                    MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr32)),
                    MachOperand::Imm(1),
                    MachOperand::Imm(shift),
                ],
            );
            if legal {
                let theorem = assert_const_mat_candidate(movn);
                assert!(
                    theorem.name.contains("Wd") && theorem.name.contains("upper 32 bits zero"),
                    "W-form MOVN LSL #{shift} must name the width-specific theorem"
                );
                assert!(!theorem.is_degenerate());
            } else {
                assert!(FunctionVerifier::inst_to_proof_query(&movn).is_none());
                let report = verify_function(&make_func_with_insts(vec![movn]));
                assert_eq!(
                    report.verified_count(),
                    0,
                    "illegal W-form MOVN LSL #{shift} must not be credited"
                );
                assert_eq!(report.unverified_count(), 1);
                assert_eq!(report.registry_name_lookup_count(), 0);
            }
        }
    }

    #[test]
    fn eor_lsl_lsr_reconstruction_is_sampled_at_all_emitted_widths() {
        for (class, width) in [
            (trust_cg_ir::RegClass::Gpr32, 32i64),
            (trust_cg_ir::RegClass::Gpr64, 64),
        ] {
            for opcode in [AArch64Opcode::EorRRLsl, AArch64Opcode::EorRRLsr] {
                for amount in [1i64, 7, width - 1] {
                    let fused = inst_with_operands(
                        opcode,
                        vec![
                            MachOperand::VReg(trust_cg_ir::VReg::new(0, class)),
                            MachOperand::VReg(trust_cg_ir::VReg::new(1, class)),
                            MachOperand::VReg(trust_cg_ir::VReg::new(2, class)),
                            MachOperand::Imm(amount),
                        ],
                    );
                    let report = verify_function(&make_func_with_insts(vec![fused]));
                    // Reconstructed from the real operands, discharged only by
                    // sampling: reported, never credited (E0.2).
                    assert_eq!(
                        report.genuinely_verified_count(),
                        0,
                        "{opcode:?} #{amount} at width {width}"
                    );
                    assert_eq!(report.failed_count(), 0);
                    assert_sampled_uncredited(&report.instructions[0].result, "Bxor");
                }
            }
        }
    }

    #[test]
    fn ror_immediate_reconstruction_is_sampled_for_w32_and_x64() {
        use crate::lowering_proof::verify_by_evaluation;

        for (class, width) in [
            (trust_cg_ir::RegClass::Gpr32, 32i64),
            (trust_cg_ir::RegClass::Gpr64, 64),
        ] {
            let reg = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, class));
            for amount in [1i64, 7, width - 1] {
                let ror = inst_with_operands(
                    AArch64Opcode::RorRI,
                    vec![reg(0), reg(1), MachOperand::Imm(amount)],
                );
                assert_eq!(
                    aarch64_emitted_op_class(&ror),
                    Some(OpClass::Bitwise),
                    "RorRI must cross-check as the bitwise rotate idiom"
                );
                let obligation = reconstruct_alu_obligation(&ror)
                    .expect("well-formed RorRI must reconstruct from its EXTR alias");
                assert!(obligation.is_reconstructed());
                assert!(
                    obligation.is_genuinely_proven(),
                    "shift/OR source and EXTR machine decode must be structurally distinct"
                );
                assert!(matches!(
                    verify_by_evaluation(&obligation),
                    VerificationResult::Valid
                ));

                // E0.2: the sampled discharge is reported, not credited, and
                // therefore blocks promotion.
                let report = verify_function(&make_func_with_insts(vec![ror]));
                assert_eq!(
                    report.genuinely_verified_count(),
                    0,
                    "RorRI #{amount} at width {width}"
                );
                assert_sampled_uncredited(&report.instructions[0].result, "Ror");
                assert!(!report.emitted_opcode_inventory().is_promotable());
            }
        }

        for (dst, src, width) in [
            (MachOperand::PReg(W16), MachOperand::PReg(W17), 32),
            (MachOperand::PReg(X16), MachOperand::PReg(X17), 64),
        ] {
            let ror = inst_with_operands(AArch64Opcode::RorRI, vec![dst, src, MachOperand::Imm(7)]);
            let obligation = reconstruct_alu_obligation(&ror)
                .expect("ordinary physical W/X registers must reconstruct");
            assert!(matches!(
                verify_by_evaluation(&obligation),
                VerificationResult::Valid
            ));
            let report = verify_function(&make_func_with_insts(vec![ror]));
            assert_eq!(
                report.sampled_uncredited_count(),
                1,
                "physical-register RorRI must reconstruct at width {width}"
            );
        }
    }

    /// With explicit proof authority, both RorRI widths must be independently
    /// certified. The runtime certification-gap skip this test carried (an
    /// exact `unproved_steps=1` BvBitBlast disclosure accepted as a pass) is
    /// gone: AY `2657db47c` with Clean `ed21fee39` certifies both widths on the
    /// Darwin host, while the Trust package's AY (build 9624) discloses the
    /// hole at width 32 and answers `incomplete self-check-rejected` at width
    /// 64. A pair that cannot certify fails here naming the tools; the
    /// reproducer is `reports/2026-10-01-ror-udiv-trap-expansion/`.
    #[test]
    fn ror_immediate_live_checker_is_verified() {
        use crate::ay_bridge::{AYConfig, AYResult, verify_with_ay};

        if std::env::var_os("TCG_EXTERNAL_CLEAN_CHECKER").is_none() {
            crate::formal_gap::skip_test(
                "ror_immediate_live_checker_is_verified",
                crate::formal_gap::NO_EXPLICIT_AUTHORITY_ENV,
            );
            return;
        }
        assert!(
            crate::ay_bridge::resolved_solver().is_some(),
            "the admitted toolchain AY and the explicit Clean/Carcara checker must resolve to \
             a usable proof authority: {:?}",
            crate::ay_bridge::proof_toolchain_unavailable_reason()
        );
        let _solver_lock = crate::ay_bridge::formal_solver_test_lock();
        let config = AYConfig {
            solver: None,
            timeout_ms: 5_000,
            produce_models: true,
        };

        for (class, width) in [
            (trust_cg_ir::RegClass::Gpr32, 32u32),
            (trust_cg_ir::RegClass::Gpr64, 64),
        ] {
            let reg = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, class));
            let ror = inst_with_operands(
                AArch64Opcode::RorRI,
                vec![reg(0), reg(1), MachOperand::Imm(7)],
            );
            let obligation = reconstruct_alu_obligation(&ror).unwrap();
            let result = verify_with_ay(&obligation, &config);
            assert_eq!(
                result,
                AYResult::Verified,
                "RorRI EXTR-alias reconstruction at width {width} must be independently \
                 certified; AY {:?} with Clean {:?} did not (reproducer: \
                 reports/2026-10-01-ror-udiv-trap-expansion/README.md)",
                crate::ay_bridge::resolved_solver(),
                std::env::var_os("TCG_EXTERNAL_CLEAN_CHECKER"),
            );
        }
    }

    #[test]
    fn ror_immediate_reconstruction_refutes_wrong_extr_fields() {
        use crate::aarch64_semantics::encode_ror_imm_extr;
        use crate::smt::EvalEnv;

        for (class, size, width) in [
            (trust_cg_ir::RegClass::Gpr32, OperandSize::S32, 32u32),
            (trust_cg_ir::RegClass::Gpr64, OperandSize::S64, 64u32),
        ] {
            let reg = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, class));
            let valid = inst_with_operands(
                AArch64Opcode::RorRI,
                vec![reg(0), reg(1), MachOperand::Imm(7)],
            );
            let obligation = reconstruct_alu_obligation(&valid).unwrap();
            let mut env = EvalEnv::default();
            env.insert("recon_src".to_string(), 1);

            let correct_extr = encode_ror_imm_extr(size, SmtExpr::var("recon_src", width), 7);
            assert_eq!(
                obligation.trust_ir_expr.eval(&env),
                correct_extr.eval(&env),
                "the direct EXTR alias decode must agree with ROR at width {width}"
            );

            let wrong_amount = encode_ror_imm_extr(size, SmtExpr::var("recon_src", width), 8);
            assert_ne!(
                obligation.trust_ir_expr.eval(&env),
                wrong_amount.eval(&env),
                "an EXTR immediate-field error must refute at width {width}"
            );

            // Wrong source field: decode EXTR from two different registers
            // instead of the required same-register pair. A non-zero wrong high
            // half is observable in the wrapped bits selected by #7.
            let wrong_source = SmtExpr::var("wrong_src", width)
                .concat(SmtExpr::var("recon_src", width))
                .extract(7 + width - 1, 7);
            env.insert("wrong_src".to_string(), u64::MAX);
            assert_ne!(
                obligation.trust_ir_expr.eval(&env),
                wrong_source.eval(&env),
                "an EXTR source-register field error must refute at width {width}"
            );
        }
    }

    #[test]
    fn ror_immediate_reconstruction_fails_closed_on_alias_and_shape() {
        let w = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, trust_cg_ir::RegClass::Gpr32));
        let x = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, trust_cg_ir::RegClass::Gpr64));
        let s = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, trust_cg_ir::RegClass::Fpr32));

        let malformed = [
            // #0 is encoded as MOV and needs a separate copy-alias proof.
            vec![w(0), w(1), MachOperand::Imm(0)],
            vec![w(0), w(1), MachOperand::Imm(-1)],
            vec![w(0), w(1), MachOperand::Imm(32)],
            vec![w(0), w(1)],
            vec![w(0), w(1), w(2)],
            vec![w(0), x(1), MachOperand::Imm(7)],
            vec![s(0), s(1), MachOperand::Imm(7)],
            vec![MachOperand::PReg(SP), x(1), MachOperand::Imm(7)],
            vec![x(0), MachOperand::PReg(SP), MachOperand::Imm(7)],
            vec![MachOperand::PReg(WSP), w(1), MachOperand::Imm(7)],
            vec![w(0), MachOperand::PReg(WSP), MachOperand::Imm(7)],
            vec![MachOperand::PReg(WZR), w(1), MachOperand::Imm(7)],
            vec![w(0), MachOperand::PReg(WZR), MachOperand::Imm(7)],
            vec![MachOperand::PReg(XZR), x(1), MachOperand::Imm(7)],
            vec![x(0), MachOperand::PReg(XZR), MachOperand::Imm(7)],
            vec![
                MachOperand::Special(SpecialReg::SP),
                x(1),
                MachOperand::Imm(7),
            ],
            vec![
                x(0),
                MachOperand::Special(SpecialReg::SP),
                MachOperand::Imm(7),
            ],
            vec![
                w(0),
                MachOperand::Special(SpecialReg::WZR),
                MachOperand::Imm(7),
            ],
            vec![
                MachOperand::Special(SpecialReg::XZR),
                x(1),
                MachOperand::Imm(7),
            ],
            vec![
                x(0),
                MachOperand::Special(SpecialReg::XZR),
                MachOperand::Imm(7),
            ],
            vec![
                MachOperand::Special(SpecialReg::WZR),
                w(1),
                MachOperand::Imm(7),
            ],
        ];
        for operands in malformed {
            let malformed = inst_with_operands(AArch64Opcode::RorRI, operands);
            assert!(
                reconstruct_alu_obligation(&malformed).is_none(),
                "malformed RorRI must fail closed: {:?}",
                malformed.operands
            );
        }
    }

    #[test]
    fn physical_zero_register_mvn_alias_and_generic_destinations_fail_closed() {
        use crate::lowering_proof::verify_by_evaluation;

        for (class, zero, width) in [
            (trust_cg_ir::RegClass::Gpr32, MachOperand::PReg(WZR), 32),
            (trust_cg_ir::RegClass::Gpr64, MachOperand::PReg(XZR), 64),
            (
                trust_cg_ir::RegClass::Gpr32,
                MachOperand::Special(SpecialReg::WZR),
                32,
            ),
            (
                trust_cg_ir::RegClass::Gpr64,
                MachOperand::Special(SpecialReg::XZR),
                64,
            ),
        ] {
            let reg = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, class));
            let mvn = inst_with_operands(AArch64Opcode::OrnRR, vec![reg(0), zero, reg(1)]);
            let obligation = reconstruct_alu_obligation(&mvn)
                .expect("both physical and special ZR forms must select the MVN alias");
            assert!(obligation.name.contains(&format!("Bnot_{width}")));
            assert_eq!(obligation.inputs.len(), 1);
            assert!(matches!(
                verify_by_evaluation(&obligation),
                VerificationResult::Valid
            ));
        }

        let w = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, trust_cg_ir::RegClass::Gpr32));
        let x = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, trust_cg_ir::RegClass::Gpr64));
        for malformed in [
            // A zero-register alias with the wrong W/X tag is not a well-typed
            // MVN instruction and must not inherit the other width's proof.
            vec![w(0), MachOperand::PReg(XZR), w(1)],
            vec![x(0), MachOperand::PReg(WZR), x(1)],
        ] {
            assert!(
                reconstruct_alu_obligation(&inst_with_operands(AArch64Opcode::OrnRR, malformed,))
                    .is_none()
            );
        }

        for (dst, src1, src2) in [
            (MachOperand::PReg(WZR), w(1), w(2)),
            (MachOperand::PReg(XZR), x(1), x(2)),
            (MachOperand::PReg(WSP), w(1), w(2)),
            (MachOperand::PReg(SP), x(1), x(2)),
            (MachOperand::Special(SpecialReg::WZR), w(1), w(2)),
            (MachOperand::Special(SpecialReg::XZR), x(1), x(2)),
            (MachOperand::Special(SpecialReg::SP), x(1), x(2)),
        ] {
            let discarded_or_special_dst =
                inst_with_operands(AArch64Opcode::AddRR, vec![dst, src1, src2]);
            assert!(
                reconstruct_alu_obligation(&discarded_or_special_dst).is_none(),
                "generic reconstruction must reject non-ordinary destinations: {:?}",
                discarded_or_special_dst.operands
            );
        }
    }

    #[test]
    fn tst_packed_nzcv_binding_is_width_and_shape_sensitive() {
        for (class, width_tag) in [
            (trust_cg_ir::RegClass::Gpr32, "w32"),
            (trust_cg_ir::RegClass::Gpr64, "w64"),
        ] {
            let reg = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, class));
            for rhs in [reg(1), MachOperand::Imm(0xff)] {
                let tst = inst_with_operands(AArch64Opcode::Tst, vec![reg(0), rhs]);
                let (query, category) = FunctionVerifier::inst_to_proof_query(&tst)
                    .expect("well-formed TST must name its complete flag theorem");
                assert_eq!(query, format!("tst packed nzcv {width_tag}"));
                assert_eq!(category, ProofCategory::CmpCombine);
                let theorem = registry_theorem(query, category);
                assert!(!theorem.is_degenerate());
                assert!(theorem.name.to_lowercase().contains(width_tag));

                // E0.2: the named theorem is not a proof about this TST.
                let report = verify_function(&make_func_with_insts(vec![tst]));
                assert_eq!(report.genuinely_verified_count(), 0);
                assert_registry_withdrawn(&report.instructions[0].result, query);
            }
        }

        let w = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, trust_cg_ir::RegClass::Gpr32));
        let x = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, trust_cg_ir::RegClass::Gpr64));
        let f = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, trust_cg_ir::RegClass::Fpr32));
        for malformed in [
            inst_with_operands(AArch64Opcode::Tst, vec![]),
            inst_with_operands(AArch64Opcode::Tst, vec![x(0)]),
            inst_with_operands(AArch64Opcode::Tst, vec![w(0), x(1)]),
            inst_with_operands(AArch64Opcode::Tst, vec![f(0), w(1)]),
            inst_with_operands(AArch64Opcode::Tst, vec![MachOperand::PReg(SP), x(1)]),
            inst_with_operands(AArch64Opcode::Tst, vec![x(0), MachOperand::Imm(0)]),
            inst_with_operands(AArch64Opcode::Tst, vec![x(0), x(1), MachOperand::Imm(1)]),
        ] {
            assert!(
                FunctionVerifier::inst_to_proof_query(&malformed).is_none(),
                "malformed TST must fail closed: {:?}",
                malformed.operands
            );
        }
    }

    #[test]
    fn tst_complete_flag_theorem_does_not_promote_a_real_instruction() {
        // E0.2: the packed-NZCV theorem is complete for its representative
        // operands, but it is found by name, so the TST blocks promotion.
        let x = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, trust_cg_ir::RegClass::Gpr64));
        let func = make_func_with_insts(vec![
            inst_with_operands(AArch64Opcode::Tst, vec![x(0), x(1)]),
            inst(AArch64Opcode::Ret),
        ]);
        let report = verify_function(&func);
        assert_registry_withdrawn(&report.instructions[0].result, "tst packed nzcv w64");
        assert!(!report.emitted_opcode_inventory().is_promotable());
    }

    #[test]
    fn bitfield_extract_binding_is_width_and_shape_sensitive() {
        for (class, width_tag) in [
            (trust_cg_ir::RegClass::Gpr32, "w32"),
            (trust_cg_ir::RegClass::Gpr64, "w64"),
        ] {
            let reg = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, class));
            let inst = inst_with_operands(
                AArch64Opcode::Ubfm,
                vec![reg(0), reg(1), MachOperand::Imm(8), MachOperand::Imm(11)],
            );
            let (query, category) = FunctionVerifier::inst_to_proof_query(&inst)
                .expect("valid extract-form UBFM must bind");
            assert_eq!(query, format!("ubfm extract {width_tag}"));
            assert_eq!(category, ProofCategory::ExtensionTruncation);
            assert!(
                registry_theorem(query, category)
                    .name
                    .to_lowercase()
                    .contains(width_tag),
                "wrong carrier theorem named for {width_tag}"
            );

            // E0.2: named, not credited.
            let report = verify_function(&make_func_with_insts(vec![inst]));
            assert_registry_withdrawn(&report.instructions[0].result, query);
        }

        let w = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, trust_cg_ir::RegClass::Gpr32));
        let x = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, trust_cg_ir::RegClass::Gpr64));
        for malformed in [
            inst_with_operands(AArch64Opcode::Ubfm, vec![]),
            inst_with_operands(
                AArch64Opcode::Ubfm,
                vec![w(0), x(1), MachOperand::Imm(1), MachOperand::Imm(3)],
            ),
            inst_with_operands(
                AArch64Opcode::Ubfm,
                vec![w(0), w(1), MachOperand::Imm(4), MachOperand::Imm(3)],
            ),
            inst_with_operands(
                AArch64Opcode::Ubfm,
                vec![w(0), w(1), MachOperand::Imm(1), MachOperand::Imm(32)],
            ),
        ] {
            assert!(
                FunctionVerifier::inst_to_proof_query(&malformed).is_none(),
                "malformed UBFM must fail closed: {:?}",
                malformed.operands
            );
        }
    }

    #[test]
    fn eor_shift_reconstruction_fails_closed_on_shape_and_refutes_wrong_kind() {
        use crate::aarch64_semantics::{RegShiftKind, encode_eor_shifted_reg};
        use crate::smt::EvalEnv;

        let w = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, trust_cg_ir::RegClass::Gpr32));
        let valid = inst_with_operands(
            AArch64Opcode::EorRRLsl,
            vec![w(0), w(1), w(2), MachOperand::Imm(1)],
        );
        let mut obligation =
            reconstruct_alu_obligation(&valid).expect("well-formed EOR LSL must reconstruct");
        obligation.aarch64_expr = encode_eor_shifted_reg(
            OperandSize::S32,
            SmtExpr::var("recon_src1", 32),
            SmtExpr::var("recon_src2", 32),
            RegShiftKind::Lsr,
            1,
        );
        let mut env = EvalEnv::default();
        env.insert("recon_src1".to_string(), 0);
        env.insert("recon_src2".to_string(), 1);
        assert_ne!(
            obligation.trust_ir_expr.eval(&env),
            obligation.aarch64_expr.eval(&env),
            "the reconstruction must distinguish an LSL source from an LSR machine form"
        );

        let mixed_width = inst_with_operands(
            AArch64Opcode::EorRRLsl,
            vec![
                w(0),
                w(1),
                MachOperand::VReg(trust_cg_ir::VReg::new(2, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::Imm(1),
            ],
        );
        assert!(reconstruct_alu_obligation(&mixed_width).is_none());

        for bad_amount in [0, 32] {
            let malformed = inst_with_operands(
                AArch64Opcode::EorRRLsr,
                vec![w(0), w(1), w(2), MachOperand::Imm(bad_amount)],
            );
            assert!(reconstruct_alu_obligation(&malformed).is_none());
        }
    }

    #[test]
    fn test_shifted_movz_does_not_inherit_shift_zero_proof() {
        for shift in [0i64, 16, 32, 48] {
            let movz = inst_with_operands(
                AArch64Opcode::Movz,
                vec![
                    MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                    MachOperand::Imm(0x1234),
                    MachOperand::Imm(shift),
                ],
            );
            let query = FunctionVerifier::inst_to_proof_query(&movz);
            let report = verify_function(&make_func_with_insts(vec![movz]));
            if shift == 0 {
                let (query, category) = query.expect("shift-zero MOVZ must retain the hw0 query");
                assert_eq!(query, "movz #imm16, lsl #0");
                assert_eq!(category, ProofCategory::ConstantMaterialization);
                assert!(
                    registry_theorem(query, category).name.contains("LSL #0"),
                    "shift zero names the wrong theorem"
                );
                // E0.2: named, not credited.
                assert_eq!(report.verified_count(), 0);
                assert_registry_withdrawn(&report.instructions[0].result, query);
            } else {
                assert_eq!(report.verified_count(), 0);
                assert_eq!(report.unverified_count(), 1);
                assert_eq!(report.registry_name_lookup_count(), 0);
                assert!(
                    query.is_none(),
                    "shifted MOVZ must not inherit the hw0 proof"
                );
            }
        }

        let invalid = inst_with_operands(
            AArch64Opcode::Movz,
            vec![
                MachOperand::PReg(X0),
                MachOperand::Imm(1),
                MachOperand::Imm(8),
            ],
        );
        assert!(
            FunctionVerifier::inst_to_proof_query(&invalid).is_none(),
            "invalid MOVZ shift must not inherit the hw0 proof"
        );

        for invalid in [
            inst_with_operands(
                AArch64Opcode::Movz,
                vec![MachOperand::PReg(X0), MachOperand::Imm(0x1_0000)],
            ),
            inst_with_operands(
                AArch64Opcode::Movz,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::Imm(1),
                    MachOperand::Imm(16),
                    MachOperand::Imm(0),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::Movz,
                vec![
                    MachOperand::PReg(trust_cg_ir::aarch64_regs::W0),
                    MachOperand::Imm(1),
                    MachOperand::Imm(32),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::Movz,
                vec![MachOperand::Special(SpecialReg::SP), MachOperand::Imm(1)],
            ),
            inst_with_operands(
                AArch64Opcode::Movz,
                vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
            ),
            inst_with_operands(
                AArch64Opcode::Movz,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::Imm(1),
                    MachOperand::PReg(X1),
                ],
            ),
        ] {
            assert!(
                FunctionVerifier::inst_to_proof_query(&invalid).is_none(),
                "encoder-invalid MOVZ shape must not receive a proof"
            );
        }

        // W-form MOVN no longer inherits the X-form theorem OR goes unverified:
        // it binds its own width-specific proof, which pins the 32-bit
        // complement + zero-extension the X-form theorem cannot supply.
        let w_form = inst_with_operands(
            AArch64Opcode::Movn,
            vec![
                MachOperand::PReg(trust_cg_ir::aarch64_regs::W0),
                MachOperand::Imm(1),
            ],
        );
        assert_eq!(
            FunctionVerifier::inst_to_proof_query(&w_form),
            Some((
                "movn wd #imm16, lsl #0 inverts halfword",
                ProofCategory::ConstantMaterialization
            )),
            "W-form MOVN must bind the width-specific W-form proof, never the X-form theorem"
        );
        let theorem = registry_theorem(
            "movn wd #imm16, lsl #0 inverts halfword",
            ProofCategory::ConstantMaterialization,
        );
        assert!(!theorem.is_degenerate());
        // L07-P2: on a hardware register the walk judges it by its
        // instruction-derived obligation, not by that theorem.
        let report = verify_function(&make_func_with_insts(vec![w_form]));
        assert_instruction_derived(&report.instructions[0].result);
    }

    #[test]
    fn test_shifted_movn_binds_its_own_slot_never_another_forms_proof() {
        // Every legal X-form shift binds the query for EXACTLY its own
        // (width, shift) — per-form credit, not hw0 inheritance (the #62 class).
        for shift in [0i64, 16, 32, 48] {
            let movn = inst_with_operands(
                AArch64Opcode::Movn,
                vec![
                    MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                    MachOperand::Imm(0x1234),
                    MachOperand::Imm(shift),
                ],
            );
            let expected = crate::const_materialize_proofs::movn_halfword_query(64, shift as u32)
                .expect("legal X-form MOVN shift");
            assert_eq!(
                FunctionVerifier::inst_to_proof_query(&movn),
                Some((expected, ProofCategory::ConstantMaterialization)),
                "X-form MOVN LSL #{shift} must bind its own per-form proof"
            );
            // E0.2: the named per-form theorem is reported, not credited.
            let report = verify_function(&make_func_with_insts(vec![movn]));
            assert_eq!(report.verified_count(), 0);
            assert_registry_withdrawn(&report.instructions[0].result, expected);
        }

        // Architecturally illegal W-form shifts bind NOTHING.
        for shift in [32i64, 48] {
            let movn = inst_with_operands(
                AArch64Opcode::Movn,
                vec![
                    MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr32)),
                    MachOperand::Imm(0x1234),
                    MachOperand::Imm(shift),
                ],
            );
            assert!(
                FunctionVerifier::inst_to_proof_query(&movn).is_none(),
                "illegal W-form MOVN LSL #{shift} must not inherit an X slot's proof"
            );
        }

        for invalid in [
            inst_with_operands(
                AArch64Opcode::Movn,
                vec![MachOperand::PReg(X0), MachOperand::Imm(0x1_0000)],
            ),
            inst_with_operands(
                AArch64Opcode::Movn,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::Imm(1),
                    MachOperand::Imm(0),
                    MachOperand::Imm(0),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::Movn,
                vec![MachOperand::Special(SpecialReg::SP), MachOperand::Imm(1)],
            ),
            inst_with_operands(
                AArch64Opcode::Movn,
                vec![MachOperand::PReg(X0), MachOperand::PReg(X1)],
            ),
            // Non-halfword shift amounts are encoder-invalid in BOTH forms.
            inst_with_operands(
                AArch64Opcode::Movn,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::Imm(1),
                    MachOperand::Imm(8),
                ],
            ),
            // Shift operand must be an immediate, not a register.
            inst_with_operands(
                AArch64Opcode::Movn,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::Imm(1),
                    MachOperand::PReg(X1),
                ],
            ),
        ] {
            assert!(
                FunctionVerifier::inst_to_proof_query(&invalid).is_none(),
                "encoder-invalid MOVN shape must not receive a proof"
            );
        }
    }

    #[test]
    fn test_malformed_movi_movk_and_typed_movz_receive_no_proof() {
        for invalid in [
            inst_with_operands(
                AArch64Opcode::MovI,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::Imm(1),
                    MachOperand::Imm(0),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::MovI,
                vec![MachOperand::Special(SpecialReg::SP), MachOperand::Imm(1)],
            ),
            inst_with_operands(
                AArch64Opcode::MOVZXi,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::Imm(1),
                    MachOperand::Imm(0),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::MOVZWi,
                vec![MachOperand::PReg(X0), MachOperand::Imm(0x1_0000)],
            ),
            inst_with_operands(
                AArch64Opcode::MOVZWi,
                vec![MachOperand::PReg(X0), MachOperand::Imm(1)],
            ),
            inst_with_operands(
                AArch64Opcode::MOVZXi,
                vec![
                    MachOperand::PReg(trust_cg_ir::aarch64_regs::W0),
                    MachOperand::Imm(1),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::Movk,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::Imm(1),
                    MachOperand::Imm(8),
                ],
            ),
        ] {
            assert!(
                FunctionVerifier::inst_to_proof_query(&invalid).is_none(),
                "encoder-invalid move-wide shape must not receive a proof"
            );
        }
    }

    #[test]
    fn test_generated_const_materialization_mappings_resolve_typed_check_kind() {
        let db = ProofDatabase::new();
        for opcode in [
            AArch64Opcode::Movz,
            AArch64Opcode::MOVZWi,
            AArch64Opcode::MOVZXi,
        ] {
            let (query, category) = FunctionVerifier::opcode_to_proof_query(opcode)
                .expect("generated constant materialization opcode must map to a proof query");
            let query = query.to_lowercase();
            let proof = db
                .by_category(category)
                .into_iter()
                .find(|p| p.obligation.name.to_lowercase().contains(&query))
                .unwrap_or_else(|| panic!("no proof matching {query:?} for {opcode:?}"));
            assert_eq!(
                proof.obligation.category,
                Some(category.transval_check_kind())
            );
        }
    }

    #[test]
    fn test_generated_const_materialization_large_offset_names_theorems_but_is_uncovered() {
        // REGRESSION PIN (history): a wide-constant chain (MOVZ + MOVK) was once
        // left with MOVK as its one uncovered row. E0.2: every row here now only
        // names a registry theorem (MOVZ/MOVK per-form splices, operand-less
        // ADD/LDR/STR), so none is credited.
        let constant = trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr64);
        let func = make_func_with_insts(vec![
            inst_with_operands(
                AArch64Opcode::Movz,
                vec![MachOperand::VReg(constant), MachOperand::Imm(0x1234)],
            ),
            inst_with_operands(
                AArch64Opcode::Movk,
                vec![
                    MachOperand::VReg(constant),
                    MachOperand::Imm(0x5678),
                    MachOperand::Imm(16),
                ],
            ),
            inst(AArch64Opcode::AddRR),
            inst(AArch64Opcode::LdrRI),
            inst(AArch64Opcode::StrRI),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 5);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.registry_name_lookup_count(), 5);
        assert_registry_withdrawn(
            &report.instructions[1].result,
            "movk xd #imm16, lsl #16 splices halfword",
        );
        assert!(!report.all_verified());
    }

    #[test]
    fn test_generated_const_materialization_small_negative_sequence_is_uncredited() {
        // MOVN names its per-form theorem but is not credited (E0.2); the
        // trailing RET (proof retracted in #62) is tested separately.
        let movn = inst_with_operands(
            AArch64Opcode::Movn,
            vec![
                MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::Imm(0),
            ],
        );
        assert!(
            assert_const_mat_candidate(movn)
                .name
                .contains("MOVN Xd #imm16, LSL #0")
        );
    }

    // =======================================================================
    // 29. Generated FP conversion instructions are verified
    // =======================================================================

    #[test]
    fn test_generated_fp_conversion_ops_name_theorems_but_are_uncredited() {
        for (opcode, theorem) in [
            (AArch64Opcode::FcvtzsRR, "FCVTZS"),
            (AArch64Opcode::FcvtzuRR, "FCVTZU"),
            (AArch64Opcode::ScvtfRR, "SCVTF"),
            (AArch64Opcode::UcvtfRR, "UCVTF"),
            (AArch64Opcode::FcvtSD, "Fpromote_F64_F32 -> FCVT Dd,Sn"),
            (AArch64Opcode::FcvtDS, "Fdemote_F32_F64 -> FCVT Ss,Dn"),
        ] {
            assert_registry_candidate_with_theorem(opcode, ProofCategory::FpConversion, theorem);
        }
    }

    #[test]
    fn test_generated_fp_conversion_mappings_resolve_typed_check_kind() {
        let db = ProofDatabase::new();
        for opcode in [
            AArch64Opcode::FcvtzsRR,
            AArch64Opcode::FcvtzuRR,
            AArch64Opcode::ScvtfRR,
            AArch64Opcode::UcvtfRR,
            AArch64Opcode::FcvtSD,
            AArch64Opcode::FcvtDS,
        ] {
            let (query, category) = FunctionVerifier::opcode_to_proof_query(opcode)
                .expect("generated FP conversion opcode must map to a proof query");
            let query = query.to_lowercase();
            let proof = db
                .by_category(category)
                .into_iter()
                .find(|p| p.obligation.name.to_lowercase().contains(&query))
                .unwrap_or_else(|| panic!("no proof matching {query:?} for {opcode:?}"));
            assert_eq!(
                proof.obligation.category,
                Some(category.transval_check_kind())
            );
        }
    }

    #[test]
    fn test_generated_fp_conversion_sequence_has_no_registry_credit() {
        // Operand-less FP conversions only name registry theorems (E0.2); the
        // trailing RET (proof retracted #62) is tested separately.
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::ScvtfRR),
            inst(AArch64Opcode::FcvtzsRR),
            inst(AArch64Opcode::UcvtfRR),
            inst(AArch64Opcode::FcvtzuRR),
            inst(AArch64Opcode::FcvtSD),
            inst(AArch64Opcode::FcvtDS),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 6);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.unverified_count(), 6);
        assert_eq!(report.registry_name_lookup_count(), 6);
        assert!(!report.all_verified());
    }

    // =======================================================================
    // 30. Generated stack-slot spill/reload instructions are verified
    // =======================================================================

    #[test]
    fn test_generated_stack_slot_spill_reload_operands_select_distinct_proofs() {
        let slot = StackSlotId(0);
        let func = make_func_with_insts(vec![
            inst_with_operands(
                AArch64Opcode::LdrRI,
                vec![MachOperand::PReg(X16), MachOperand::StackSlot(slot)],
            ),
            inst_with_operands(
                AArch64Opcode::StrRI,
                vec![MachOperand::PReg(X16), MachOperand::StackSlot(slot)],
            ),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 2);
        // E0.2: the operands still select distinct RegAlloc theorems, but a
        // selected theorem is reported, not credited.
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.registry_name_lookup_count(), 2);

        let (query, category) = withdrawn_registry_row(&report.instructions[0].result);
        assert_eq!(category, ProofCategory::RegAlloc);
        let theorem = registry_theorem(&query, category);
        assert!(
            theorem.name.contains("spill/reload semantic roundtrip"),
            "unexpected stack-slot reload theorem: {}",
            theorem.name
        );

        let (query, category) = withdrawn_registry_row(&report.instructions[1].result);
        assert_eq!(category, ProofCategory::RegAlloc);
        let theorem = registry_theorem(&query, category);
        assert!(
            theorem.name.contains("spill offset non-interference"),
            "unexpected stack-slot spill theorem: {}",
            theorem.name
        );
    }

    #[test]
    fn test_post_frame_stack_slot_spill_reload_memops_select_distinct_proofs() {
        let func = make_func_with_insts(vec![
            inst_with_operands(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::PReg(W16),
                    MachOperand::MemOp {
                        base: X29,
                        offset: -8,
                    },
                ],
            ),
            inst_with_operands(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(X17),
                    MachOperand::MemOp {
                        base: X29,
                        offset: -16,
                    },
                ],
            ),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 2);
        // E0.2: distinct RegAlloc theorems are still selected by the retired
        // mapping, never credited. L07-P2: the walk judges both rows by their
        // instruction-derived obligations instead, and X-OPCODES-P1 records
        // each word's memory-effect decomposition after that reason.
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.registry_name_lookup_count(), 0);
        assert_eq!(report.instruction_derived_count(), 2);
        assert_eq!(report.memory_effect_count(), 2);

        let (query, category) = instruction_derived_over_retired_query(&func, &report, 0);
        assert_eq!(category, ProofCategory::RegAlloc);
        let theorem = registry_theorem(query, category);
        assert!(
            theorem.name.contains("spill/reload semantic roundtrip"),
            "unexpected post-frame reload theorem: {}",
            theorem.name
        );

        let (query, category) = instruction_derived_over_retired_query(&func, &report, 1);
        assert_eq!(category, ProofCategory::RegAlloc);
        let theorem = registry_theorem(query, category);
        assert!(
            theorem.name.contains("spill offset non-interference"),
            "unexpected post-frame spill theorem: {}",
            theorem.name
        );
    }

    #[test]
    fn test_generated_stack_slot_spill_stores_select_non_interference() {
        let func = make_func_with_insts(vec![
            inst_with_operands(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(X16),
                    MachOperand::StackSlot(StackSlotId(0)),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::StrRI,
                vec![MachOperand::PReg(W17), MachOperand::FrameIndex(FrameIdx(1))],
            ),
            inst_with_operands(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(X17),
                    MachOperand::MemOp {
                        base: X29,
                        offset: -16,
                    },
                ],
            ),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 3);
        // E0.2: every spill store still selects the non-interference theorem,
        // which is not credited. The two frame-placeholder stores report it;
        // the frame-resolved store is judged by its instruction-derived
        // obligation (L07-P2), then its word's memory-effect decomposition
        // (X-OPCODES-P1).
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.registry_name_lookup_count(), 2);
        assert_eq!(report.instruction_derived_count(), 1);
        assert_eq!(report.memory_effect_count(), 1);

        for position in 0..3 {
            let (query, category) = if position < 2 {
                withdrawn_registry_row(&report.instructions[position].result)
            } else {
                let (query, category) = instruction_derived_over_retired_query(&func, &report, 2);
                (query.to_string(), category)
            };
            assert_eq!(category, ProofCategory::RegAlloc);
            let theorem = registry_theorem(&query, category);
            assert!(
                theorem.name.contains("spill offset non-interference"),
                "unexpected generated spill-store theorem: {}",
                theorem.name
            );
        }
    }

    #[test]
    fn test_regular_load_store_operands_stay_memory_proofs() {
        let func = make_func_with_insts(vec![
            inst_with_operands(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                    MachOperand::Imm(0),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::PReg(X1),
                    MachOperand::Imm(0),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(X16),
                    MachOperand::MemOp {
                        base: SP,
                        offset: 0,
                    },
                ],
            ),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 3);
        assert_eq!(report.verified_count(), 0);
        // Generic Memory queries (E0.2: not credited), no longer reached: the
        // walk judges each row by its instruction-derived obligation (L07-P2).
        for (position, query) in [(0, "load"), (1, "store"), (2, "store")] {
            assert_eq!(
                instruction_derived_over_retired_query(&func, &report, position),
                (query, ProofCategory::Memory)
            );
        }
    }

    #[test]
    fn test_generated_stack_slot_spill_reload_mappings_resolve_typed_check_kind() {
        let db = ProofDatabase::new();
        for (inst, expected_query) in [
            (
                inst_with_operands(
                    AArch64Opcode::LdrRI,
                    vec![
                        MachOperand::PReg(X16),
                        MachOperand::StackSlot(StackSlotId(0)),
                    ],
                ),
                "spill/reload semantic roundtrip",
            ),
            (
                inst_with_operands(
                    AArch64Opcode::StrRI,
                    vec![MachOperand::PReg(X17), MachOperand::FrameIndex(FrameIdx(1))],
                ),
                "spill offset non-interference",
            ),
        ] {
            let (query, category) = FunctionVerifier::inst_to_proof_query(&inst)
                .expect("generated stack-slot spill/reload must map to a proof query");
            assert_eq!(query, expected_query);
            let query = query.to_lowercase();
            let proof = db
                .by_category(category)
                .into_iter()
                .find(|p| p.obligation.name.to_lowercase().contains(&query))
                .unwrap_or_else(|| {
                    panic!("no proof matching {query:?} for stack-slot spill/reload")
                });
            assert_eq!(
                proof.obligation.category,
                Some(category.transval_check_kind())
            );
        }
    }

    // =======================================================================
    // 31. Generated STP spill scalarization stores are verified
    // =======================================================================

    #[test]
    fn test_generated_stp_spill_scalarization_stores_name_memory_theorems() {
        let func = make_func_with_insts(vec![
            inst_with_operands(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::PReg(X16),
                    MachOperand::StackSlot(StackSlotId(2)),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::AddRI,
                vec![
                    MachOperand::PReg(X16),
                    MachOperand::PReg(X16),
                    MachOperand::Imm(32),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::PReg(X17),
                    MachOperand::StackSlot(StackSlotId(0)),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(X17),
                    MachOperand::PReg(X16),
                    MachOperand::Imm(0),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::PReg(X17),
                    MachOperand::StackSlot(StackSlotId(1)),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(X17),
                    MachOperand::PReg(X16),
                    MachOperand::Imm(8),
                ],
            ),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 6);
        // E0.2: no row is credited. The ADD reconstructs but is sampled; the
        // frame-placeholder loads only name registry theorems, and the stores
        // are judged by their instruction-derived obligations (L07-P2), then
        // their words' memory-effect decompositions (X-OPCODES-P1).
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.unverified_count(), 6);
        assert_sampled_uncredited(&report.instructions[1].result, "Iadd");
        assert_eq!(report.registry_name_lookup_count(), 3);
        assert_eq!(report.instruction_derived_count(), 2);
        assert_eq!(report.memory_effect_count(), 2);

        // #62: the dedicated "stp spill scalarization" FrameLayout proof was a
        // degenerate X==X and was RETRACTED, so the two scalarized stores reach
        // the ordinary store (Memory) query rather than the dedicated one.
        for position in [3, 5] {
            let (_, category) = instruction_derived_over_retired_query(&func, &report, position);
            assert_eq!(category, ProofCategory::Memory);
        }
    }

    #[test]
    fn test_generated_stp_spill_scalarization_mapping_resolves_typed_check_kind() {
        let db = ProofDatabase::new();
        let func = make_func_with_insts(vec![
            inst_with_operands(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::PReg(X16),
                    MachOperand::StackSlot(StackSlotId(2)),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::PReg(X17),
                    MachOperand::StackSlot(StackSlotId(0)),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(X17),
                    MachOperand::PReg(X16),
                    MachOperand::Imm(0),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::PReg(X17),
                    MachOperand::StackSlot(StackSlotId(1)),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(X17),
                    MachOperand::PReg(X16),
                    MachOperand::Imm(8),
                ],
            ),
        ]);
        let block = &func.blocks[0].insts;
        let inst = &func.insts[block[4].0 as usize];
        let (query, category) =
            FunctionVerifier::inst_to_proof_query_in_block(&func, block, 4, inst)
                .expect("scalarized STP spill store must still map to its ordinary store proof");
        // #62: the dedicated "stp spill scalarization" FrameLayout proof was a
        // degenerate X==X and was RETRACTED, so the scalarized store falls through
        // to its ordinary opcode-level store mapping (Memory).
        assert_eq!(query, "store");
        assert_eq!(category, ProofCategory::Memory);
        let _ = &db;
    }

    #[test]
    fn test_plain_store_overclassification_negative_stays_memory_proof() {
        let func = make_func_with_insts(vec![
            inst_with_operands(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(X17),
                    MachOperand::PReg(X16),
                    MachOperand::Imm(0),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(X17),
                    MachOperand::PReg(X16),
                    MachOperand::Imm(8),
                ],
            ),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 2);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.unverified_count(), 2);

        for position in 0..2 {
            // The generic Memory `"store"` query, never the STP scalarization
            // query (E0.2: neither is credit); the walk judges the row by its
            // instruction-derived obligation (L07-P2).
            assert_eq!(
                instruction_derived_over_retired_query(&func, &report, position),
                ("store", ProofCategory::Memory)
            );
        }

        let (query, category) = FunctionVerifier::inst_to_proof_query(&func.insts[0])
            .expect("plain StrRI must keep the generic store query");
        assert_eq!(query, "store");
        assert_eq!(category, ProofCategory::Memory);
    }

    #[test]
    fn test_non_stp_spill_scalarization_str_stays_memory_proof() {
        let func = make_func_with_insts(vec![
            inst_with_operands(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(X17),
                    MachOperand::PReg(X16),
                    MachOperand::Imm(16),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(X16),
                    MachOperand::PReg(X17),
                    MachOperand::Imm(8),
                ],
            ),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 2);
        assert_eq!(report.verified_count(), 0);

        // Both would reach the generic Memory `"store"` query (E0.2: not
        // credited); the walk judges them by their instruction-derived
        // obligations (L07-P2).
        for position in 0..2 {
            assert_eq!(
                instruction_derived_over_retired_query(&func, &report, position),
                ("store", ProofCategory::Memory)
            );
        }
    }

    // =======================================================================
    // 32. Generated emergency spill-slot address instructions are verified
    // =======================================================================

    #[test]
    fn test_generated_emergency_spill_slot_address_memops_name_memory_theorems() {
        let func = make_func_with_insts(vec![
            inst_with_operands(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::MemOp {
                        base: X16,
                        offset: 0,
                    },
                ],
            ),
            inst_with_operands(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(X16),
                    MachOperand::MemOp {
                        base: X17,
                        offset: 0,
                    },
                ],
            ),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 2);
        assert_eq!(report.verified_count(), 0);

        // #62: the dedicated "emergency spill slot address via X16" FrameLayout
        // proof was a degenerate X==X and was RETRACTED, so the X16-base
        // load/store reach the ordinary Memory load/store queries. E0.2: those
        // name representative theorems and are not credited.
        // L07-P2: the walk judges them by their instruction-derived obligations.
        for position in 0..2 {
            let (_, category) = instruction_derived_over_retired_query(&func, &report, position);
            assert_eq!(category, ProofCategory::Memory);
        }
    }

    #[test]
    fn test_nonzero_or_nonscratch_memops_stay_memory_proofs() {
        let func = make_func_with_insts(vec![
            inst_with_operands(
                AArch64Opcode::LdrRI,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::MemOp {
                        base: X16,
                        offset: 8,
                    },
                ],
            ),
            inst_with_operands(
                AArch64Opcode::StrRI,
                vec![
                    MachOperand::PReg(X0),
                    MachOperand::MemOp {
                        base: X1,
                        offset: 0,
                    },
                ],
            ),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 2);
        assert_eq!(report.verified_count(), 0);
        // Generic Memory queries (E0.2: not credited), no longer reached: the
        // walk judges both rows by their instruction-derived obligations
        // (L07-P2).
        for (position, query) in [(0, "load"), (1, "store")] {
            assert_eq!(
                instruction_derived_over_retired_query(&func, &report, position),
                (query, ProofCategory::Memory)
            );
        }
    }

    #[test]
    fn test_generated_emergency_spill_slot_mapping_resolves_typed_check_kind() {
        // #62: the dedicated "emergency spill slot address via X16" FrameLayout proof
        // was a degenerate X==X and was RETRACTED, so the special emergency-spill
        // query now returns None. The StrRI falls through to its ordinary opcode-level
        // store mapping (Memory) rather than the dedicated FrameLayout proof.
        let inst = inst_with_operands(
            AArch64Opcode::StrRI,
            vec![
                MachOperand::PReg(X16),
                MachOperand::MemOp {
                    base: X17,
                    offset: 0,
                },
            ],
        );
        let (query, category) = FunctionVerifier::inst_to_proof_query(&inst)
            .expect("StrRI must still map to its ordinary store proof");
        assert_eq!(query, "store");
        assert_eq!(category, ProofCategory::Memory);
    }

    // =======================================================================
    // 33. Report counts are accurate
    // =======================================================================

    #[test]
    fn test_report_verified_count() {
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::AddRR), // registry candidate: unverified (E0.2)
            inst(AArch64Opcode::SubRR), // registry candidate: unverified (E0.2)
            inst(AArch64Opcode::MulRR), // registry candidate: unverified (E0.2)
            inst(AArch64Opcode::Neg),   // registry candidate: unverified (E0.2)
            inst(AArch64Opcode::Phi),   // skipped
            inst(AArch64Opcode::Ret),   // unverified (#62: RET proof retracted)
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 6);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.skipped_count(), 1);
        assert_eq!(report.unverified_count(), 5);
        assert_eq!(report.registry_name_lookup_count(), 4);
        assert_eq!(report.failed_count(), 0);
    }

    // =======================================================================
    // 33. with_config constructor
    // =======================================================================

    #[test]
    fn test_with_config() {
        // The configured sample count reaches the discharge: the sampled 64-bit
        // ADD reports exactly the configured count (and is not credited).
        let config = VerificationConfig::with_sample_count(1_000);
        let verifier = FunctionVerifier::with_config(config);
        let func = make_func_with_insts(vec![
            representative_reconstructable_inst(AArch64Opcode::AddRR).unwrap(),
        ]);
        let report = verifier.verify(&func);
        assert_eq!(report.verified_count(), 0);
        assert_sampled_uncredited(&report.instructions[0].result, "1000 sampled inputs");
    }

    // =======================================================================
    // 34. FP ops coverage
    // =======================================================================

    #[test]
    fn test_fp_ops_name_theorems_but_are_uncredited() {
        for opcode in [
            AArch64Opcode::FaddRR,
            AArch64Opcode::FsubRR,
            AArch64Opcode::FmulRR,
            AArch64Opcode::FnegRR,
        ] {
            assert_registry_candidate_with_theorem(opcode, ProofCategory::FloatingPoint, "");
        }
    }

    // =======================================================================
    // 35. opcode_to_proof_query returns None for unmapped
    // =======================================================================

    #[test]
    fn test_opcode_to_proof_query_none() {
        // Csinv has no proof mapping (a genuine gap). The INDIRECT branches
        // Blr/Br have no DB proof query either — their register target is
        // covered-elsewhere (is_covered_elsewhere_indirect_branch), not by a
        // per-instruction obligation. (The DIRECT branches B/Bl/BL DO now have a
        // query — the BRANCH26 proof; see test_opcode_to_proof_query_some.)
        assert!(FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Csinv).is_none());
        assert!(FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Blr).is_none());
        assert!(FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Br).is_none());
    }

    // =======================================================================
    // 36. opcode_to_proof_query returns Some for mapped
    // =======================================================================

    #[test]
    fn test_opcode_to_proof_query_some() {
        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::AddRR).unwrap();
        assert_eq!(query, "add");
        assert_eq!(cat, ProofCategory::Arithmetic);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Madd).unwrap();
        assert_eq!(query, "madd_rr");
        assert_eq!(cat, ProofCategory::Arithmetic);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Msub).unwrap();
        assert_eq!(query, "msub_rr");
        assert_eq!(cat, ProofCategory::Arithmetic);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Tst).unwrap();
        assert_eq!(query, "tst packed nzcv");
        assert_eq!(cat, ProofCategory::CmpCombine);

        // Direct branch/call B/Bl/BL -> the BRANCH26 call-relocation proof.
        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Bl).unwrap();
        assert_eq!(query, "branch26 bl == s+a");
        assert_eq!(cat, ProofCategory::MachOEmission);
        // ADRP/ADD address materialization -> the PAGE21/PAGEOFF12 proofs.
        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Adrp).unwrap();
        assert_eq!(query, "arm64_reloc_page21 adrp == page");
        assert_eq!(cat, ProofCategory::MachOEmission);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::SDiv).unwrap();
        assert_eq!(query, "sdiv");
        assert_eq!(cat, ProofCategory::Division);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::LdrRI).unwrap();
        assert_eq!(query, "load");
        assert_eq!(cat, ProofCategory::Memory);

        // #62: RET's only proof was the degenerate "RET branches to LR" X==X,
        // retracted -> None.
        assert!(FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Ret).is_none());

        // Neither an opcode nor an SP/X29-shaped operand list authenticates
        // the pair's source memory, both transfers and any base writeback.
        for opcode in [
            AArch64Opcode::StpRI,
            AArch64Opcode::LdpRI,
            AArch64Opcode::StpPreIndex,
            AArch64Opcode::LdpPostIndex,
            AArch64Opcode::NeonLdpQPost,
            AArch64Opcode::NeonStpQPost,
        ] {
            assert!(FunctionVerifier::opcode_to_proof_query(opcode).is_none());
        }

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Sxtb).unwrap();
        assert_eq!(query, "sextend_i8_to_i32");
        assert_eq!(cat, ProofCategory::ExtensionTruncation);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Sxth).unwrap();
        assert_eq!(query, "sextend_i16_to_i32");
        assert_eq!(cat, ProofCategory::ExtensionTruncation);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Sxtw).unwrap();
        assert_eq!(query, "sextend_i32_to_i64");
        assert_eq!(cat, ProofCategory::ExtensionTruncation);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Uxtb).unwrap();
        assert_eq!(query, "uextend_i8_to_i32");
        assert_eq!(cat, ProofCategory::ExtensionTruncation);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Uxth).unwrap();
        assert_eq!(query, "uextend_i16_to_i32");
        assert_eq!(cat, ProofCategory::ExtensionTruncation);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Uxtw).unwrap();
        assert_eq!(query, "uextend_i32_to_i64");
        assert_eq!(cat, ProofCategory::ExtensionTruncation);

        // GPR copy aliases (MOVWrr/MOVXrr): the degenerate "CopyProp: COPY(x)==x"
        // proof was retracted in #62, so they have NO opcode-wide mapping; a
        // concrete instance binds its decoded-word form (MovWrr/MovXrr).
        assert!(FunctionVerifier::opcode_to_proof_query(AArch64Opcode::MOVWrr).is_none());
        assert!(FunctionVerifier::opcode_to_proof_query(AArch64Opcode::MOVXrr).is_none());

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Movz).unwrap();
        assert_eq!(query, "movz #imm16, lsl #0");
        assert_eq!(cat, ProofCategory::ConstantMaterialization);

        // MOVK must NEVER receive opcode-WIDE credit (that inheritance is the
        // retracted #62 class: an illegal W-form LSL #32/#48 could inherit an
        // X-form slot's proof). The SOUND path is the per-form binding in
        // `operand_sensitive_or_opcode_query`, which routes each concrete
        // (width, shift) through `const_materialize_proofs::movk_halfword_query`.
        assert!(
            FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Movk).is_none(),
            "MOVK must NEVER be credited opcode-wide (its hw0 idempotence theorem is not a \
             general lowering proof); per-(width, halfword) credit comes only from the \
             operand-sensitive splice binding via movk_halfword_query"
        );

        assert!(
            FunctionVerifier::opcode_to_proof_query(AArch64Opcode::Movn).is_none(),
            "MOVN binding is width-sensitive and cannot be credited opcode-wide"
        );

        let (query, cat) =
            FunctionVerifier::opcode_to_proof_query(AArch64Opcode::FcvtzsRR).unwrap();
        assert_eq!(query, "fcvtzs");
        assert_eq!(cat, ProofCategory::FpConversion);

        let (query, cat) =
            FunctionVerifier::opcode_to_proof_query(AArch64Opcode::FcvtzuRR).unwrap();
        assert_eq!(query, "fcvtzu");
        assert_eq!(cat, ProofCategory::FpConversion);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::ScvtfRR).unwrap();
        assert_eq!(query, "scvtf");
        assert_eq!(cat, ProofCategory::FpConversion);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::UcvtfRR).unwrap();
        assert_eq!(query, "ucvtf");
        assert_eq!(cat, ProofCategory::FpConversion);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::FcvtSD).unwrap();
        assert_eq!(query, "fpromote_f64_f32");
        assert_eq!(cat, ProofCategory::FpConversion);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::FcvtDS).unwrap();
        assert_eq!(query, "fdemote_f32_f64");
        assert_eq!(cat, ProofCategory::FpConversion);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::MOVZWi).unwrap();
        assert_eq!(query, "movz #imm16, lsl #0");
        assert_eq!(cat, ProofCategory::ConstantMaterialization);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::MOVZXi).unwrap();
        assert_eq!(query, "movz #imm16, lsl #0");
        assert_eq!(cat, ProofCategory::ConstantMaterialization);
    }

    // =======================================================================
    // 37. Report with function signature
    // =======================================================================

    #[test]
    fn test_function_with_signature() {
        let sig = Signature::new(vec![Type::I64, Type::I64], vec![Type::I64]);
        let mut func = MachFunction::new("add_two".to_string(), sig);
        func.insts.push(inst(AArch64Opcode::AddRR));
        func.blocks[0].insts.push(InstId(0));
        func.insts.push(inst(AArch64Opcode::Ret));
        func.blocks[0].insts.push(InstId(1));

        let report = verify_function(&func);
        assert_eq!(report.function_name, "add_two");
        assert_eq!(report.total(), 2);
        // The operand-less ADD is a registry candidate (E0.2); RET is
        // Unverified (#62: RET X==X retracted).
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.unverified_count(), 2);
        assert_eq!(report.registry_name_lookup_count(), 1);
    }

    // =======================================================================
    // 38. Trap rows are no longer skipped (L04-P12)
    // =======================================================================

    /// The unconditional traps decode to their single `BRK` word
    /// (`aarch64_trap_expansion`), but an unbound BRK and the bare trap
    /// pseudos used to be skipped, hence promotable. The trap-guard analysis
    /// now refuses each by name: none is a recorded guard window, a source
    /// `Trap`, a BRK after a noreturn call or the stack-limit trap
    /// (`aarch64_trap_guard`).
    #[test]
    fn test_unbound_trap_rows_are_refused_not_skipped() {
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::Brk),
            inst(AArch64Opcode::TrapOverflow),
            inst(AArch64Opcode::TrapBoundsCheck),
            inst(AArch64Opcode::TrapNull),
            inst(AArch64Opcode::TrapDivZero),
            inst(AArch64Opcode::TrapShiftRange),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.skipped_count(), 0);
        assert_eq!(report.unverified_count(), 6);
        for ir in &report.instructions {
            assert!(
                matches!(
                    &ir.result,
                    InstructionVerificationResult::Unverified { reason }
                        if reason.starts_with(crate::aarch64_trap_guard::TRAP_GUARD_REFUSED)
                ),
                "trap opcode {:?} must be refused by name, got {:?}",
                ir.opcode,
                ir.result
            );
        }
        assert!(!report.emitted_opcode_inventory().is_promotable());
        assert!(
            FunctionVerifier::inst_to_proof_query(&inst(AArch64Opcode::Brk)).is_none(),
            "BRK is judged by the trap-guard analysis, not a proof query"
        );
    }

    /// L04-P12: a conditional trap carrier is judged by its stated expansion,
    /// never skipped. A holding expansion is uncredited without a Clean-checked
    /// replay; a carrier outside the model is refused by name.
    #[test]
    fn trap_carriers_are_judged_by_their_expansion_not_skipped() {
        use crate::aarch64_trap_expansion::TRAP_EXPANSION_IS_NOT_CREDIT;
        use trust_cg_ir::RegClass;
        let v = |id, class| MachOperand::VReg(trust_cg_ir::VReg::new(id, class));
        let tag = |op| MachOperand::Imm(trust_cg_ir::overflow_tag::pack_overflow_tag(op, 64));
        use trust_cg_ir::overflow_tag::OverflowOp;
        let carriers = vec![
            inst_with_operands(AArch64Opcode::TrapNullIfZero, vec![v(0, RegClass::Gpr64)]),
            inst_with_operands(
                AArch64Opcode::TrapDivZeroIfZero,
                vec![v(1, RegClass::Gpr32)],
            ),
            inst_with_operands(
                AArch64Opcode::TrapBoundsCheckExact,
                vec![
                    v(2, RegClass::Gpr64),
                    v(3, RegClass::Gpr64),
                    MachOperand::Imm(0x1_0000),
                ],
            ),
            inst_with_operands(
                AArch64Opcode::TrapShiftRangeIfOOB,
                vec![v(4, RegClass::Gpr64), MachOperand::Imm(64)],
            ),
            inst_with_operands(
                AArch64Opcode::TrapOverflowExact,
                vec![
                    v(5, RegClass::Gpr64),
                    v(6, RegClass::Gpr64),
                    tag(OverflowOp::UnsignedMul),
                ],
            ),
        ];
        let report = verify_function(&make_func_with_insts(carriers));
        assert_eq!(report.skipped_count(), 0);
        assert_eq!(report.failed_count(), 0);
        for row in &report.instructions {
            match &row.result {
                InstructionVerificationResult::Unverified { reason } => assert!(
                    reason.starts_with(TRAP_EXPANSION_IS_NOT_CREDIT)
                        && reason.contains("decided in-process for every input")
                        && reason.contains("no live replay"),
                    "{:?}: {reason}",
                    row.opcode
                ),
                other => panic!("{:?}: {other:?}", row.opcode),
            }
        }
        assert!(!report.emitted_opcode_inventory().is_promotable());

        // Outside the model: refused by name, still not skipped.
        let malformed = verify_function(&make_func_with_insts(vec![inst(
            AArch64Opcode::TrapShiftRangeIfOOB,
        )]));
        match &malformed.instructions[0].result {
            InstructionVerificationResult::Unverified { reason } => {
                assert!(reason.contains("not a modeled trap carrier"), "{reason}")
            }
            other => panic!("{other:?}"),
        }
    }

    /// A post-allocation function whose `CBNZ x0, #2; BRK #1` is recorded as
    /// the expansion of `carrier`, followed by `tail`.
    fn recorded_null_guard(
        carrier: MachInst,
        words: Vec<MachInst>,
        tail: Vec<MachInst>,
    ) -> MachFunction {
        let count = words.len();
        let mut func = make_func_with_insts(words.into_iter().chain(tail).collect());
        func.trap_expansions.push(trust_cg_ir::TrapExpansionRecord {
            carrier,
            insts: (0..count as u32).map(InstId).collect(),
        });
        func
    }

    #[test]
    fn recorded_trap_expansions_are_judged_by_their_words() {
        use trust_cg_ir::aarch64_regs::{X0, X1};
        let null_x0 =
            inst_with_operands(AArch64Opcode::TrapNullIfZero, vec![MachOperand::PReg(X0)]);
        let cbnz = |reg| {
            inst_with_operands(
                AArch64Opcode::Cbnz,
                vec![MachOperand::PReg(reg), MachOperand::Imm(2)],
            )
        };
        let brk = || inst(AArch64Opcode::Brk);
        let ret = || inst(AArch64Opcode::Ret);

        // The faithful expansion: the BRK row carries the expansion's verdict.
        let report = verify_function(&recorded_null_guard(
            null_x0.clone(),
            vec![cbnz(X0), brk()],
            vec![ret()],
        ));
        match &report.instructions[1].result {
            InstructionVerificationResult::Unverified { reason } => assert!(
                reason.starts_with(crate::aarch64_trap_expansion::TRAP_EXPANSION_IS_NOT_CREDIT),
                "{reason}"
            ),
            other => panic!("{other:?}"),
        }
        assert!(!report.emitted_opcode_inventory().is_promotable());

        // The expansion tests x1 while the carrier names x0: refuted.
        let report = verify_function(&recorded_null_guard(
            null_x0.clone(),
            vec![cbnz(X1), brk()],
            vec![ret()],
        ));
        assert!(
            matches!(&report.instructions[1].result, InstructionVerificationResult::Failed { detail, .. } if detail.contains("counterexample")),
            "{:?}",
            report.instructions[1].result
        );

        // A NOP between the branch and the trap: no longer the recorded unit.
        let mut func = make_func_with_insts(vec![cbnz(X0), inst(AArch64Opcode::Nop), brk(), ret()]);
        func.trap_expansions.push(trust_cg_ir::TrapExpansionRecord {
            carrier: null_x0,
            insts: vec![InstId(0), InstId(2)],
        });
        let report = verify_function(&func);
        assert!(
            matches!(&report.instructions[2].result, InstructionVerificationResult::Failed { detail, .. } if detail.contains("contiguous")),
            "{:?}",
            report.instructions[2].result
        );
    }

    #[test]
    fn a_flag_setting_expansion_must_leave_nzcv_dead() {
        use trust_cg_ir::aarch64_regs::{X2, X3};
        let carrier = inst_with_operands(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![
                MachOperand::PReg(X2),
                MachOperand::PReg(X2),
                MachOperand::Imm(10),
            ],
        );
        let expansion = || {
            vec![
                inst_with_operands(
                    AArch64Opcode::CmpRI,
                    vec![MachOperand::PReg(X2), MachOperand::Imm(10)],
                ),
                inst_with_operands(
                    AArch64Opcode::BCond,
                    vec![MachOperand::Imm(3), MachOperand::Imm(2)],
                ),
                inst(AArch64Opcode::Brk),
            ]
        };
        // A later CSET reads the flags the expansion's CMP left.
        let reader = inst_with_operands(
            AArch64Opcode::CSet,
            vec![MachOperand::PReg(X3), MachOperand::Imm(0)],
        );
        let report = verify_function(&recorded_null_guard(
            carrier.clone(),
            expansion(),
            vec![reader],
        ));
        assert!(
            matches!(&report.instructions[2].result, InstructionVerificationResult::Failed { detail, .. } if detail.contains("NZCV")),
            "{:?}",
            report.instructions[2].result
        );
        // A later CMP overwrites them first: the expansion's verdict stands.
        let writer = inst_with_operands(
            AArch64Opcode::CmpRR,
            vec![MachOperand::PReg(X3), MachOperand::PReg(X2)],
        );
        let report = verify_function(&recorded_null_guard(carrier, expansion(), vec![writer]));
        assert!(
            matches!(&report.instructions[2].result, InstructionVerificationResult::Unverified { reason } if reason.contains("holds")),
            "{:?}",
            report.instructions[2].result
        );
    }

    /// The NZCV a flag-setting expansion leaves flows into the successors of
    /// the block it ends. Only a successor whose every path writes NZCV before
    /// reading it lets the verdict stand; a flag reader there (directly or
    /// after a neutral instruction) or an opaque pseudo before any writer
    /// leaves NZCV not provably dead, and the row uncredited whatever the
    /// replay would say.
    #[test]
    fn a_flag_setting_expansion_must_leave_nzcv_dead_in_its_successors() {
        use trust_cg_ir::aarch64_regs::{X2, X3};
        let carrier = inst_with_operands(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![
                MachOperand::PReg(X2),
                MachOperand::PReg(X2),
                MachOperand::Imm(10),
            ],
        );
        // Block 0 is exactly the expansion; block 1 follows it.
        let build = |successor: Vec<MachInst>| {
            let mut func = make_empty_func();
            let entry = func.entry;
            let next = func.create_block();
            let expansion = [
                inst_with_operands(
                    AArch64Opcode::CmpRI,
                    vec![MachOperand::PReg(X2), MachOperand::Imm(10)],
                ),
                inst_with_operands(
                    AArch64Opcode::BCond,
                    vec![MachOperand::Imm(3), MachOperand::Imm(2)],
                ),
                inst(AArch64Opcode::Brk),
            ];
            let ids: Vec<InstId> = expansion
                .into_iter()
                .map(|member| {
                    let id = func.push_inst(member);
                    func.append_inst(entry, id);
                    id
                })
                .collect();
            for member in successor.into_iter().chain([inst(AArch64Opcode::Ret)]) {
                let id = func.push_inst(member);
                func.append_inst(next, id);
            }
            func.block_mut(entry).succs = vec![next];
            func.trap_expansions.push(trust_cg_ir::TrapExpansionRecord {
                carrier: carrier.clone(),
                insts: ids,
            });
            func
        };
        let brk_row = |func: &MachFunction| {
            verify_function(func)
                .instructions
                .into_iter()
                .find(|row| row.opcode == InstructionOpcode::AArch64(AArch64Opcode::Brk))
                .expect("the BRK row")
                .result
        };
        let reader = inst_with_operands(
            AArch64Opcode::CSet,
            vec![MachOperand::PReg(X3), MachOperand::Imm(0)],
        );
        let writer = inst_with_operands(
            AArch64Opcode::CmpRR,
            vec![MachOperand::PReg(X3), MachOperand::PReg(X2)],
        );
        let not_dead = |row: &InstructionVerificationResult| {
            matches!(row, InstructionVerificationResult::Unverified { reason }
                if reason.contains("NZCV is not provably dead"))
        };
        let row = brk_row(&build(vec![reader.clone()]));
        assert!(not_dead(&row), "{row:?}");
        // The reader is in the successor after a neutral instruction.
        let neutral = inst_with_operands(
            AArch64Opcode::MovR,
            vec![MachOperand::PReg(X3), MachOperand::PReg(X2)],
        );
        let row = brk_row(&build(vec![neutral, reader.clone()]));
        assert!(not_dead(&row), "{row:?}");
        let row = brk_row(&build(vec![inst(AArch64Opcode::Retain), writer.clone()]));
        assert!(not_dead(&row), "{row:?}");
        // A writer first: the expansion's own verdict (uncredited here, with
        // no live replay) stands.
        let row = brk_row(&build(vec![writer, reader]));
        assert!(
            matches!(&row, InstructionVerificationResult::Unverified { reason }
                if reason.starts_with(crate::aarch64_trap_expansion::TRAP_EXPANSION_IS_NOT_CREDIT)),
            "{row:?}"
        );
    }

    /// A holding conditional trap row is replayed through the verification
    /// request, under an enforced source-bound replay policy only: the
    /// request's refusals and its AY decide the row, never another request's
    /// answer or the ambient environment.
    #[test]
    fn trap_rows_replay_through_the_verification_request() {
        use crate::aarch64_trap_expansion::TRAP_EXPANSION_IS_NOT_CREDIT;
        use trust_cg_ir::aarch64_regs::X0;
        use trust_cg_ir::provenance::{LoweringProvenance, SourceInstId};
        use trust_cg_lower::instructions::{Block, Instruction, Opcode as LirOpcode, Value};
        // The window binds to a source `GuardNull v0` through its TV-1 stamp
        // (the trap-guard layer refuses an unstamped carrier before any
        // replay), so the replay route itself decides the BRK row.
        let mut lir = tv2_lir_function();
        lir.blocks.get_mut(&Block(0)).expect("block 0").instructions = vec![
            Instruction {
                opcode: LirOpcode::GuardNull { obligation: None },
                args: vec![Value(0)],
                results: vec![],
            },
            Instruction {
                opcode: LirOpcode::Return,
                args: vec![Value(0)],
                results: vec![],
            },
        ];
        let mut func = recorded_null_guard(
            inst_with_operands(AArch64Opcode::TrapNullIfZero, vec![MachOperand::PReg(X0)]),
            vec![
                inst_with_operands(
                    AArch64Opcode::Cbnz,
                    vec![MachOperand::PReg(X0), MachOperand::Imm(2)],
                ),
                inst(AArch64Opcode::Brk),
            ],
            vec![inst(AArch64Opcode::Ret)],
        );
        let digest = lir.blocks[&Block(0)].instructions[0].lowering_digest();
        func.set_inst_lowering_provenance(
            InstId(0),
            LoweringProvenance::SourceInst {
                id: SourceInstId { block: 0, index: 0 },
                digest,
                trust_ir_inst: None,
            },
        );
        let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
        let brk_reason = |request: &crate::FunctionVerificationRequest| {
            let report = verifier.verify_with_request(&func, Some(&lir), request);
            let report = report.report();
            assert!(report.precondition_failure.is_none(), "{report:?}");
            match &report.instructions[1].result {
                InstructionVerificationResult::Unverified { reason } => {
                    assert!(reason.starts_with(TRAP_EXPANSION_IS_NOT_CREDIT), "{reason}");
                    reason.clone()
                }
                other => panic!("{other:?}"),
            }
        };
        let recording = verifier
            .capture_request_with_mode(ProvenanceXCheckMode::Enforce)
            .captured_while_recording();
        let no_ay = trust_cg_process_env::with_env_edits(|env| {
            env.set("AY_SOLVER_PATH", "/nonexistent/trap-row-ay");
            env.set("TCG_EXTERNAL_CLEAN_CHECKER", "/nonexistent/trap-row-clean");
            env.remove("TCG_REFINE_SOLVER");
            verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce)
        });
        for _ in 0..2 {
            let reason = brk_reason(&recording);
            assert!(reason.contains("tier-0 recorder is armed"), "{reason}");
            let reason = brk_reason(&no_ay);
            assert!(reason.contains("no AY solver was admitted"), "{reason}");
        }
        // Outside an enforced replay policy, nothing is replayed.
        let warn = verifier.capture_request_with_mode(ProvenanceXCheckMode::Warn);
        let reason = brk_reason(&warn);
        assert!(
            reason.contains("no live replay (not an enforced source-bound replay policy)"),
            "{reason}"
        );
    }

    // =======================================================================
    // 39. Immediate variants map to same category
    // =======================================================================

    #[test]
    fn test_immediate_variants() {
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::AddRI),
            inst(AArch64Opcode::SubRI),
            inst(AArch64Opcode::CmpRI),
        ]);
        let report = verify_function(&func);
        // Operand-less immediate forms only name registry theorems (E0.2).
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.registry_name_lookup_count(), 3);
    }

    // =======================================================================
    // TV-2: provenance cross-check (see crate::provenance_xcheck)
    // =======================================================================

    /// LIR function named `test_func` (matching [`make_empty_func`]) with
    /// block 0 = `[Iadd, Imul, Return]`.
    fn tv2_lir_function() -> trust_cg_lower::Function {
        use trust_cg_lower::function::{BasicBlock, Signature as LirSignature};
        use trust_cg_lower::instructions::{Block, Instruction, Opcode as LirOpcode, Value};
        use trust_cg_lower::types::Type as LirType;

        let mut lir = trust_cg_lower::Function::new(
            "test_func",
            LirSignature {
                params: vec![LirType::I64, LirType::I64],
                returns: vec![LirType::I64],
            },
        );
        let block = Block(0);
        lir.block_order.push(block);
        lir.blocks.insert(
            block,
            BasicBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: LirOpcode::Iadd,
                        args: vec![Value(0), Value(1)],
                        results: vec![Value(2)],
                    },
                    Instruction {
                        opcode: LirOpcode::Imul,
                        args: vec![Value(2), Value(1)],
                        results: vec![Value(3)],
                    },
                    Instruction {
                        opcode: LirOpcode::Return,
                        args: vec![Value(3)],
                        results: vec![],
                    },
                ],
                source_locs: vec![],
            },
        );
        lir
    }

    /// LIR function named `test_func` whose first instruction is one exact
    /// signed/unsigned 64-bit division. Used to pin the fact that TV-2's
    /// `IntDiv` class does not itself distinguish Sdiv from Udiv.
    fn tv2_div_lir_function(
        opcode: trust_cg_lower::instructions::Opcode,
    ) -> trust_cg_lower::Function {
        use trust_cg_lower::function::{BasicBlock, Signature as LirSignature};
        use trust_cg_lower::instructions::{Block, Instruction, Opcode as LirOpcode, Value};
        use trust_cg_lower::types::Type as LirType;

        assert!(matches!(opcode, LirOpcode::Sdiv | LirOpcode::Udiv));
        let mut lir = trust_cg_lower::Function::new(
            "test_func",
            LirSignature {
                params: vec![LirType::I64, LirType::I64],
                returns: vec![LirType::I64],
            },
        );
        let block = Block(0);
        lir.block_order.push(block);
        lir.blocks.insert(
            block,
            BasicBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode,
                        args: vec![Value(0), Value(1)],
                        results: vec![Value(2)],
                    },
                    Instruction {
                        opcode: LirOpcode::Return,
                        args: vec![Value(2)],
                        results: vec![],
                    },
                ],
                source_locs: vec![],
            },
        );
        lir
    }

    /// One single-ALU-instruction MachFunction (3-operand `dst, a, b` form)
    /// whose TV-1 sidecar stamps the instruction as lowering the LIR
    /// instruction at `(0, index)`.
    fn tv2_func_with_alu_stamped(
        lir: &trust_cg_lower::Function,
        opcode: AArch64Opcode,
        index: u32,
    ) -> MachFunction {
        use trust_cg_ir::provenance::{LoweringProvenance, SourceInstId};
        use trust_cg_lower::instructions::Block;

        let mut func = make_func_with_insts(vec![inst_with_operands(
            opcode,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
            ],
        )]);
        let src = &lir.blocks[&Block(0)].instructions[index as usize];
        func.set_inst_lowering_provenance(
            InstId(0),
            LoweringProvenance::SourceInst {
                id: SourceInstId { block: 0, index },
                digest: src.lowering_digest(),
                trust_ir_inst: None,
            },
        );
        func
    }

    fn tv2_provenance_failure(report: &FunctionVerificationReport) -> bool {
        report.precondition_failure.is_some()
            || report.instructions.iter().any(|r| {
                matches!(
                    &r.result,
                    InstructionVerificationResult::Failed { proof_name, .. }
                        if proof_name == "provenance-crosscheck (TV-2)"
                )
            })
    }

    #[test]
    fn dangling_instruction_reference_cannot_be_verified_as_empty() {
        let verifier = FunctionVerifier::new();
        let lir = tv2_lir_function();
        for mode in [
            ProvenanceXCheckMode::Off,
            ProvenanceXCheckMode::Warn,
            ProvenanceXCheckMode::Enforce,
        ] {
            let valid = make_empty_func();
            assert!(
                verifier
                    .verify_with_lir_source_and_mode(&valid, Some(&lir), mode)
                    .all_verified()
            );
            for index in [0, u32::MAX] {
                let mut malformed = valid.clone();
                malformed.blocks[0].insts.push(InstId(index));
                let report = verifier.verify_with_lir_source_and_mode(&malformed, Some(&lir), mode);
                assert!(
                    report.has_failures(),
                    "missing instruction {index} was silently omitted in {mode:?}"
                );
                assert!(!report.all_verified());
                assert!(!report.all_genuinely_verified());
                assert_eq!(report.coverage_percent(), 0.0);
                assert_eq!(report.genuine_coverage_percent(), 0.0);
                assert!(!report.emitted_opcode_inventory().is_promotable());
                assert!(report.to_string().contains("instruction reference"));
            }
        }
    }

    #[test]
    fn tv2_aarch64_enforce_rejects_absent_and_mispaired_sources_including_empty() {
        let lir = tv2_lir_function();
        let mut wrong_lir = lir.clone();
        wrong_lir.name = "wrong_source".to_string();
        let verifier = FunctionVerifier::new();
        for func in [
            make_empty_func(),
            tv2_func_with_alu_stamped(&lir, AArch64Opcode::AddRR, 0),
            make_func_with_insts(vec![inst(AArch64Opcode::Nop)]),
        ] {
            for (source, expected) in [
                (
                    None,
                    FunctionVerificationPreconditionFailure::MissingLirSource,
                ),
                (
                    Some(&wrong_lir),
                    FunctionVerificationPreconditionFailure::LirSourceNameMismatch {
                        source_function: wrong_lir.name.clone(),
                    },
                ),
            ] {
                let report = verifier.verify_with_lir_source_and_mode(
                    &func,
                    source,
                    ProvenanceXCheckMode::Enforce,
                );
                assert_eq!(report.precondition_failure.as_ref(), Some(&expected));
                assert!(report.has_failures());
                assert!(!report.all_verified());
                assert!(!report.all_genuinely_verified());
                // No instruction was examined, fabricated, or credited after
                // the function prerequisite failed.
                assert_eq!(report.total(), 0);
                assert_eq!(report.failed_count(), 0);
                assert_eq!(report.genuinely_verified_count(), 0);
                assert_eq!(report.coverage_percent(), 0.0);
                assert_eq!(report.genuine_coverage_percent(), 0.0);
                let inventory = report.emitted_opcode_inventory();
                assert!(inventory.entries.is_empty());
                assert!(!inventory.is_promotable());
                assert_eq!(inventory.precondition_failure.as_ref(), Some(&expected));
                assert!(inventory.promotion_rejection_reason().is_some());
                assert!(report.to_string().contains("Function precondition FAILED"));
            }
        }
    }

    #[test]
    fn tv2_aarch64_warn_and_off_preserve_diagnostic_source_pairing_behavior() {
        let lir = tv2_lir_function();
        let mut wrong_lir = lir.clone();
        wrong_lir.name = "wrong_source".to_string();
        let func = tv2_func_with_alu_stamped(&lir, AArch64Opcode::AddRR, 0);
        let verifier = FunctionVerifier::with_config(VerificationConfig::with_sample_count(16));
        let baseline = verifier.verify_with_lir_source_and_mode(
            &func,
            Some(&lir),
            ProvenanceXCheckMode::Enforce,
        );
        assert!(!baseline.has_failures());
        assert_eq!(baseline.total(), 1);
        assert_eq!(baseline.formally_credited_count(), 0);
        for mode in [ProvenanceXCheckMode::Warn, ProvenanceXCheckMode::Off] {
            for source in [None, Some(&wrong_lir), Some(&lir)] {
                let report = verifier.verify_with_lir_source_and_mode(&func, source, mode);
                assert!(report.precondition_failure.is_none());
                assert!(!report.has_failures());
                assert_eq!(
                    format!("{:?}", report.instructions),
                    format!("{:?}", baseline.instructions),
                    "diagnostic mode {mode:?} must retain its prior instruction results"
                );
            }
        }
    }

    #[test]
    fn tv2_aarch64_source_pairing_does_not_claim_exact_lowering_evidence() {
        let lir = tv2_lir_function();
        // TV-2 permits SUB as a constituent of an Iadd lowering. A present,
        // same-name source is a prerequisite, not exact operation/operand
        // correspondence; this known gap must not earn Formal credit.
        let func = tv2_func_with_alu_stamped(&lir, AArch64Opcode::SubRR, 0);
        let report = FunctionVerifier::with_config(VerificationConfig::with_sample_count(16))
            .verify_with_lir_source_and_mode(&func, Some(&lir), ProvenanceXCheckMode::Enforce);
        assert!(report.precondition_failure.is_none());
        assert!(!tv2_provenance_failure(&report));
        // The 64-bit SUB reconstructs and discharges only by sampling, which is
        // reported and never credited (E0.2).
        assert_eq!(report.sampled_uncredited_count(), 1);
        assert_eq!(report.verified_count(), 0);
        assert_eq!(report.formally_credited_count(), 0);
    }

    /// PINNED TV-2 REFUTATION (aarch64 side): a `MUL` stamped as lowering the
    /// `Iadd` at (0,0) must fail closed when the cross-check is ENFORCED.
    ///
    /// NB: "an ADD stamped as from an Imul" is deliberately NOT used — the
    /// i128 multiply expansion legitimately emits partial-product ADDs stamped
    /// with the Imul anchor (`compatible(IntMul, IntAdd)`); the
    /// unambiguously-wrong direction is an integer MULTIPLY emitted while
    /// lowering an integer ADD (`!compatible(IntAdd, IntMul)`).
    #[test]
    fn tv2_aarch64_mul_stamped_as_iadd_fails_when_enforced() {
        let lir = tv2_lir_function();
        let func = tv2_func_with_alu_stamped(&lir, AArch64Opcode::MulRR, 0);
        let report = FunctionVerifier::new().verify_with_lir_source_and_mode(
            &func,
            Some(&lir),
            ProvenanceXCheckMode::Enforce,
        );
        assert!(
            tv2_provenance_failure(&report),
            "a MUL stamped as lowering an Iadd must fail the provenance cross-check: {:?}",
            report.instructions
        );
    }

    /// The aarch64 DEFAULT is WARN-ONLY (the aarch64 differential corpus
    /// cannot run on the x86 validation host; the enforce flip belongs to the
    /// Apple-Silicon lane): the default public entry point counts and reports
    /// the mismatch but demotes nothing.
    #[test]
    fn tv2_aarch64_default_is_warn_only() {
        let lir = tv2_lir_function();
        let func = tv2_func_with_alu_stamped(&lir, AArch64Opcode::MulRR, 0);
        let hits_before = crate::provenance_xcheck::provenance_xcheck_hit_count();
        let report = FunctionVerifier::new().verify_with_lir_source(&func, Some(&lir));
        assert!(
            !tv2_provenance_failure(&report),
            "aarch64 default must be warn-only until the AS lane validates"
        );
        assert!(
            crate::provenance_xcheck::provenance_xcheck_hit_count() > hits_before,
            "warn-only mode must still count the mismatch"
        );
    }

    /// SOUNDNESS REGRESSION: exact equality between the two trees of a
    /// `Reconstructed` obligation is not, by itself, source-lowering evidence.
    /// The reconstruction's current `SourceOp` is selected from the EMITTED
    /// opcode, so a bad Iadd -> SUB selection self-reconstructs as
    /// `bvsub(a,b) == bvsub(a,b)`. TV-2 deliberately permits IntSub as a
    /// constituent of an IntAdd lowering, and TV-3 does not bind exact source
    /// operands, so neither existing provenance check supplies the missing
    /// exact source/operand authority.
    ///
    /// Keep this end-to-end promotion path non-Formal until such an authority
    /// is enforced. The verifier reports the resulting sampled discharge as
    /// unverified (E0.2); a future local reflexivity shortcut must not turn
    /// this self-attesting wrong-source case into Formal.
    #[test]
    fn reconstructed_identity_cannot_formally_self_attest_wrong_source_opcode() {
        let lir = tv2_lir_function();
        let func = tv2_func_with_alu_stamped(&lir, AArch64Opcode::SubRR, 0);
        let obligation =
            reconstruct_alu_obligation(&func.insts[0]).expect("well-formed SUB must reconstruct");
        assert_eq!(
            obligation.trust_ir_expr, obligation.aarch64_expr,
            "the negative control must exercise the tempting structural-identity case"
        );

        crate::env_lock::with_env_overrides(
            &[("TCG_NO_VERDICT_DB", "1"), ("TCG_REFINE_SOLVER", "0")],
            || {
                let verifier =
                    FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
                let report = verifier.verify_with_lir_source_and_mode(
                    &func,
                    Some(&lir),
                    ProvenanceXCheckMode::Enforce,
                );
                assert_eq!(report.instructions.len(), 1);
                // A self-reconstructed Iadd -> SUB identity must remain
                // non-Formal: sampled, reported, uncredited.
                assert_sampled_uncredited(&report.instructions[0].result, "Isub");
                assert_eq!(report.formally_credited_count(), 0);
            },
        );
    }

    /// A portable proof of the target-reconstructed UDIV theorem is not exact
    /// source-lowering authority. TV-2 intentionally classifies both Sdiv and
    /// Udiv as `IntDiv`, while reconstruction infers Udiv from the emitted
    /// UDIV. Without an exact source-op/type/operand binding, a bad Sdiv→UDIV
    /// selection would otherwise consume the valid UDIV certificate and earn
    /// Formal credit. Keep both the faithful Udiv case and this negative
    /// control honestly sampled (reported as unverified, E0.2) until that
    /// binding exists.
    #[test]
    fn udiv_portable_theorem_cannot_formally_self_attest_sdiv_source() {
        use trust_cg_lower::instructions::Opcode as LirOpcode;

        crate::env_lock::with_env_edits(|env| {
            env.set("TCG_NO_VERDICT_DB", "1");
            env.set("TCG_REFINE_SOLVER", "0");
            env.remove("TCG_NO_PROOF_CACHE");
            env.remove("TCG_CANARY_NO_CACHE");

            for (source_opcode, case) in [
                (LirOpcode::Udiv, "faithful Udiv -> UDIV"),
                (LirOpcode::Sdiv, "wrong Sdiv -> UDIV"),
            ] {
                let lir = tv2_div_lir_function(source_opcode);
                let func = tv2_func_with_alu_stamped(&lir, AArch64Opcode::UDiv, 0);
                let obligation = reconstruct_alu_obligation(&func.insts[0])
                    .expect("well-formed UDIV must reconstruct");
                // PRECONDITION, not the claim under test: the committed
                // `aarch64_udiv_64.lratcert` must actually be servable here,
                // or the "must not consume target-only portable authority"
                // assertions below pass vacuously. A decline is fail-closed
                // by design; name its gate and fix rather than a bare false.
                assert!(
                    crate::verdict_db::portable_cert_verified_obligation(&obligation),
                    "{case}: the regression must exercise the committed UDIV64 portable \
                     theorem, but portable replay declined: {}",
                    crate::canary_cert::describe_cert_skip_miss(
                        &crate::verdict_db::db_obligation_smt2(&obligation)
                    )
                    .unwrap_or_else(|| {
                        "no decline reason found on re-walk (a transient replay failure; rerun)"
                            .to_string()
                    })
                );

                let verifier =
                    FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
                let report = verifier.verify_with_lir_source_and_mode(
                    &func,
                    Some(&lir),
                    ProvenanceXCheckMode::Enforce,
                );
                assert_eq!(report.instructions.len(), 1);
                // {case}: valid but non-Formal until exact source binding, so
                // reported as sampled and uncredited.
                assert_sampled_uncredited(&report.instructions[0].result, "Udiv");
                assert_eq!(
                    report.formally_credited_count(),
                    0,
                    "{case} must not consume target-only portable authority"
                );
            }
        });
    }

    /// A faithful stamp (the ADD really lowers the Iadd at (0,0)) passes the
    /// cross-check even in enforce mode.
    #[test]
    fn tv2_aarch64_faithful_stamp_passes_enforce() {
        let lir = tv2_lir_function();
        let func = tv2_func_with_alu_stamped(&lir, AArch64Opcode::AddRR, 0);
        let report = FunctionVerifier::new().verify_with_lir_source_and_mode(
            &func,
            Some(&lir),
            ProvenanceXCheckMode::Enforce,
        );
        assert!(
            !tv2_provenance_failure(&report),
            "a faithful stamp must pass: {:?}",
            report.instructions
        );
    }

    /// Instructions without a sidecar entry are Unattributed and exempt.
    #[test]
    fn tv2_aarch64_unattributed_insts_are_exempt() {
        let lir = tv2_lir_function();
        let func = make_func_with_insts(vec![inst_with_operands(
            AArch64Opcode::AddRR,
            vec![
                MachOperand::PReg(X0),
                MachOperand::PReg(X0),
                MachOperand::PReg(X1),
            ],
        )]);
        let report = FunctionVerifier::new().verify_with_lir_source_and_mode(
            &func,
            Some(&lir),
            ProvenanceXCheckMode::Enforce,
        );
        assert!(!tv2_provenance_failure(&report));
    }

    /// E0.2 (statistical credit withdrawn): the single discharge-to-result
    /// mapping every function verifier uses never turns sampling into
    /// `Verified`. A sampled `Valid` is reported as `Unverified` with its sample
    /// count; `Exhaustive` and `Formal` `Valid` credit at exactly their own
    /// strength, and only `Formal` enters the formal tally (ENC-11). Refutation
    /// and inconclusive verdicts fail at every strength.
    #[test]
    fn statistical_discharge_is_never_verified_and_never_formal() {
        let sampled = VerificationStrength::Statistical {
            sample_count: 100_000,
        };
        let result = InstructionVerificationResult::from_discharge(
            "RECONSTRUCTED Iadd_I64",
            ProofCategory::Arithmetic,
            VerificationResult::Valid,
            sampled,
            false,
        );
        match &result {
            InstructionVerificationResult::Unverified { reason } => {
                assert!(
                    reason.starts_with(STATISTICAL_EVIDENCE_IS_NOT_CREDIT),
                    "{reason}"
                );
                assert!(reason.contains("100000 sampled inputs"), "{reason}");
            }
            other => panic!("sampled evidence must not be credited: {other:?}"),
        }
        let row = |opcode, result| InstructionReport {
            inst_index: 0,
            opcode: InstructionOpcode::AArch64(opcode),
            result,
        };
        let report = FunctionVerificationReport {
            function_name: "e02_statistical".to_string(),
            precondition_failure: None,
            instructions: vec![
                row(AArch64Opcode::AddRR, result),
                row(
                    AArch64Opcode::SubRR,
                    InstructionVerificationResult::from_discharge(
                        "formal",
                        ProofCategory::Arithmetic,
                        VerificationResult::Valid,
                        VerificationStrength::Formal,
                        false,
                    ),
                ),
                row(
                    AArch64Opcode::MulRR,
                    InstructionVerificationResult::from_discharge(
                        "exhaustive",
                        ProofCategory::Arithmetic,
                        VerificationResult::Valid,
                        VerificationStrength::Exhaustive,
                        false,
                    ),
                ),
            ],
        };
        assert_eq!(report.verified_count(), 2);
        assert_eq!(report.sampled_uncredited_count(), 1);
        assert_eq!(report.formally_credited_count(), 1);
        assert!(!report.all_verified());
        assert!(!report.emitted_opcode_inventory().is_promotable());
        assert!(matches!(
            &report.instructions[2].result,
            InstructionVerificationResult::Verified {
                strength: VerificationStrength::Exhaustive,
                ..
            }
        ));
        for strength in [
            sampled,
            VerificationStrength::Exhaustive,
            VerificationStrength::Formal,
        ] {
            assert!(
                InstructionVerificationResult::from_discharge(
                    "refuted",
                    ProofCategory::Arithmetic,
                    VerificationResult::Invalid {
                        counterexample: "x = 1".into(),
                    },
                    strength,
                    false,
                )
                .is_failed()
            );
            assert!(
                InstructionVerificationResult::from_discharge(
                    "inconclusive",
                    ProofCategory::Arithmetic,
                    VerificationResult::Unknown {
                        reason: "timeout".into(),
                    },
                    strength,
                    false,
                )
                .is_failed()
            );
        }
    }
}

/// The walk resolves an instruction to a registry proof by a short QUERY
/// fragment matched as a lowercase SUBSTRING of proof names inside one
/// category, first match in database order. That is fragile in exactly one
/// way: a new registry entry earlier in a category whose name contains an
/// existing fragment silently re-routes the walk. This pins, for every
/// literal query in this file, which proof it resolves to and how many
/// candidates it matched — so a change is a deliberate golden update, never
/// a surprise. (The computed MOVK/MOVN queries have their own uniqueness
/// tests in `const_materialize_proofs`.)
#[cfg(test)]
mod walk_query_resolution_golden {
    use super::*;

    const GOLDEN_PATH: &str = "tests/fixtures/walk_query_resolution.txt";

    /// Every `Some(("<query>", ProofCategory::<Cat>))` literal in this file.
    fn literal_queries() -> Vec<(String, String)> {
        let src = include_str!("function_verifier.rs");
        let mut out = Vec::new();
        let needle = "Some((\"";
        let mut rest = src;
        while let Some(i) = rest.find(needle) {
            rest = &rest[i + needle.len()..];
            let Some(q_end) = rest.find('"') else { break };
            let query = &rest[..q_end];
            let after = &rest[q_end..];
            const CAT: &str = "\", ProofCategory::";
            if let Some(stripped) = after.strip_prefix(CAT)
                && let Some(c_end) = stripped.find("))")
            {
                let cat = &stripped[..c_end];
                if cat.chars().all(|c| c.is_ascii_alphanumeric()) {
                    out.push((query.to_string(), cat.to_string()));
                }
            }
        }
        out.sort();
        out.dedup();
        out
    }

    fn category_by_name(db: &ProofDatabase, name: &str) -> Option<ProofCategory> {
        db.all()
            .iter()
            .map(|p| p.category)
            .find(|c| format!("{c:?}") == name)
    }

    #[test]
    fn every_literal_query_resolves_as_pinned() {
        let verifier = FunctionVerifier::new();
        let db = ProofDatabase::new();
        let queries = literal_queries();
        assert!(
            queries.len() >= 90,
            "found only {} literal queries",
            queries.len()
        );
        let mut actual = Vec::new();
        for (query, cat_name) in &queries {
            let Some(category) = category_by_name(&db, cat_name) else {
                panic!("query `{query}`: category {cat_name} has no proofs in the database");
            };
            let query_static: &'static str = Box::leak(query.clone().into_boxed_str());
            let resolved = verifier
                .registry_proof_for_query(query_static, category)
                .map(|p| p.obligation.name.clone())
                .unwrap_or_else(|| "<unresolved>".to_string());
            let matches = db
                .all()
                .iter()
                .filter(|p| {
                    p.category == category
                        && p.obligation.name.to_lowercase().contains(query.as_str())
                })
                .count();
            actual.push(format!("{cat_name}\t{query}\t{matches}\t{resolved}"));
        }
        let actual_text = actual.join("\n") + "\n";
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(GOLDEN_PATH);
        if std::env::var_os("UPDATE_GOLDEN").is_some() {
            std::fs::write(&path, &actual_text).expect("write golden");
            return;
        }
        let golden = std::fs::read_to_string(&path).unwrap_or_else(|e| {
            panic!(
                "read {}: {e} (run with UPDATE_GOLDEN=1 to create)",
                path.display()
            )
        });
        if golden != actual_text {
            let g: std::collections::BTreeSet<&str> = golden.lines().collect();
            let a: std::collections::BTreeSet<&str> = actual_text.lines().collect();
            let removed: Vec<_> = g.difference(&a).collect();
            let added: Vec<_> = a.difference(&g).collect();
            panic!(
                "walk query resolution changed (category\\tquery\\tmatches\\tresolved):\n  was: {removed:#?}\n  now: {added:#?}\nIf intended, re-run with UPDATE_GOLDEN=1 and review the diff of {}",
                path.display()
            );
        }
        // An unresolved literal query makes the walk report the instruction
        // `Unverified` (fail-closed under emit_proofs). Three FP opcodes have a
        // query but no registry proof AND are never emitted by the lowering
        // (FmaddRR, FminnmRR, FmaxnmRR); anything beyond those is a new gap.
        const KNOWN_UNEMITTED: &[&str] = &["fmadd", "fmaxnm", "fminnm"];
        let unresolved: Vec<_> = actual
            .iter()
            .filter(|l| l.ends_with("\t<unresolved>"))
            .filter(|l| {
                !KNOWN_UNEMITTED
                    .iter()
                    .any(|q| l.contains(&format!("\t{q}\t")))
            })
            .collect();
        assert!(
            unresolved.is_empty(),
            "literal queries that resolve to nothing: {unresolved:#?}"
        );
    }
}

#[cfg(test)]
mod precise_citation_tests {
    use super::tests::make_func_with_insts;
    use super::*;
    use trust_cg_ir::aarch64_regs::{W0, W1, W2, W3, X3, X4};

    fn cmpq(
        f: &MachFunction,
        insts: &[InstId],
        pos: usize,
        inst: &MachInst,
    ) -> Option<&'static str> {
        FunctionVerifier::precise_cmp_query_why(f, insts, pos, inst).ok()
    }
    fn brq(
        f: &MachFunction,
        insts: &[InstId],
        pos: usize,
        inst: &MachInst,
    ) -> Option<&'static str> {
        FunctionVerifier::precise_condbr_query_why(f, insts, pos, inst)
            .ok()
            .map(|(q, _)| q)
    }

    /// A B.cond fed by TST cites the standalone-TST obligation for its
    /// condition, in the CmpCombine category; a C-observing condition after
    /// TST has none (it fails closed elsewhere).
    #[test]
    fn condbr_after_tst_cites_the_tst_obligation() {
        use AArch64Opcode::*;
        let f = make_func_with_insts(vec![
            MachInst::new(Tst, vec![MachOperand::PReg(X3), MachOperand::PReg(X4)]),
            MachInst::new(
                BCond,
                vec![
                    MachOperand::Imm(1),
                    MachOperand::Block(trust_cg_ir::BlockId(0)),
                ],
            ), // NE
            MachInst::new(Tst, vec![MachOperand::PReg(W0), MachOperand::PReg(W1)]),
            MachInst::new(
                BCond,
                vec![
                    MachOperand::Imm(8),
                    MachOperand::Block(trust_cg_ir::BlockId(0)),
                ],
            ), // HI
        ]);
        let insts = &f.blocks[0].insts;
        let at = |i: usize| f.insts.get(insts[i].0 as usize).unwrap();
        // (built as a value, not a `Some((literal, category))` — the walk-query
        // golden scans this file for that exact spelling)
        let want = ("tst w64: ne", ProofCategory::CmpCombine);
        assert_eq!(
            FunctionVerifier::precise_condbr_query_why(&f, insts, 1, at(1)).ok(),
            Some(want)
        );
        assert!(FunctionVerifier::precise_condbr_query_why(&f, insts, 3, at(3)).is_err());
        let v = FunctionVerifier::new();
        assert!(
            v.registry_proof_for_query("tst w64: ne", ProofCategory::CmpCombine)
                .is_some()
        );
    }

    /// Every family literal the refinement can emit names exactly one registry
    /// proof — the whole point of refining.
    #[test]
    fn precise_citation_families_are_unique() {
        let db = ProofDatabase::new();
        let mut checked = 0;
        for (kind, category) in [
            (PreciseFamily::Icmp, ProofCategory::Comparison),
            (PreciseFamily::CondBr, ProofCategory::Branch),
        ] {
            for cc in 0..16i64 {
                for width in [32u32, 64] {
                    let Some(q) = FunctionVerifier::icmp_family_query(kind, cc, width) else {
                        continue;
                    };
                    let n = db
                        .all()
                        .iter()
                        .filter(|p| {
                            p.category == category && p.obligation.name.to_lowercase().contains(q)
                        })
                        .count();
                    assert_eq!(n, 1, "family query `{q}` matches {n} proofs");
                    checked += 1;
                }
            }
        }
        assert_eq!(checked, 40);
    }

    /// CMP + CSET(LT) at 32 bits -> Icmp_SLT_I32; CMP + B.GE at 64 -> CondBr_SGE_I64;
    /// a CMP whose consumers disagree, or with no consumer, is not refined.
    #[test]
    fn cmp_and_condbr_refine_to_their_own_family_member() {
        use AArch64Opcode::*;
        let f = make_func_with_insts(vec![
            MachInst::new(CmpRR, vec![MachOperand::PReg(W0), MachOperand::PReg(W1)]),
            MachInst::new(CSet, vec![MachOperand::PReg(W2), MachOperand::Imm(11)]), // LT
            MachInst::new(CmpRR, vec![MachOperand::PReg(X3), MachOperand::PReg(X4)]),
            MachInst::new(
                BCond,
                vec![
                    MachOperand::Imm(10),
                    MachOperand::Block(trust_cg_ir::BlockId(0)),
                ], // GE
            ),
        ]);
        let insts = &f.blocks[0].insts;
        let at = |i: usize| f.insts.get(insts[i].0 as usize).unwrap();
        assert_eq!(cmpq(&f, insts, 0, at(0)), Some("icmp_slt_i32"));
        assert_eq!(cmpq(&f, insts, 2, at(2)), Some("icmp_sge_i64"));
        assert_eq!(brq(&f, insts, 3, at(3)), Some("condbr_sge_i64"));

        let g = make_func_with_insts(vec![
            MachInst::new(CmpRR, vec![MachOperand::PReg(W0), MachOperand::PReg(W1)]),
            MachInst::new(CSet, vec![MachOperand::PReg(W2), MachOperand::Imm(11)]),
            MachInst::new(CSet, vec![MachOperand::PReg(W3), MachOperand::Imm(12)]), // disagrees
        ]);
        let gi = &g.blocks[0].insts;
        assert_eq!(
            cmpq(&g, gi, 0, g.insts.get(gi[0].0 as usize).unwrap()),
            None
        );
        let h = make_func_with_insts(vec![MachInst::new(
            CmpRR,
            vec![MachOperand::PReg(W0), MachOperand::PReg(W1)],
        )]);
        let hi = &h.blocks[0].insts;
        assert_eq!(
            cmpq(&h, hi, 0, h.insts.get(hi[0].0 as usize).unwrap()),
            None
        );
    }

    /// Every AArch64 opcode this module exempts as covered-elsewhere must be
    /// one the coverage gate records as covered too: either an emitted
    /// value/effect row the gate credits through the decoded-word obligations
    /// (whose in-process credit hook must accept), or an allowlisted row whose
    /// reason names the covering evidence boundary. A gate RED deferral is
    /// never exempted, and a row the gate calls pending must be named a
    /// deferral here as well, and vice versa.
    #[test]
    fn covered_elsewhere_exemptions_agree_with_the_coverage_gate() {
        use crate::aarch64_value_decode_proofs::{a64_value_credit, a64_value_forms};
        use crate::coverage_gate::{
            ALL_AARCH64_OPCODES, OpcodeClass, aarch64_deferred_value_op_reason, classify_aarch64,
        };

        let mut exempted = Vec::new();
        for &opcode in ALL_AARCH64_OPCODES {
            let wrapped = InstructionOpcode::AArch64(opcode);
            let exempt = is_covered_elsewhere_indirect_branch(wrapped)
                || is_covered_elsewhere_emission_padding(wrapped);
            if let Some(reason) = aarch64_deferred_value_op_reason(opcode) {
                assert!(
                    !exempt,
                    "{opcode:?} is a coverage-gate RED deferral ({reason}) and must not be exempted"
                );
            }
            if !exempt {
                assert!(
                    !COVERED_ELSEWHERE_NAMED_DEFERRALS.contains(&opcode),
                    "{opcode:?} is named a deferral but is not exempted"
                );
                continue;
            }
            exempted.push(opcode);
            match classify_aarch64(opcode) {
                OpcodeClass::EmittableNeedsProof => {
                    let forms = a64_value_forms(opcode).unwrap_or_else(|| {
                        panic!(
                            "{opcode:?}: exempted, but the gate has no decoded-word credit for it"
                        )
                    });
                    assert!(
                        !forms.is_empty(),
                        "{opcode:?}: empty decoded-word form table"
                    );
                    let credit = a64_value_credit(opcode).unwrap_or_else(|e| {
                        panic!("{opcode:?}: the gate's credit hook refuses: {e}")
                    });
                    assert_eq!(credit.forms, forms.len(), "{opcode:?}: {credit:?}");
                    assert!(credit.captured_words >= 1, "{opcode:?}: {credit:?}");
                    assert!(credit.controls_refuted >= 1, "{opcode:?}: {credit:?}");
                    assert!(
                        !COVERED_ELSEWHERE_NAMED_DEFERRALS.contains(&opcode),
                        "{opcode:?} is credited by the gate and must not be named a deferral"
                    );
                }
                OpcodeClass::FailClosedAllowlisted { reason } => {
                    let lower = reason.to_ascii_lowercase();
                    assert!(
                        lower.contains("covered") || lower.contains("never selected"),
                        "{opcode:?}: allowlist reason names neither the covering evidence nor \
                         never-selected status: {reason}"
                    );
                    let pending = lower.contains("pending");
                    assert_eq!(
                        pending,
                        COVERED_ELSEWHERE_NAMED_DEFERRALS.contains(&opcode),
                        "{opcode:?}: the gate {} it pending, this module {} it a deferral: {reason}",
                        if pending { "calls" } else { "does not call" },
                        if COVERED_ELSEWHERE_NAMED_DEFERRALS.contains(&opcode) {
                            "names"
                        } else {
                            "does not name"
                        },
                    );
                }
                OpcodeClass::PseudoOrTrap => {
                    panic!(
                        "{opcode:?}: exempted as covered-elsewhere but classified as a pseudo/trap"
                    )
                }
            }
        }
        exempted.sort_by_key(|o| format!("{o:?}"));
        let mut expected = vec![
            AArch64Opcode::AlignNop,
            AArch64Opcode::BLR,
            AArch64Opcode::Blr,
            AArch64Opcode::Br,
            AArch64Opcode::Cbnz,
            AArch64Opcode::Cbz,
            AArch64Opcode::Ret,
            AArch64Opcode::Tbnz,
            AArch64Opcode::Tbz,
        ];
        expected.sort_by_key(|o| format!("{o:?}"));
        assert_eq!(
            exempted, expected,
            "the closed exemption list changed; re-reconcile it with the coverage gate"
        );
    }
}
