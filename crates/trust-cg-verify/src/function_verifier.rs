// trust-cg-verify/function_verifier.rs - Function-level verification pipeline
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Provides verify_function(): given a MachFunction, walk every instruction,
// map each opcode to a proof obligation from the ProofDatabase, run the
// proof, and produce a FunctionVerificationReport with per-instruction
// results and coverage metrics.
//
// Reference: designs/2026-04-13-verification-architecture.md,
//            crates/trust-cg-verify/src/proof_database.rs

//! Function-level verification pipeline.
//!
//! [`verify_function`] inspects every instruction in a [`MachFunction`],
//! maps each AArch64 opcode to the corresponding proof obligation from
//! the [`ProofDatabase`], runs the proof via [`verify_by_evaluation`],
//! and produces a [`FunctionVerificationReport`] with per-instruction
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
use trust_cg_ir::aarch64_regs::{SP, W16, W17, WSP, X16, X17, X29, preg_class};
use trust_cg_ir::cc::OperandSize;
use trust_cg_ir::{
    AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, PReg, SpecialReg, X86Opcode,
};

use crate::lowering_proof::{
    MachineSideProvenance, ProofObligation, VerificationConfig, memoized_verify_by_evaluation,
};
use crate::proof_database::{ProofCategory, ProofDatabase};
use crate::provenance_xcheck::{
    self, AARCH64_PROVENANCE_XCHECK_DEFAULT, LirSourceIndex, OpClass, ProvenanceXCheckMode,
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
}

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
///
///   * #62 covered-elsewhere structural forms (their ONLY mapped proof WAS a
///     degenerate X==X, now RETRACTED — but the form is genuinely covered by a
///     structural argument, NOT pending a missing value theorem):
///       - Register copy (MOV/typed aliases, FMOV FPR↔FPR, AND the cross-class
///         FMOV FPR↔GPR `to_bits`/`from_bits`/`copysign` reinterpret moves): a
///         bit-preserving identity (the x86 Copy_I*/F* bit-identity proofs are the
///         genuine model; AArch64 MOV/FMOV denote the same MATCHED-WIDTH bit copy).
///         `FMOV Xd,Dn` / `FMOV Dd,Xn` copy ALL 64 (or 32) bits with NO transform,
///         NO canonicalization, NO rounding — exactly the FPR↔FPR copy, just
///         crossing register classes; the bits preserved ARE the trust_ir
///         bit-preserving reinterpret (`f64::to_bits`/`from_bits`), so there is
///         nothing to PROVE (it is a copy). A per-instruction obligation is
///         DEGENERATE here: the verify SMT model shares ONE bitvector domain for an
///         FP value and its raw IEEE bits (`encode_trust_ir_bitcast` is the
///         bitvector identity), so machine==spec collapses to the X==X that #62
///         retracted — the form is covered by the structural bit-copy argument, NOT
///         pending a missing value theorem. Every non-trivial function emits copies.
///       - Return edge (RET): the architecturally-fixed return transfer; the CFG
///         return edge is covered by the Branch/CallLowering family. Every function
///         that returns emits RET.
///       - Conditional select (CSEL/CSINC/CSNEG): the genuine select semantics +
///         the CSEL condition-inversion algebra proof cover the form; the per-opcode
///         X==X was the retracted degeneracy. (CSINV is deliberately EXCLUDED — it
///         has no proof at all and stays blocking, matching the pre-#62 posture.)
///       - Direct call / unconditional jump targets (Call/Jmp): the CFG edge +
///         PLT32/branch relocation cover the target (mirrors the indirect family).
///       - Constant materialization (x86 MOV r,imm): the emitted immediate IS the
///         trust_ir constant by construction of the lowerer; correctness is the
///         immediate/relocation encoding (covered-elsewhere structural), the same
///         class as AArch64 MovI/Adr/Adrp ("constant materialization — covered by
///         AddressMode/relocation proofs"). The retracted X==X was const==const.
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
                    | A::MovR
                    | A::MOVWrr
                    | A::MOVXrr
                    | A::FmovFprFpr
                    // Cross-class scalar FMOV bitcasts (FPR↔GPR): pure
                    // matched-width bit copies implementing the bit-preserving
                    // to_bits/from_bits/copysign reinterpret — structurally covered
                    // exactly like FmovFprFpr (a per-instruction cert is degenerate
                    // X==X under the single-bitvector-domain SMT model). NARROW: the
                    // two scalar cross-class forms ONLY, not vector/other Fmov forms.
                    | A::FmovFprGpr
                    | A::FmovGprFpr
                    | A::Ret
                    | A::Csel
                    | A::Csinc
                    | A::Csneg
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

/// Emission-time padding with no value, memory, or control-flow semantics.
///
/// `AlignNop` is a real four-byte arena instruction so every offset derivation
/// counts it, but it encodes the architectural NOP `0xD503201F`. Its meaningful
/// obligations are enforced elsewhere: the AArch64 decode check pins the exact
/// word and the independent EH/encoder offset cross-check pins stream layout.
/// A per-instruction value obligation would only be the vacuous `nop == nop`
/// form retracted from proof authority.
///
/// Keep this exact and separate from the broader coverage-gate allowlist: only
/// emission padding earns this structural credit.
pub fn is_covered_elsewhere_emission_padding(opcode: InstructionOpcode) -> bool {
    matches!(opcode, InstructionOpcode::AArch64(AArch64Opcode::AlignNop))
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
        self.uncovered_non_pseudo_opcodes().is_empty()
    }

    /// Builds a concise fail-closed rejection reason for proof promotion.
    ///
    /// Enumerates every DISTINCT uncovered opcode (not just the first) so a
    /// fail-closed compile error names the full coverage gap in one shot —
    /// essential now that the rustc bridge requests proof certificates
    /// per-compile and surfaces this reason as the compile error.
    pub fn promotion_rejection_reason(&self) -> Option<String> {
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

/// Report from verifying all instructions in a MachFunction.
#[derive(Debug, Clone)]
pub struct FunctionVerificationReport {
    /// Function name.
    pub function_name: String,
    /// Per-instruction results.
    pub instructions: Vec<InstructionReport>,
}

impl FunctionVerificationReport {
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

    /// TAXONOMY SCAN (PROOF-5 / ENC-11 / M3 criterion (d)): number of verified
    /// instructions credited via `method=Statistical` — the honest 100k-sample
    /// tier, which is NEVER a formal proof. On a SOLVER-PRESENT host this count
    /// must be 0: every `> 8`-bit reconstructed/registry obligation is credited
    /// `Formal` (SolverProven, via the tier-0 parametric verdict or the live
    /// solver), and `<= 8`-bit obligations are `Exhaustive`. On a SOLVER-ABSENT
    /// host this count reflects the honest Statistical fallback (never
    /// fail-closed). Use with [`crate::verdict_db::solver_present`] to assert the
    /// M3 gate; `> 0` on a solver-present host is a taxonomy violation.
    pub fn statistically_credited_count(&self) -> usize {
        self.instructions
            .iter()
            .filter(|r| {
                matches!(
                    &r.result,
                    InstructionVerificationResult::Verified {
                        strength: VerificationStrength::Statistical { .. },
                        ..
                    }
                )
            })
            .count()
    }

    /// TAXONOMY SCAN companion: number of verified instructions credited
    /// `Formal` (SolverProven) — a real SMT solver proved the equivalence for all
    /// inputs (offline tier-0 parametric verdict or the per-compile live solver).
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
    pub fn genuine_coverage_percent(&self) -> f64 {
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
        self.unverified_count() == 0
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
    /// (vacuous truth: all non-pseudo instructions have a discharged binding).
    pub fn coverage_percent(&self) -> f64 {
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
        self.unverified_count() == 0 && self.failed_count() == 0
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
                let (status, detail) = match &report.result {
                    InstructionVerificationResult::Verified { proof_name, .. } => {
                        (OpcodeInventoryStatus::Verified, proof_name.clone())
                    }
                    InstructionVerificationResult::Skipped { reason } => {
                        (OpcodeInventoryStatus::Skipped, reason.clone())
                    }
                    InstructionVerificationResult::Unverified { reason } => {
                        // Indirect call/branch targets are covered by the
                        // surrounding proofs, not a per-instruction tautology, so
                        // they are promotable (see `CoveredElsewhere`). This is a
                        // CLOSED, opcode-identity list — NOT the broad
                        // `coverage_gate` FailClosedAllowlisted set, which also
                        // tags genuine "pending a proof" gaps (CSINV/bitfield)
                        // that MUST keep blocking promotion.
                        if is_covered_elsewhere_indirect_branch(report.opcode)
                            || is_covered_elsewhere_emission_padding(report.opcode)
                        {
                            (OpcodeInventoryStatus::CoveredElsewhere, reason.clone())
                        } else {
                            (OpcodeInventoryStatus::Unverified, reason.clone())
                        }
                    }
                    InstructionVerificationResult::Failed { detail, .. } => {
                        (OpcodeInventoryStatus::Failed, detail.clone())
                    }
                };
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
            entries,
        }
    }
}

impl std::fmt::Display for FunctionVerificationReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Function Verification Report: {}", self.function_name)?;
        writeln!(f, "============================================")?;
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

/// True iff `op` is the AArch64 zero register (`XZR`/`WZR`).
///
/// Used to recognize the `MVN` (`Bnot`) alias of `OrnRR` (`ORN Rd, ZR, Rm`): an
/// `OrnRR` whose `rn` slot is the zero register computes `ZR | ~Rm = ~Rm`, i.e.
/// a unary bitwise NOT of `Rm`, not a binary OR-NOT.
fn is_zero_reg(op: &MachOperand) -> bool {
    matches!(op, MachOperand::Special(SpecialReg::XZR | SpecialReg::WZR))
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
    let dst_width = operand_reg_width_bits(dst)?;
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
const fn is_parametric_imm_binary_opcode(op: AArch64Opcode) -> bool {
    matches!(
        op,
        AArch64Opcode::AddRI
            | AArch64Opcode::SubRI
            | AArch64Opcode::AndRI
            | AArch64Opcode::OrrRI
            | AArch64Opcode::EorRI
            | AArch64Opcode::LslRI
            | AArch64Opcode::LsrRI
            | AArch64Opcode::AsrRI
    )
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
    if is_parametric_imm_binary_opcode(inst.opcode) && inst.operands.len() == 3 {
        use trust_cg_ir::RegClass;
        use trust_cg_ir::regs::VReg;
        let dst_width = operand_reg_width_bits(inst.operands.first()?)?;
        let class = match dst_width {
            32 => RegClass::Gpr32,
            64 => RegClass::Gpr64,
            _ => return reconstruct_alu_obligation(inst),
        };
        let mut synth = inst.clone();
        synth.operands[2] = MachOperand::VReg(VReg::new(u32::MAX, class));
        return reconstruct_alu_obligation(&synth).or_else(|| reconstruct_alu_obligation(inst));
    }
    reconstruct_alu_obligation(inst)
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

        // Other unary (Neg): [dst, src].
        _ if arity == AluArity::Unary => vec![w(0), w(1)],
        // Binary register form: [dst, src1, src2].
        _ => vec![w(0), w(1), w(2)],
    };
    Some(MachInst::new(opcode, operands))
}

/// Does a representative reconstructed obligation for `opcode` discharge `Valid`
/// under `config`? Used by the COVERAGE GATE to CREDIT a reconstructable opcode
/// as covered (task #63 Step 4).
///
/// Returns `false` (NOT covered) for any opcode that is not reconstructable, that
/// has no representative instance, that fails to reconstruct, or whose
/// reconstructed obligation does not discharge `Valid`. The credit is keyed on
/// the obligation being `Reconstructed` (its machine side came from the REAL
/// opcode) AND discharging `Valid` — the exact same dual criterion the function
/// verifier's `try_reconstruct` uses, so the gate measures precisely the
/// coverage the per-instruction walk would credit.
pub fn reconstruction_discharges_valid(opcode: AArch64Opcode, config: &VerificationConfig) -> bool {
    let Some(inst) = representative_reconstructable_inst(opcode) else {
        return false;
    };
    let Some(obligation) = reconstruct_alu_obligation(&inst) else {
        return false;
    };
    if !obligation.is_reconstructed() {
        return false;
    }
    // Routed through the shared CONTENT-keyed memo (PROOF-2): sound by
    // construction (the key embeds the full obligation, never just its name)
    // and skips re-sweeping the same representative obligation per compile.
    matches!(
        memoized_verify_by_evaluation(&obligation, config),
        VerificationResult::Valid
    )
}

// ---------------------------------------------------------------------------
// FunctionVerifier
// ---------------------------------------------------------------------------

/// Verifier that maps MachFunction instructions to proof obligations.
pub struct FunctionVerifier {
    db: ProofDatabase,
    config: VerificationConfig,
}

impl FunctionVerifier {
    /// Create a new function verifier with default configuration.
    pub fn new() -> Self {
        Self {
            db: ProofDatabase::new(),
            config: VerificationConfig::default(),
        }
    }

    /// Create a new function verifier with custom verification configuration.
    pub fn with_config(config: VerificationConfig) -> Self {
        Self {
            db: ProofDatabase::new(),
            config,
        }
    }

    /// Map an AArch64 opcode to a proof search query and category.
    ///
    /// Returns `Some((search_substring, category))` for opcodes that have
    /// corresponding proofs in the database, or `None` for opcodes without
    /// proof coverage.
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
            // TST produces the complete NZCV state. Concrete instructions are
            // width/shape-bound below; this opcode-level token is used only by
            // callers that do not have operands (the coverage gate separately
            // demands both registered widths).
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
            StrRI | StrbRI | StrhRI | StrRO | STRWui | STRXui | STRSui | STRDui => {
                Some(("store", ProofCategory::Memory))
            }
            // NEON post-index vector load/store — THE SAME shared whole-backend
            // unfaithful-load/store debt as the scalar Ldr*/Str* family above
            // (`classify_aarch64` documents NeonLdpQPost as "the paired form of the
            // same Ldr*/Str* debt", reading exactly the 32 bytes two NeonLd1Post
            // reads would; NeonStpQPost is its store sibling). Credited to the SAME
            // `("load"/"store", Memory)` debt query so the per-compile gate agrees
            // with `coverage_gate` (which FailClosedAllowlists these on the identical
            // differential + guard-page OOB basis) — NOT a new credit, the parity
            // that keeps the two gates consistent for NEON as they already are for
            // integer memory. The Memory "load"/"store" query is the honest
            // KNOWN_DEGENERATE_PENDING_FIX dereference debt (it proves the memory-op
            // is inventoried, not the loaded VALUE) — identical strength for the
            // NEON and scalar forms.
            NeonLdpQPost | NeonLd1Post => Some(("load", ProofCategory::Memory)),
            NeonStpQPost | NeonSt1Post => Some(("store", ProofCategory::Memory)),
            // Writeback (pre/post-index) memory forms + the PC-relative literal
            // load — the SAME shared Ldr*/Str* dereference debt as the scalar
            // loads/stores above (coverage_gate: "writeback memory form — covered
            // by Memory/AddressMode proofs"; "PC-relative literal load"). The
            // base-register writeback is part of the single opcode's memory
            // semantics — identical debt strength to the post-index NeonLdpQPost
            // already credited here. NOT a new credit — parity that keeps the
            // per-compile gate consistent with coverage_gate for these forms.
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
            // (`mem[addr] = desired`). NARROW: only the CAS family. The SWP/exclusive
            // (Swp*/Ldaxr/Stlxr) and min/max LSE RMW opcodes deliberately STAY
            // fail-closed — `all_atomic_proofs()` RETRACTED their degenerate
            // "returns old value" obligations, so no retained proof backs them.
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

            // Generated frame prologue/epilogue pair instructions.
            StpPreIndex => Some(("sp alignment preserved", ProofCategory::FrameLayout)),
            StpRI => Some((
                "callee-save pair slots don't overlap",
                ProofCategory::FrameLayout,
            )),
            LdpRI | LdpPostIndex => Some((
                "callee-save restore is identity",
                ProofCategory::FrameLayout,
            )),

            // Floating-point
            FaddRR => Some(("fadd", ProofCategory::FloatingPoint)),
            FmaddRR => Some(("fmadd", ProofCategory::FloatingPoint)),
            FsubRR => Some(("fsub", ProofCategory::FloatingPoint)),
            FmulRR => Some(("fmul", ProofCategory::FloatingPoint)),
            FminnmRR => Some(("fminnm", ProofCategory::FloatingPoint)),
            FmaxnmRR => Some(("fmaxnm", ProofCategory::FloatingPoint)),
            FnegRR => Some(("fneg", ProofCategory::FloatingPoint)),
            // Scalar FP compare (FCMP + CSET): bound to the FAITHFUL
            // `Fcmp_<cond>_F{32,64}` proofs (machine side = FCMP→NZCV then CSET
            // reading `from_floatcc(cond)`; a wrong cond-code REFUTES). FCMP only
            // SETS the flags (condition-independent), so a representative
            // condition is a sound per-opcode cert; the following CSET reads the
            // exact cond code. The representative MUST be a condition whose CSET
            // flag-reading is STRUCTURALLY DISTINCT from the trust_ir source
            // (else `is_genuinely_proven` rejects it as X==X): `GE` reads
            // `N==V` (= `iff(a<b, unordered)`) — manifestly different from the
            // source `fp.ge`, so the proof is non-degenerate. (`Eq`/`NE`/`LT`
            // happen to read a single flag equal to the source predicate and are
            // structurally degenerate; they are still registered+discharged but
            // are NOT the representative.) The lowercase "fcmp_ge" token resolves
            // (within FloatingPoint) to `Fcmp_GE_F32`.
            Fcmp => Some(("fcmp_ge", ProofCategory::FloatingPoint)),
            // FMOV (FPR scalar copy): its only DB proof was the degenerate
            // "CopyProp: COPY(x) == x" X==X (retracted in #62). No value-proof
            // mapping; FmovFprFpr is FailClosedAllowlisted in classify_aarch64.
            FmovFprFpr => None,
            // FMOV cross-class scalar bitcasts (FPR↔GPR): the bit-preserving
            // to_bits/from_bits/copysign reinterpret moves. No value-proof mapping —
            // a per-instruction obligation is the degenerate X==X (an FP value and
            // its IEEE bits share ONE bitvector domain in the SMT model). They are
            // CoveredElsewhere (is_covered_elsewhere_indirect_branch) as a pure
            // matched-width bit copy, exactly like FmovFprFpr / MovR.
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

            // GPR register copy (MOV/typed aliases): its only DB proof was the
            // degenerate "CopyProp: COPY(x) == x" X==X (retracted in #62). No
            // value-proof mapping; MovR/MOVWrr/MOVXrr are FailClosedAllowlisted
            // in classify_aarch64.
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
            // The retained hw0 theorem models only the X form. Concrete
            // width-sensitive binding happens below; opcode-wide credit would
            // incorrectly include W-form zero-extension semantics.
            Movn => None,
            // MOVK remains emittable as the repair step in canonical
            // materialization chains, but the registered "MOVK idempotent"
            // theorem proves only double application of the hw0 operation. It
            // is not a general per-instruction lowering/encoding proof and must
            // not be credited opcode-wide.
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
            AddTprelHi12 => Some(("add(lsl#12) == tp", ProofCategory::MachOEmission)),
            AddTprelLo12 => Some(("add;add == tp", ProofCategory::MachOEmission)),
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
            // their register target is established by the surrounding proofs.)
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
            // category). BFM (insert), RORV (RorRI, not isel-emitted), and RBIT
            // stay fail-closed — no faithful per-opcode obligation yet.
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
            NeonAndV => Some(("andv.16b lanewise-intent", ProofCategory::NeonLowering)),
            NeonOrrV => Some(("orrv.16b lanewise-intent", ProofCategory::NeonLowering)),
            NeonEorV => Some(("eorv.16b lanewise-intent", ProofCategory::NeonLowering)),
            NeonBicV => Some(("bicv.16b lanewise-intent", ProofCategory::NeonLowering)),
            NeonNotV => Some(("notv.16b lanewise-intent", ProofCategory::NeonLowering)),

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
            // `.8H->.4S`); the query matches the `.16b->.8h` obligation, and the
            // `.8h->.4s` obligation is co-registered and discharged by the batch and
            // gate tests — the opcode-level credit is that UADDLP computes the right
            // pairwise-widening add, which both obligations establish.
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
            // NeonUaddlpV, one opcode with two arrangements: the query matches the
            // `.16b->.8h` obligation; the `.8h->.4s` obligation is co-registered
            // and discharged by the same batch and gate tests.
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

            // Conditional select (covered by comparison proofs)
            CSet => Some(("cmp", ProofCategory::Comparison)),

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
            // expansion and the standalone smulh-idiom high-half.
            Smulh => Some(("checkedsmul_i64", ProofCategory::Arithmetic)),
            Umulh => Some(("checkedumul_i64", ProofCategory::Arithmetic)),

            // i128 carry-chain HIGH limb (ADC/SBC occur ONLY inside an i128
            // add/sub/neg chain) -> the FAITHFUL whole-chain composition proof.
            // Query MUST be lowercase: verify() does name.to_lowercase().contains(query)
            // WITHOUT lowercasing the query (function_verifier.rs lookup), so a
            // mixed-case token silently fails to match there.
            Adc => Some(("iadd_i128 whole-chain", ProofCategory::Arithmetic)),
            Sbc => Some(("isub_i128 whole-chain", ProofCategory::Arithmetic)),

            // Conditional selects (CSEL/CSINC/CSNEG): their only mapped proofs were
            // the degenerate IfConversion X==X self-equalities (machine side
            // mirrored the spec, no independent select encoder), which were
            // RETRACTED in #62. They have no static value-proof now (None) and are
            // FailClosedAllowlisted in classify_aarch64 — exactly like CSINV, which
            // never had a proof. (The genuine CSEL condition-inversion algebra proof
            // remains in the DB but is not a per-opcode value cert.)
            Csel | Csinc | Csneg => None,

            // Scalar FP abs / sqrt / div: bound to the registered FloatingPoint
            // value proofs whose machine side IS that exact instruction. These
            // are width-polymorphic over {F32, F64}; the verifier matches a
            // representative width here while the coverage gate demands BOTH the
            // F32 and F64 proofs discharge (see `aarch64_width_polymorphic_proofs`).
            FabsRR => Some(("fabs", ProofCategory::FloatingPoint)),
            FsqrtRR => Some(("fsqrt", ProofCategory::FloatingPoint)),
            FdivRR => Some(("fdiv", ProofCategory::FloatingPoint)),

            // Scalar FP conditional select (FCSEL) — bound to the FAITHFUL
            // bit-preserving-mux obligations (all_fcsel_proofs). Width-polymorphic
            // over {F32, F64}; the "fcsel" token matches a representative here
            // (both discharge Valid) while the coverage gate demands BOTH the
            // fcsel_f32 and fcsel_f64 proofs (see `aarch64_width_polymorphic_proofs`).
            // Unlike the integer CSEL family above (None — their only proofs were
            // the retracted degenerate X==X IfConversion entries), FCSEL has an
            // independent, structurally-distinct machine model, so it is credited.
            FcselRR => Some(("fcsel", ProofCategory::FloatingPoint)),

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
    /// scalarized STP spills, are handled by `inst_to_proof_query_in_block`.
    pub fn inst_to_proof_query(inst: &MachInst) -> Option<(&'static str, ProofCategory)> {
        Self::generated_stack_slot_spill_or_reload_query(inst)
            .or_else(|| Self::generated_emergency_spill_slot_address_query(inst))
            .or_else(|| Self::generated_frame_address_materialization_query(inst))
            .or_else(|| Self::generated_fp_sp_relative_addressing_query(inst))
            .or_else(|| Self::operand_sensitive_or_opcode_query(inst))
    }

    fn inst_to_proof_query_in_block(
        func: &MachFunction,
        block_insts: &[InstId],
        block_pos: usize,
        inst: &MachInst,
    ) -> Option<(&'static str, ProofCategory)> {
        Self::generated_stack_slot_spill_or_reload_query(inst)
            .or_else(|| Self::generated_stp_spill_scalarization_query(func, block_insts, block_pos))
            .or_else(|| Self::generated_emergency_spill_slot_address_query(inst))
            .or_else(|| Self::generated_frame_address_materialization_query(inst))
            .or_else(|| Self::generated_fp_sp_relative_addressing_query(inst))
            .or_else(|| Self::i128_carry_chain_low_limb_query(func, block_insts, block_pos))
            .or_else(|| Self::operand_sensitive_or_opcode_query(inst))
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
        // MOVK binds to the (width, halfword)-SPECIFIC splice obligation rather
        // than an opcode-wide credit: the proof pins both the 16 written bits and
        // the preservation of the remaining bits at exactly this slot, so a MOVK
        // emitted at the wrong halfword cannot inherit another slot's proof.
        if inst.opcode == AArch64Opcode::Movk {
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
        use AArch64Opcode::{Adc, AddsRR, Sbc, SubsRR};
        let cur = Self::inst_at_block_pos(func, block_insts, block_pos)?;
        let next = Self::inst_at_block_pos(func, block_insts, block_pos + 1)?;
        match (cur.opcode, next.opcode) {
            (AddsRR, Adc) => Some(("iadd_i128 whole-chain", ProofCategory::Arithmetic)),
            (SubsRR, Sbc) => Some(("isub_i128 whole-chain", ProofCategory::Arithmetic)),
            _ => None,
        }
    }

    fn trap_skip_reason(opcode: AArch64Opcode) -> Option<&'static str> {
        match opcode {
            AArch64Opcode::Brk => Some("emitted trap instruction"),
            AArch64Opcode::TrapOverflow
            | AArch64Opcode::TrapBoundsCheck
            | AArch64Opcode::TrapBoundsCheckExact
            | AArch64Opcode::TrapNull
            | AArch64Opcode::TrapNullIfZero
            | AArch64Opcode::TrapDivZero
            | AArch64Opcode::TrapDivZeroIfZero
            | AArch64Opcode::TrapShiftRange
            | AArch64Opcode::TrapShiftRangeIfOOB
            | AArch64Opcode::TrapOverflowExact => Some("trap pseudo-instruction"),
            _ => None,
        }
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

    /// Phase-2 reconstruction discharge for a pilot ALU instruction (#63).
    ///
    /// Returns:
    /// - `Some(Verified { degenerate: false, .. })` when the instruction is a
    ///   pilot opcode with a reconstructable operand shape AND the reconstructed
    ///   obligation discharges `Valid`. The proof is credited (`degenerate:
    ///   false`) because its provenance is `Reconstructed` — the machine side
    ///   came from the REAL emitted instruction, so a wrong opcode/wiring would
    ///   have refuted, even though a *correct* commutative lowering reconstructs
    ///   to `bvadd == bvadd`.
    /// - `Some(Failed { .. })` when the reconstructed obligation REFUTES (the
    ///   isel opcode/wiring is wrong). This is the content of the mechanism.
    /// - `None` when the opcode is NOT a pilot opcode, or the instruction has no
    ///   reconstructable operand shape (e.g. an operand-less stub). The caller
    ///   then falls through to the existing DB-substring path unchanged, so no
    ///   path that previously verified regresses.
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

        // PROOF-5 / TV-9 (B2): prefer a PARAMETRIC/tier-0 candidate after live
        // solver revalidation (or a live fallback verdict on a miss) and
        // credit it `Formal` (SolverProven) instead of the 100k-sample
        // Statistical sweep. The `canonical` obligation frees the immediate for
        // the immediate-baked RI families so one parametric row covers the whole
        // width family; a miss with a solver present routes to the live solver
        // (refute → fail closed; inconclusive → statistical fallback); a
        // solver-absent host keeps the honest Statistical label. Crediting is
        // MONOTONE — never weaker than the previous sweep.
        let canonical =
            canonical_reconstruct_obligation(inst).unwrap_or_else(|| obligation.clone());
        let (vresult, strength) = crate::lowering_proof::discharge_reconstructed_obligation(
            &obligation,
            &canonical,
            &self.config,
        );
        Some(match vresult {
            VerificationResult::Valid => {
                debug_assert!(
                    obligation.is_reconstructed(),
                    "reconstruct_alu_obligation must tag Reconstructed provenance"
                );
                InstructionVerificationResult::Verified {
                    proof_name: obligation.name.clone(),
                    category: ProofCategory::Arithmetic,
                    strength,
                    // Credited: a reconstructed obligation is the genuine
                    // (non-degenerate) credit even when structurally X==X.
                    degenerate: !obligation.is_reconstructed(),
                }
            }
            VerificationResult::Invalid { counterexample } => {
                InstructionVerificationResult::Failed {
                    proof_name: obligation.name.clone(),
                    detail: counterexample,
                }
            }
            VerificationResult::Unknown { reason } => InstructionVerificationResult::Failed {
                proof_name: obligation.name.clone(),
                detail: format!("Unknown: {}", reason),
            },
        })
    }

    /// Verify all instructions in a MachFunction.
    ///
    /// This entry point has NO replayed LIR function, so the TV-2 provenance
    /// cross-check cannot run here; the compiler cert path uses
    /// [`Self::verify_with_lir_source`] instead.
    pub fn verify(&self, func: &MachFunction) -> FunctionVerificationReport {
        self.verify_with_lir_source(func, None)
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

    /// Mode-explicit body of [`Self::verify_with_lir_source`] (tests inject
    /// the mode directly to stay independent of ambient env vars).
    fn verify_with_lir_source_and_mode(
        &self,
        func: &MachFunction,
        lir_source: Option<&trust_cg_lower::Function>,
        xcheck_mode: ProvenanceXCheckMode,
    ) -> FunctionVerificationReport {
        // TV-2: index the replayed LIR function. A name mismatch means the
        // caller mis-zipped functions — loudly report and run without the
        // cross-check rather than judging stamps against the wrong spec.
        let lir_index: Option<LirSourceIndex> = match xcheck_mode {
            ProvenanceXCheckMode::Off => None,
            _ => lir_source.and_then(|lir| {
                if lir.name == func.name {
                    Some(LirSourceIndex::build(lir))
                } else {
                    eprintln!(
                        "[TCG-PROVENANCE-XCHECK-WARN] arch=aarch64 fn={} replayed LIR function \
                         name mismatch (got `{}`): provenance cross-check skipped",
                        func.name, lir.name
                    );
                    None
                }
            }),
        };
        let mut attributed_count: usize = 0;
        let mut synthetic_count: usize = 0;
        let mut mismatch_count: usize = 0;

        let mut instructions = Vec::new();

        // Walk all blocks and their instructions.
        for block in &func.blocks {
            for (block_pos, &inst_id) in block.insts.iter().enumerate() {
                let idx = inst_id.0 as usize;
                if idx >= func.insts.len() {
                    continue;
                }
                let inst = &func.insts[idx];

                let result = if let Some(reason) = Self::trap_skip_reason(inst.opcode) {
                    InstructionVerificationResult::Skipped {
                        reason: format!("{:?} is a {}", inst.opcode, reason),
                    }
                } else if inst.opcode.is_pseudo() {
                    InstructionVerificationResult::Skipped {
                        reason: format!("{:?} is a pseudo-instruction", inst.opcode),
                    }
                } else if let Some(recon_result) = self.try_reconstruct_pilot(inst) {
                    // PHASE-2 OPERAND RECONSTRUCTION (PILOT, task #63).
                    //
                    // Pilot ALU opcodes (Add/Sub/Mul/Neg) with a real operand
                    // shape are routed through reconstruction BEFORE the
                    // DB-substring path. The machine side is rebuilt from the REAL
                    // emitted opcode+operands, so a wrong isel choice (e.g. SUB for
                    // Iadd) or wrong operand wiring on a non-commutative op (SUB)
                    // REFUTES. The proof is credited Verified IFF
                    // `is_reconstructed() && Valid`.
                    //
                    // `try_reconstruct_pilot` returns `None` only when the opcode
                    // is not a pilot opcode OR the instruction does not carry a
                    // reconstructable operand shape (e.g. an operand-less test
                    // stub); in that case this arm is skipped and the existing
                    // DB-substring path below runs unchanged — no regression on
                    // any path that previously verified.
                    recon_result
                } else if let Some((query, category)) =
                    Self::inst_to_proof_query_in_block(func, &block.insts, block_pos, inst)
                {
                    // Search the proof database for a matching proof.
                    let matching_proofs = self.db.by_category(category);
                    let proof = matching_proofs
                        .iter()
                        .find(|p| p.obligation.name.to_lowercase().contains(query));

                    match proof {
                        Some(cp) => {
                            // PROOF-2: shared CONTENT-keyed memo (was an
                            // unmemoized per-instance re-evaluation). DB
                            // obligations are fixed for the process lifetime,
                            // so this is a pure compile-time win; the content
                            // key keeps it sound even if a future DB entry
                            // reused a name with different content.
                            //
                            // PROOF-4 B1: prefer a tier-0 candidate after live
                            // revalidation over the statistical sweep for >8-bit
                            // registry obligations (stronger). A miss
                            // keeps the sweep, so nothing that verified before
                            // regresses; `strength` is `Formal` on a tier-0 hit.
                            let (vresult, strength) =
                                crate::lowering_proof::discharge_registry_obligation(
                                    &cp.obligation,
                                    &self.config,
                                );
                            match vresult {
                                // The per-instruction `Verified` records that the
                                // bound lowering proof DISCHARGED (the provenance /
                                // cert-chain binding the compile pipeline consumes).
                                // STRICT proven-honesty (task #61) is applied at the
                                // TALLY level — `genuinely_verified_count`,
                                // `coverage_percent`, `all_verified` — which credit
                                // ONLY non-degenerate proofs via the `degenerate`
                                // flag carried here. A degenerate (X==X) proof is
                                // still recorded as a binding but contributes ZERO
                                // to any proven/covered/verified count.
                                VerificationResult::Valid => {
                                    InstructionVerificationResult::Verified {
                                        proof_name: cp.obligation.name.clone(),
                                        category,
                                        strength,
                                        degenerate: cp.obligation.is_degenerate(),
                                    }
                                }
                                VerificationResult::Invalid { counterexample } => {
                                    InstructionVerificationResult::Failed {
                                        proof_name: cp.obligation.name.clone(),
                                        detail: counterexample,
                                    }
                                }
                                VerificationResult::Unknown { reason } => {
                                    InstructionVerificationResult::Failed {
                                        proof_name: cp.obligation.name.clone(),
                                        detail: format!("Unknown: {}", reason),
                                    }
                                }
                            }
                        }
                        None => InstructionVerificationResult::Unverified {
                            reason: format!(
                                "no proof matching '{}' in category {:?}",
                                query, category
                            ),
                        },
                    }
                } else {
                    InstructionVerificationResult::Unverified {
                        reason: format!("no proof mapping for opcode {:?}", inst.opcode),
                    }
                };

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
                        aarch64_emitted_op_class(inst),
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

                instructions.push(InstructionReport {
                    inst_index: idx,
                    opcode: InstructionOpcode::AArch64(inst.opcode),
                    result,
                });
            }
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

        FunctionVerificationReport {
            function_name: func.name.clone(),
            instructions,
        }
    }
}

impl Default for FunctionVerifier {
    fn default() -> Self {
        Self::new()
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
mod tests {
    use super::*;
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

    fn make_func_with_insts(insts: Vec<MachInst>) -> MachFunction {
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

    fn inst_with_operands(opcode: AArch64Opcode, operands: Vec<MachOperand>) -> MachInst {
        MachInst::new(opcode, operands)
    }

    fn assert_verified_with_proof(
        opcode: AArch64Opcode,
        expected_category: ProofCategory,
        proof_substring: &str,
    ) {
        let func = make_func_with_insts(vec![inst(opcode)]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 1);
        assert_eq!(report.unverified_count(), 0);
        match &report.instructions[0].result {
            InstructionVerificationResult::Verified {
                proof_name,
                category,
                ..
            } => {
                assert_eq!(*category, expected_category);
                assert!(
                    proof_name.contains(proof_substring),
                    "unexpected {opcode:?} proof name: {proof_name}"
                );
            }
            other => panic!("expected Verified result for {opcode:?}, got {other:?}"),
        }
    }

    /// Assert an opcode is Unverified because its only DB proof was a degenerate
    /// X==X that was retracted (#62) — i.e. `opcode_to_proof_query` now returns
    /// None and the opcode is FailClosedAllowlisted in the coverage gate.
    fn assert_unverified_no_proof(opcode: AArch64Opcode) {
        assert!(
            FunctionVerifier::opcode_to_proof_query(opcode).is_none(),
            "{opcode:?}: expected no proof mapping after #62 retraction"
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
        let func = make_func_with_insts(vec![inst(AArch64Opcode::AddRR), inst(AArch64Opcode::Nop)]);
        let report = verify_function(&func);
        let inventory = report.emitted_opcode_inventory();

        assert_eq!(inventory.entries.len(), 2);
        assert_eq!(
            inventory.entries[0].opcode,
            InstructionOpcode::AArch64(AArch64Opcode::AddRR)
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
    fn adrp_addpcrel_address_pair_is_per_compile_promotable() {
        // The ADRP page + ADD lo12 PC-relative address-materialization pair is now
        // credited to the AY-discharged MachO data-relocation proofs (PAGE21
        // `ADRP == page(S+A)`; PAGEOFF12 `ADRP+ADD == S+A`), so an address
        // materialization no longer blocks per-compile proof promotion — it did
        // before (the gate rejected every aarch64 function touching a global).
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::Adrp),
            inst(AArch64Opcode::AddPCRel),
            inst(AArch64Opcode::Ret),
        ]);
        let report = verify_function(&func);
        let inventory = report.emitted_opcode_inventory();
        assert_eq!(
            inventory.entries[0].status,
            OpcodeInventoryStatus::Verified,
            "ADRP must be Verified via the PAGE21 page proof; got {:?}",
            inventory.entries[0].detail
        );
        assert_eq!(
            inventory.entries[1].status,
            OpcodeInventoryStatus::Verified,
            "AddPCRel must be Verified via the PAGEOFF12 full-address proof; got {:?}",
            inventory.entries[1].detail
        );
        assert!(
            inventory.is_promotable(),
            "ADRP+ADD+Ret must be per-compile promotable; rejection: {:?}",
            inventory.promotion_rejection_reason()
        );
    }

    #[test]
    fn direct_branch_and_call_are_per_compile_promotable() {
        // B / BL (direct PC-relative branch/call) are credited to the BRANCH26
        // call-relocation proof; the indirect Br/Blr/BLR are CoveredElsewhere. So
        // a function mixing a direct call, a direct branch, an indirect branch and
        // a return now promotes — the last control-flow blocker for the per-compile
        // proof gate on aarch64.
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::Bl),
            inst(AArch64Opcode::B),
            inst(AArch64Opcode::Br),
            inst(AArch64Opcode::Ret),
        ]);
        let report = verify_function(&func);
        let inventory = report.emitted_opcode_inventory();
        assert_eq!(
            inventory.entries[0].status,
            OpcodeInventoryStatus::Verified,
            "BL must be Verified via the BRANCH26 call-target proof; got {:?}",
            inventory.entries[0].detail
        );
        assert_eq!(
            inventory.entries[1].status,
            OpcodeInventoryStatus::Verified,
            "B must be Verified via the BRANCH26 proof; got {:?}",
            inventory.entries[1].detail
        );
        assert!(
            inventory.is_promotable(),
            "Bl/B/Br/Ret must be per-compile promotable; rejection: {:?}",
            inventory.promotion_rejection_reason()
        );
    }

    #[test]
    fn neon_bytesum_structural_opcodes_are_per_compile_promotable() {
        // The full set of NEON opcodes a byte-widening reduction vectorizer emits.
        // CNT/UADDLP/ADD are Verified via their faithful lowering proofs; UMOV via
        // the all_neon_umov_proofs matrix; the paired Q load/store via the shared
        // Ldr*/Str* Memory debt; MOVI via constant-materialization covered-elsewhere.
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::NeonMovi),
            inst(AArch64Opcode::NeonLdpQPost),
            inst(AArch64Opcode::NeonCntV),
            inst(AArch64Opcode::NeonUaddlpV),
            inst(AArch64Opcode::NeonAddV),
            inst(AArch64Opcode::NeonUmovGen),
            inst(AArch64Opcode::NeonStpQPost),
            inst(AArch64Opcode::Ret),
        ]);
        let report = verify_function(&func);
        let inventory = report.emitted_opcode_inventory();
        assert!(
            inventory.is_promotable(),
            "the NEON byte-reduction opcode set must be per-compile promotable; rejection: {:?}",
            inventory.promotion_rejection_reason()
        );
        // MOVI promotes via the disclosed const-materialization identity proof
        // (`NeonEncoding: MOVI immediate 16B`), like scalar Movz — Verified but
        // credits zero in the STRICT proven tally.
        assert_eq!(
            inventory.entries[0].status,
            OpcodeInventoryStatus::Verified,
            "NeonMovi must be Verified via the MOVI-immediate const-mat proof; got {:?}",
            inventory.entries[0].detail
        );
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
    fn writeback_and_literal_memory_forms_are_per_compile_promotable() {
        // Pre/post-index writeback loads/stores + the PC-relative literal load
        // carry the same Ldr*/Str* memory debt as scalar loads (and the already
        // credited post-index NeonLdpQPost) — a function using them must promote.
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::LdrPostIndex),
            inst(AArch64Opcode::StrPreIndex),
            inst(AArch64Opcode::LdrLiteral),
            inst(AArch64Opcode::Ret),
        ]);
        let inventory = verify_function(&func).emitted_opcode_inventory();
        assert!(
            inventory.is_promotable(),
            "writeback/literal memory forms must promote; rejection: {:?}",
            inventory.promotion_rejection_reason()
        );
    }

    #[test]
    fn proven_but_unwired_and_const_mat_opcodes_promote() {
        // The batch wired from their EXISTING registered proofs: EorRRShift
        // (bitwise ROR-shift), MovI (const-mat), AddTprelHi12/Lo12 (TLS reloc),
        // Cas (compare-and-swap), Ldar/Stlr (atomic load/store).
        for op in [
            AArch64Opcode::EorRRShift,
            AArch64Opcode::AddRRShift,
            AArch64Opcode::SubRRShift,
            AArch64Opcode::AddRRShiftLsr,
            // Widening multiply-accumulate-long — proven + gate-registered, wired
            // from their FAITHFUL all_neon_smlal_proofs obligations.
            AArch64Opcode::NeonSmlalV,
            AArch64Opcode::NeonSmlal2V,
            AArch64Opcode::NeonUmlalV,
            AArch64Opcode::NeonUmlal2V,
            // Widening add-wide — proven + gate-registered, wired from their
            // FAITHFUL all_neon_uaddw_proofs obligations.
            AArch64Opcode::NeonUaddwV,
            AArch64Opcode::NeonUaddw2V,
            // SIGNED widening add-wide — proven + gate-registered, wired from
            // their FAITHFUL all_neon_saddw_proofs obligations (the
            // neon_predsum widening i64-acc condsum accumulate).
            AArch64Opcode::NeonSaddwV,
            AArch64Opcode::NeonSaddw2V,
            // Vector multiply-accumulate + pairwise widening accumulate —
            // proven + gate-registered, wired from their FAITHFUL
            // all_neon_mla_proofs / all_neon_uadalp_proofs obligations (the
            // neon_predsum MLA-by-mask condsum accumulate and the neon_array
            // TRACK D abs-sum accumulate).
            AArch64Opcode::NeonMlaV,
            AArch64Opcode::NeonUadalpV,
            AArch64Opcode::MovI,
            AArch64Opcode::AddTprelHi12,
            AArch64Opcode::AddTprelLo12,
            AArch64Opcode::Cas,
            AArch64Opcode::Ldar,
            AArch64Opcode::Stlr,
            // LSE fetch-op RMW (fetch_add/or/xor/and) via updates_mem proofs.
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
            let func = make_func_with_insts(vec![tested, inst(AArch64Opcode::Ret)]);
            let inv = verify_function(&func).emitted_opcode_inventory();
            assert!(
                inv.is_promotable(),
                "{op:?} must promote per-compile; rejection: {:?}",
                inv.promotion_rejection_reason()
            );
        }
    }

    #[test]
    fn atomic_swap_and_exclusive_still_block_promotion() {
        // NARROWNESS: SWP and the LL/SC exclusives have NO retained proof
        // (`all_atomic_proofs()` retracted the degenerate "returns old value"
        // obligation), so they MUST keep blocking — the atomic credits above do
        // not leak to them.
        for op in [
            AArch64Opcode::Swp,
            AArch64Opcode::Swpal,
            AArch64Opcode::Ldaxr,
        ] {
            assert!(
                FunctionVerifier::opcode_to_proof_query(op).is_none(),
                "{op:?} must have NO proof query (retracted/unproven)"
            );
            let func = make_func_with_insts(vec![inst(op), inst(AArch64Opcode::Ret)]);
            assert!(
                !verify_function(&func)
                    .emitted_opcode_inventory()
                    .is_promotable(),
                "{op:?} must keep blocking per-compile promotion"
            );
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
    fn neon_lane_select_permutes_now_promote_via_per_lane_proofs() {
        // These two register-data permutes SELECT a lane — NeonDupElem (broadcast
        // a CHOSEN vector lane) and NeonInsGen (insert into a CHOSEN lane) — and
        // used to be pinned here as fail-closed BLOCKERS. The stated concern was
        // exact and correct at the time: "a mis-wired lane SELECTION must never
        // slip through", and nothing then constrained the lane axis.
        //
        // That concern is now discharged by PROOF rather than by blocking. Both
        // opcodes carry FAITHFUL per-(arrangement, LANE) obligations
        // (all_neon_dup_elem_proofs / all_neon_ins_gen_proofs) covering EVERY lane
        // of every emitted element size, and their wrong-LANE negative controls
        // REFUTE (neon_dup_elem_wrong_encoding_controls /
        // neon_ins_gen_wrong_encoding_controls). A mis-wired lane selection is
        // therefore caught by the obligation, which is strictly stronger than
        // refusing to promote.
        //
        // Same transition NeonRbitV made above — see
        // `neon_rbitv_bit_reverse_promotes`.
        for op in [AArch64Opcode::NeonDupElem, AArch64Opcode::NeonInsGen] {
            assert!(
                FunctionVerifier::opcode_to_proof_query(op).is_some(),
                "{op:?} must now have a proof query (faithful per-lane obligations)"
            );
            let func = make_func_with_insts(vec![inst(op), inst(AArch64Opcode::Ret)]);
            let inventory = verify_function(&func).emitted_opcode_inventory();
            assert!(
                inventory.is_promotable(),
                "{op:?} must be per-compile promotable now that every emitted lane is \
                 proven; rejection: {:?}",
                inventory.promotion_rejection_reason()
            );
        }
    }

    #[test]
    fn neon_rbitv_bit_reverse_promotes() {
        // NeonRbitV (`RBIT.16B` — the per-byte 8-bit reverse the neon-bitrev
        // vectorizer emits for `a[i].reverse_bits()`) is bound to the FAITHFUL
        // proof_neon_rbitv_16b obligation via opcode_to_proof_query, so a
        // function emitting it must PROMOTE per-compile (the reverse portion of
        // k4_bitrev pairs it with the covered NeonLdpQPost/NeonStpQPost Q
        // load/store).
        assert!(
            FunctionVerifier::opcode_to_proof_query(AArch64Opcode::NeonRbitV).is_some(),
            "NeonRbitV must have a proof query (faithful RBIT.16B obligation)"
        );
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::NeonLdpQPost),
            inst(AArch64Opcode::NeonRbitV),
            inst(AArch64Opcode::NeonStpQPost),
            inst(AArch64Opcode::Ret),
        ]);
        let inventory = verify_function(&func).emitted_opcode_inventory();
        assert!(
            inventory.is_promotable(),
            "the NEON per-byte bit-reverse opcode set must be per-compile promotable; \
             rejection: {:?}",
            inventory.promotion_rejection_reason()
        );
    }

    #[test]
    fn neon_dup_gen_broadcast_is_promotable() {
        // NeonDupGen (broadcast a GPR to ALL lanes) promotes via the disclosed
        // `NeonEncoding: DUP broadcast` identity — the NeonMovi posture.
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::NeonDupGen),
            inst(AArch64Opcode::Ret),
        ]);
        assert!(
            verify_function(&func)
                .emitted_opcode_inventory()
                .is_promotable(),
            "NeonDupGen (broadcast-all) must promote via the DUP-broadcast identity"
        );
    }

    #[test]
    fn test_fmov_cross_class_bitcasts_are_covered_elsewhere_and_promotable() {
        // The two scalar cross-class FMOV bitcasts (FPR<->GPR) implement the
        // bit-preserving f64::to_bits / from_bits / copysign reinterpret. They have
        // no per-instruction value-proof (that would be the degenerate X==X), but
        // they are a PURE matched-width bit copy — structurally covered exactly like
        // FmovFprFpr / MovR — so the inventory marks them CoveredElsewhere and the
        // function is per-compile promotable. This is what lets the float bitcast
        // helpers (to_bits/from_bits/copysign) compile under the proof gate.
        for opcode in [AArch64Opcode::FmovFprGpr, AArch64Opcode::FmovGprFpr] {
            let func = make_func_with_insts(vec![inst(opcode)]);
            let report = verify_function(&func);
            let inventory = report.emitted_opcode_inventory();
            assert_eq!(
                inventory.entries[0].status,
                OpcodeInventoryStatus::CoveredElsewhere,
                "{opcode:?} must be CoveredElsewhere (bit-preserving cross-class copy)"
            );
            assert!(
                inventory.is_promotable(),
                "{opcode:?} must be per-compile promotable; rejection: {:?}",
                inventory.promotion_rejection_reason()
            );
            assert_eq!(inventory.promotion_rejection_reason(), None);
        }

        // CONTROL: an unrelated genuinely-uncovered opcode (CSINV — no proof, NOT
        // covered-elsewhere) stays Unverified and BLOCKS promotion. The
        // covered-elsewhere reclassification must NOT leak to real gaps.
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
    fn common_aarch64_function_shape_is_per_compile_promotable() {
        // CAPSTONE: the full common aarch64 function shape — integer ALU, frame
        // load/store, global address materialization (ADRP+ADD), a direct call
        // (BL), conditional + unconditional branches, and a return. With the
        // control-flow/address relocation proofs wired (ADRP/ADD PAGE21/PAGEOFF12,
        // B/BL BRANCH26) plus the pre-existing data/memory/BCond/Ret coverage, the
        // per-compile proof-promotion gate is CLEAN for such a function: the
        // compiler can verify EVERY instruction it emits, with TCG_NO_PROOF_CERTS
        // off. (The remaining fail-closed opcodes are exotic — i128 carry-chain,
        // NEON, bitfield, atomics, GOT/TLS.)
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
        let inventory = report.emitted_opcode_inventory();
        assert!(
            inventory.is_promotable(),
            "the common aarch64 function shape must be per-compile promotable; rejection: {:?}",
            inventory.promotion_rejection_reason()
        );
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
    // 2-9. Single verified instructions
    // =======================================================================

    #[test]
    fn test_single_add_verified() {
        let func = make_func_with_insts(vec![inst(AArch64Opcode::AddRR)]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 1);
        assert_eq!(report.verified_count(), 1);
        assert!(report.instructions[0].result.is_verified());
    }

    #[test]
    fn test_single_sub_verified() {
        let func = make_func_with_insts(vec![inst(AArch64Opcode::SubRR)]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 1);
    }

    #[test]
    fn test_single_mul_verified() {
        let func = make_func_with_insts(vec![inst(AArch64Opcode::MulRR)]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 1);
    }

    #[test]
    fn test_single_madd_verified() {
        let func = make_func_with_insts(vec![inst(AArch64Opcode::Madd)]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 1);
        match &report.instructions[0].result {
            InstructionVerificationResult::Verified { proof_name, .. } => {
                assert_eq!(proof_name, "AArch64 MADD_RR generic");
            }
            other => panic!("expected Verified result for Madd, got {other:?}"),
        }
    }

    #[test]
    fn test_single_msub_verified() {
        let func = make_func_with_insts(vec![inst(AArch64Opcode::Msub)]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 1);
        match &report.instructions[0].result {
            InstructionVerificationResult::Verified { proof_name, .. } => {
                assert_eq!(proof_name, "AArch64 MSUB_RR generic");
            }
            other => panic!("expected Verified result for Msub, got {other:?}"),
        }
    }

    #[test]
    fn test_single_neg_verified() {
        let func = make_func_with_insts(vec![inst(AArch64Opcode::Neg)]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 1);
    }

    #[test]
    fn test_sdiv_verified() {
        let func = make_func_with_insts(vec![inst(AArch64Opcode::SDiv)]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 1);
    }

    #[test]
    fn test_udiv_verified() {
        let func = make_func_with_insts(vec![inst(AArch64Opcode::UDiv)]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 1);
    }

    // =======================================================================
    // 8-9. Comparison and branch
    // =======================================================================

    #[test]
    fn test_cmp_verified() {
        let func = make_func_with_insts(vec![inst(AArch64Opcode::CmpRR)]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 1);
        if let InstructionVerificationResult::Verified { category, .. } =
            &report.instructions[0].result
        {
            assert_eq!(*category, ProofCategory::Comparison);
        } else {
            panic!("expected Verified result for CmpRR");
        }
    }

    #[test]
    fn test_bcond_verified() {
        let func = make_func_with_insts(vec![inst(AArch64Opcode::BCond)]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 1);
        if let InstructionVerificationResult::Verified { category, .. } =
            &report.instructions[0].result
        {
            assert_eq!(*category, ProofCategory::Branch);
        } else {
            panic!("expected Verified result for BCond");
        }
    }

    // =======================================================================
    // 10-11. Memory
    // =======================================================================

    #[test]
    fn test_load_verified() {
        let func = make_func_with_insts(vec![inst(AArch64Opcode::LdrRI)]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 1);
        if let InstructionVerificationResult::Verified { category, .. } =
            &report.instructions[0].result
        {
            assert_eq!(*category, ProofCategory::Memory);
        } else {
            panic!("expected Verified result for LdrRI");
        }
    }

    #[test]
    fn test_store_verified() {
        let func = make_func_with_insts(vec![inst(AArch64Opcode::StrRI)]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 1);
        if let InstructionVerificationResult::Verified { category, .. } =
            &report.instructions[0].result
        {
            assert_eq!(*category, ProofCategory::Memory);
        } else {
            panic!("expected Verified result for StrRI");
        }
    }

    // =======================================================================
    // 12. Floating-point
    // =======================================================================

    #[test]
    fn test_fadd_verified() {
        let func = make_func_with_insts(vec![inst(AArch64Opcode::FaddRR)]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 1);
        if let InstructionVerificationResult::Verified { category, .. } =
            &report.instructions[0].result
        {
            assert_eq!(*category, ProofCategory::FloatingPoint);
        } else {
            panic!("expected Verified result for FaddRR");
        }
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
            inst(AArch64Opcode::AddRR), // verified
            inst(AArch64Opcode::Phi),   // skipped
            inst(AArch64Opcode::Ret),   // unverified (#62: RET proof retracted)
            inst(AArch64Opcode::SubRR), // verified
            inst(AArch64Opcode::Nop),   // skipped
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 5);
        assert_eq!(report.verified_count(), 2);
        assert_eq!(report.skipped_count(), 2);
        assert_eq!(report.unverified_count(), 1);
    }

    // =======================================================================
    // 15. 100% coverage
    // =======================================================================

    #[test]
    fn test_coverage_100_percent() {
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::AddRR),
            inst(AArch64Opcode::SubRR),
            inst(AArch64Opcode::MulRR),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 3);
        assert_eq!(report.coverage_percent(), 100.0);
        assert!(report.all_verified());
    }

    // =======================================================================
    // 16. RET no longer contributes to verified coverage (#62: proof retracted).
    // =======================================================================

    #[test]
    fn test_add_verified_ret_unverified_after_retraction() {
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::AddRR), // verified (genuine add proof)
            inst(AArch64Opcode::Ret),   // unverified (#62: RET X==X proof retracted)
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
            inst(AArch64Opcode::AddRR), // verified
            inst(AArch64Opcode::Br),    // unverified (branch target)
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
        func.insts.push(inst(AArch64Opcode::AddRR));
        func.blocks[0].insts.push(InstId(0));

        // Create block 1
        let mut block1 = trust_cg_ir::MachBlock::new();
        func.insts.push(inst(AArch64Opcode::SubRR));
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
    fn test_and_or_eor_verified() {
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::AndRR),
            inst(AArch64Opcode::OrrRR),
            inst(AArch64Opcode::EorRR),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 3);
        for ir in &report.instructions {
            if let InstructionVerificationResult::Verified { category, .. } = &ir.result {
                // Logical ops must be discharged by the GENERAL bitwise proofs
                // (BitwiseShift), NOT degenerate Peephole rewrite identities.
                assert_eq!(*category, ProofCategory::BitwiseShift);
            } else {
                panic!("expected Verified for logical ops");
            }
        }
    }

    // =======================================================================
    // 23. Shift ops verified
    // =======================================================================

    #[test]
    fn test_shift_ops_verified() {
        // #62: the static degenerate Ishl/Ushr/Sshr -> SHL/LSL/LSR/ASR proofs were
        // RETRACTED. Shift opcodes are now covered by OPERAND RECONSTRUCTION (the
        // machine side is rebuilt from the REAL opcode+operands with the faithful
        // hardware-amount-masked encoder under the #57 amount<width precondition).
        // Build instructions with real reconstructable operand shapes and assert
        // they verify via reconstruction (category Arithmetic, non-degenerate).
        let func = make_func_with_insts(vec![
            representative_reconstructable_inst(AArch64Opcode::LslRR).unwrap(),
            representative_reconstructable_inst(AArch64Opcode::LsrRR).unwrap(),
            representative_reconstructable_inst(AArch64Opcode::AsrRR).unwrap(),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 3);
        for ir in &report.instructions {
            if let InstructionVerificationResult::Verified {
                category,
                degenerate,
                ..
            } = &ir.result
            {
                assert_eq!(*category, ProofCategory::Arithmetic);
                assert!(
                    !degenerate,
                    "reconstructed shift must be non-degenerate credit"
                );
            } else {
                panic!(
                    "expected Verified (via reconstruction) for shift ops, got {:?}",
                    ir.result
                );
            }
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
        // reinterpret moves) have NO per-instruction value-proof: an obligation
        // would be the degenerate X==X (FP value and IEEE bits share one bitvector
        // domain). At the INSTRUCTION level they are Unverified-no-proof exactly
        // like FmovFprFpr; their correctness is structural (pure matched-width bit
        // copy), credited at the INVENTORY level as CoveredElsewhere — see
        // `test_fmov_cross_class_bitcasts_are_covered_elsewhere_and_promotable`.
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
    fn test_generated_scalar_extensions_verified() {
        for (opcode, proof_substring) in [
            (AArch64Opcode::Sxtb, "Sextend_I8_to_I32 -> SXTB"),
            (AArch64Opcode::Sxth, "Sextend_I16_to_I32 -> SXTH"),
            (AArch64Opcode::Sxtw, "Sextend_I32_to_I64 -> SXTW"),
            (AArch64Opcode::Uxtb, "Uextend_I8_to_I32 -> UXTB"),
            (AArch64Opcode::Uxth, "Uextend_I16_to_I32 -> UXTH"),
        ] {
            assert_verified_with_proof(opcode, ProofCategory::ExtensionTruncation, proof_substring);
        }
    }

    #[test]
    fn test_uxtw_verified_as_generated_zero_extend() {
        assert_verified_with_proof(
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
    fn test_generated_scalar_extension_sequence_has_full_verifier_coverage() {
        // Extension ops verify; the trailing RET (proof retracted #62) is tested
        // separately and excluded from this extension-coverage sequence.
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
        assert_eq!(report.verified_count(), 6);
        assert_eq!(report.unverified_count(), 0);
        assert!(report.all_verified());
    }

    #[test]
    fn test_generated_cli_add_sequence_covers_uxtw() {
        // #62: MovR (degenerate CopyProp X==X) and RET (degenerate RET X==X) proofs
        // were retracted, so those forms are now Unverified. This test's subject is
        // that the generated add-with-UXTW sequence's frame-pair/ADD/UXTW/load-store
        // ops all verify; the retracted copy/return forms are excluded.
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
        assert_eq!(report.verified_count(), 9);
        assert_eq!(report.unverified_count(), 0);
        assert!(report.all_verified());
    }

    // =======================================================================
    // 27. Generated frame prologue/epilogue pair instructions are verified
    // =======================================================================

    #[test]
    fn test_stp_preindex_verified_as_generated_frame_prologue() {
        assert_verified_with_proof(
            AArch64Opcode::StpPreIndex,
            ProofCategory::FrameLayout,
            "SP alignment preserved",
        );
    }

    #[test]
    fn test_stp_ri_verified_as_generated_callee_save_store() {
        assert_verified_with_proof(
            AArch64Opcode::StpRI,
            ProofCategory::FrameLayout,
            "callee-save pair slots don't overlap",
        );
    }

    #[test]
    fn test_ldp_pair_loads_verified_as_generated_callee_save_restore() {
        assert_verified_with_proof(
            AArch64Opcode::LdpRI,
            ProofCategory::FrameLayout,
            "callee-save restore is identity",
        );
        assert_verified_with_proof(
            AArch64Opcode::LdpPostIndex,
            ProofCategory::FrameLayout,
            "callee-save restore is identity",
        );
    }

    #[test]
    fn test_generated_frame_sequence_has_full_verifier_coverage() {
        // The frame prologue/epilogue PAIR opcodes verify; the trailing RET is
        // tested separately (its degenerate proof was retracted in #62, so it is
        // now Unverified and excluded from this frame-op coverage sequence).
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
        assert_eq!(report.verified_count(), 6);
        assert_eq!(report.unverified_count(), 0);
        assert!(report.all_verified());
    }

    #[test]
    fn test_generated_frame_pair_mappings_resolve_typed_check_kind() {
        let db = ProofDatabase::new();
        for opcode in [
            AArch64Opcode::StpPreIndex,
            AArch64Opcode::StpRI,
            AArch64Opcode::LdpRI,
            AArch64Opcode::LdpPostIndex,
        ] {
            let (query, category) = FunctionVerifier::opcode_to_proof_query(opcode)
                .expect("generated frame opcode must map to a proof query");
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
    fn test_generated_large_frame_offset_materialization_verified() {
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
        assert_eq!(report.verified_count(), 2);
        assert_eq!(report.unverified_count(), 0);

        // task #63: AddRR/SubRR are PILOT opcodes, so a frame-address
        // materialization `ADD X16, FP, X16` / `SUB X17, SP, X17` now routes
        // through OPERAND RECONSTRUCTION (it is a genuine Iadd/Isub over the real
        // operands) rather than the degenerate FrameLayout DB binding. The
        // reconstructed obligation discharges Valid and is credited GENUINELY
        // (not a degenerate binding) — strictly stronger than the prior path.
        for inst_report in report.instructions.iter() {
            match &inst_report.result {
                InstructionVerificationResult::Verified {
                    proof_name,
                    category,
                    ..
                } => {
                    assert_eq!(*category, ProofCategory::Arithmetic);
                    assert!(
                        proof_name.contains("RECONSTRUCTED"),
                        "expected reconstructed pilot proof, got: {proof_name}"
                    );
                }
                other => panic!("expected reconstructed Verified result, got {other:?}"),
            }
        }
        // Genuinely (non-degenerately) verified: the reconstruction credit.
        assert_eq!(report.genuinely_verified_count(), 2);
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
        assert_eq!(report.verified_count(), 1);

        match &report.instructions[0].result {
            InstructionVerificationResult::Verified {
                proof_name,
                category,
                ..
            } => {
                assert_eq!(*category, ProofCategory::Arithmetic);
                assert!(
                    proof_name.to_lowercase().contains("add"),
                    "unexpected generic add proof name: {proof_name}"
                );
            }
            other => panic!("expected generic arithmetic proof, got {other:?}"),
        }
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
    fn test_generated_fp_sp_relative_addressing_verified() {
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
        assert_eq!(report.verified_count(), 2);
        assert_eq!(report.unverified_count(), 0);

        // task #63: AddRI/SubRI are PILOT opcodes, so `ADD X0, SP, #32` /
        // `SUB X1, FP, #512` now route through OPERAND RECONSTRUCTION (genuine
        // Iadd/Isub with the real immediate bound as a bv_const) rather than the
        // degenerate FrameLayout DB binding. Credited GENUINELY.
        for inst_report in &report.instructions {
            match &inst_report.result {
                InstructionVerificationResult::Verified {
                    proof_name,
                    category,
                    ..
                } => {
                    assert_eq!(*category, ProofCategory::Arithmetic);
                    assert!(
                        proof_name.contains("RECONSTRUCTED"),
                        "expected reconstructed pilot proof, got: {proof_name}"
                    );
                }
                other => panic!("expected reconstructed Verified result, got {other:?}"),
            }
        }
        assert_eq!(report.genuinely_verified_count(), 2);
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
        assert_eq!(report.verified_count(), 2);

        for inst_report in &report.instructions {
            match &inst_report.result {
                InstructionVerificationResult::Verified {
                    proof_name,
                    category,
                    ..
                } => {
                    assert_eq!(*category, ProofCategory::Arithmetic);
                    assert!(
                        proof_name.to_lowercase().contains("add")
                            || proof_name.to_lowercase().contains("sub"),
                        "unexpected generic arithmetic proof name: {proof_name}"
                    );
                }
                other => panic!("expected generic arithmetic proof, got {other:?}"),
            }
        }
    }

    // =======================================================================
    // 28. Generated constant materialization moves are verified
    // =======================================================================

    #[test]
    fn test_generated_const_materialization_moves_verified() {
        let movz = inst_with_operands(
            AArch64Opcode::Movz,
            vec![
                MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::Imm(42),
            ],
        );
        let report = verify_function(&make_func_with_insts(vec![movz]));
        assert_eq!(report.verified_count(), 1);
        assert!(matches!(
            &report.instructions[0].result,
            InstructionVerificationResult::Verified {
                proof_name,
                category: ProofCategory::ConstantMaterialization,
                ..
            } if proof_name.contains("MOVZ #imm16, LSL #0")
        ));

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
            let report = verify_function(&make_func_with_insts(vec![alias]));
            assert_eq!(report.verified_count(), 1);
            assert!(matches!(
                &report.instructions[0].result,
                InstructionVerificationResult::Verified {
                    proof_name,
                    category: ProofCategory::ConstantMaterialization,
                    ..
                } if proof_name.contains("MOVZ #imm16, LSL #0")
            ));
        }

        let movn = inst_with_operands(
            AArch64Opcode::Movn,
            vec![
                MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::Imm(7),
            ],
        );
        let report = verify_function(&make_func_with_insts(vec![movn]));
        assert_eq!(report.verified_count(), 1);
        assert!(matches!(
            &report.instructions[0].result,
            InstructionVerificationResult::Verified {
                proof_name,
                category: ProofCategory::ConstantMaterialization,
                ..
            } if proof_name.contains("MOVN Xd #imm16, LSL #0")
        ));

        // MOVK now binds to a faithful PER-FORM halfword-splice obligation: one
        // proof per architecturally legal (width, shift), whose reference side is
        // an independent concat/extract splice. Every legal X-form slot verifies,
        // and each binds to the proof for ITS OWN slot (never another's).
        for shift in [0i64, 16, 32, 48] {
            let movk = inst_with_operands(
                AArch64Opcode::Movk,
                vec![
                    MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                    MachOperand::Imm(1),
                    MachOperand::Imm(shift),
                ],
            );
            let report = verify_function(&make_func_with_insts(vec![movk]));
            assert_eq!(report.verified_count(), 1, "X-form MOVK LSL #{shift}");
            // STRICT tally: the splice obligation is a NON-DEGENERATE proof
            // (independent concat/extract reference side), so it must credit
            // the genuinely-verified count — not just the binding count.
            assert_eq!(
                report.genuinely_verified_count(),
                1,
                "X-form MOVK LSL #{shift} splice proof must be non-degenerate"
            );
            let expected = format!("LSL #{shift} splices halfword");
            assert!(
                matches!(
                    &report.instructions[0].result,
                    InstructionVerificationResult::Verified {
                        proof_name,
                        category: ProofCategory::ConstantMaterialization,
                        ..
                    } if proof_name.contains(&expected) && proof_name.contains("Xd")
                ),
                "X-form MOVK LSL #{shift} bound to the wrong proof: {:?}",
                report.instructions[0].result
            );
        }

        // W-form MOVK admits only LSL #0/#16; #32/#48 are architecturally illegal
        // and must NOT inherit an X-form slot's credit.
        for (shift, want_verified) in [(0i64, true), (16, true), (32, false), (48, false)] {
            let movk = inst_with_operands(
                AArch64Opcode::Movk,
                vec![
                    MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr32)),
                    MachOperand::Imm(1),
                    MachOperand::Imm(shift),
                ],
            );
            let report = verify_function(&make_func_with_insts(vec![movk]));
            if want_verified {
                assert_eq!(report.verified_count(), 1, "W-form MOVK LSL #{shift}");
                assert_eq!(
                    report.genuinely_verified_count(),
                    1,
                    "W-form MOVK LSL #{shift} splice proof must be non-degenerate"
                );
                assert!(
                    matches!(
                        &report.instructions[0].result,
                        InstructionVerificationResult::Verified { proof_name, .. }
                            if proof_name.contains("Wd")
                    ),
                    "W-form MOVK LSL #{shift} must bind the W-form proof"
                );
            } else {
                assert_eq!(
                    report.verified_count(),
                    0,
                    "illegal W-form MOVK LSL #{shift} must not be credited"
                );
                assert_eq!(report.unverified_count(), 1);
            }
        }
    }

    #[test]
    fn movn_per_form_binding_covers_all_legal_forms_and_refuses_illegal_w_shifts() {
        // MOVN binds to a faithful PER-FORM inverted-field obligation: one proof
        // per architecturally legal (width, shift), whose reference side is an
        // independent concat/XOR inverted-field algebra. Every legal X-form slot
        // verifies, each binding the proof for ITS OWN slot (never another's).
        for shift in [0i64, 16, 32, 48] {
            let movn = inst_with_operands(
                AArch64Opcode::Movn,
                vec![
                    MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                    MachOperand::Imm(1),
                    MachOperand::Imm(shift),
                ],
            );
            let report = verify_function(&make_func_with_insts(vec![movn]));
            assert_eq!(report.verified_count(), 1, "X-form MOVN LSL #{shift}");
            // STRICT tally: the inverted-field obligation is a NON-DEGENERATE
            // proof (independent concat/XOR reference side), so it must credit
            // the genuinely-verified count — not just the binding count.
            assert_eq!(
                report.genuinely_verified_count(),
                1,
                "X-form MOVN LSL #{shift} inverted-field proof must be non-degenerate"
            );
            let expected = format!("LSL #{shift} inverts halfword");
            assert!(
                matches!(
                    &report.instructions[0].result,
                    InstructionVerificationResult::Verified {
                        proof_name,
                        category: ProofCategory::ConstantMaterialization,
                        ..
                    } if proof_name.contains(&expected) && proof_name.contains("Xd")
                ),
                "X-form MOVN LSL #{shift} bound to the wrong proof: {:?}",
                report.instructions[0].result
            );
        }

        // W-form MOVN admits only LSL #0/#16, and its proof pins the 32-bit
        // complement + zero-extension (upper 32 bits zero) — the width
        // semantics that used to keep W-form MOVN unverifiable. #32/#48 are
        // architecturally illegal and must NOT inherit an X-form slot's credit.
        for (shift, want_verified) in [(0i64, true), (16, true), (32, false), (48, false)] {
            let movn = inst_with_operands(
                AArch64Opcode::Movn,
                vec![
                    MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr32)),
                    MachOperand::Imm(1),
                    MachOperand::Imm(shift),
                ],
            );
            let report = verify_function(&make_func_with_insts(vec![movn]));
            if want_verified {
                assert_eq!(report.verified_count(), 1, "W-form MOVN LSL #{shift}");
                assert_eq!(
                    report.genuinely_verified_count(),
                    1,
                    "W-form MOVN LSL #{shift} inverted-field proof must be non-degenerate"
                );
                assert!(
                    matches!(
                        &report.instructions[0].result,
                        InstructionVerificationResult::Verified { proof_name, .. }
                            if proof_name.contains("Wd")
                                && proof_name.contains("upper 32 bits zero")
                    ),
                    "W-form MOVN LSL #{shift} must bind the width-specific W-form proof"
                );
            } else {
                assert_eq!(
                    report.verified_count(),
                    0,
                    "illegal W-form MOVN LSL #{shift} must not be credited"
                );
                assert_eq!(report.unverified_count(), 1);
            }
        }
    }

    #[test]
    fn eor_lsl_lsr_reconstruction_verifies_all_emitted_widths() {
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
                    assert_eq!(
                        report.genuinely_verified_count(),
                        1,
                        "{opcode:?} #{amount} at width {width}: {:?}",
                        report.instructions[0].result
                    );
                }
            }
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
                    .expect("well-formed TST must bind to its complete flag proof");
                assert_eq!(query, format!("tst packed nzcv {width_tag}"));
                assert_eq!(category, ProofCategory::CmpCombine);

                let report = verify_function(&make_func_with_insts(vec![tst]));
                assert_eq!(
                    report.genuinely_verified_count(),
                    1,
                    "{width_tag} TST must be genuinely verified: {:?}",
                    report.instructions[0].result
                );
                assert!(matches!(
                    &report.instructions[0].result,
                    InstructionVerificationResult::Verified {
                        proof_name,
                        category: ProofCategory::CmpCombine,
                        degenerate: false,
                        ..
                    } if proof_name.to_lowercase().contains(width_tag)
                ));
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
    fn tst_complete_flag_proof_promotes_a_real_instruction() {
        let x = |id| MachOperand::VReg(trust_cg_ir::VReg::new(id, trust_cg_ir::RegClass::Gpr64));
        let func = make_func_with_insts(vec![
            inst_with_operands(AArch64Opcode::Tst, vec![x(0), x(1)]),
            inst(AArch64Opcode::Ret),
        ]);
        let inventory = verify_function(&func).emitted_opcode_inventory();
        assert!(
            inventory.is_promotable(),
            "TST with complete packed-NZCV authority must promote: {:?}",
            inventory.promotion_rejection_reason()
        );
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

            let report = verify_function(&make_func_with_insts(vec![inst]));
            match &report.instructions[0].result {
                InstructionVerificationResult::Verified { proof_name, .. } => {
                    assert!(
                        proof_name.to_lowercase().contains(width_tag),
                        "wrong carrier theorem selected: {proof_name}"
                    );
                }
                other => panic!("valid {width_tag} UBFM did not verify: {other:?}"),
            }
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
                let (query, category) = query.expect("shift-zero MOVZ must retain the hw0 proof");
                assert_eq!(query, "movz #imm16, lsl #0");
                assert_eq!(category, ProofCategory::ConstantMaterialization);
                assert_eq!(report.verified_count(), 1);
                match &report.instructions[0].result {
                    InstructionVerificationResult::Verified { proof_name, .. } => {
                        assert!(
                            proof_name.contains("LSL #0"),
                            "shift zero selected the wrong proof: {proof_name}"
                        );
                    }
                    other => panic!("shift-zero MOVZ must verify, got {other:?}"),
                }
            } else {
                assert_eq!(report.verified_count(), 0);
                assert_eq!(report.unverified_count(), 1);
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
        let report = verify_function(&make_func_with_insts(vec![w_form]));
        assert_eq!(report.verified_count(), 1);
        assert_eq!(report.genuinely_verified_count(), 1);
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
            let report = verify_function(&make_func_with_insts(vec![movn]));
            assert_eq!(report.verified_count(), 1);
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
    fn test_generated_const_materialization_large_offset_is_fully_covered() {
        // REGRESSION PIN: a wide-constant materialization chain (MOVZ + MOVK)
        // must be FULLY covered. MOVK was previously the one uncovered row here,
        // which is what took proof-required AArch64 compilation to zero admitted
        // functions once loop-head alignment started emitting wide constants.
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
        assert_eq!(
            report.unverified_count(),
            0,
            "MOVZ+MOVK wide-constant chain must be fully covered; uncovered rows: {:?}",
            report
                .instructions
                .iter()
                .filter(|i| matches!(i.result, InstructionVerificationResult::Unverified { .. }))
                .map(|i| i.opcode)
                .collect::<Vec<_>>()
        );
        assert_eq!(report.verified_count(), 5);
        assert!(report.all_verified());
    }

    #[test]
    fn test_generated_const_materialization_small_negative_sequence_has_full_verifier_coverage() {
        // MOVN verifies; the trailing RET (proof retracted in #62) is tested separately.
        let func = make_func_with_insts(vec![inst_with_operands(
            AArch64Opcode::Movn,
            vec![
                MachOperand::VReg(trust_cg_ir::VReg::new(0, trust_cg_ir::RegClass::Gpr64)),
                MachOperand::Imm(0),
            ],
        )]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 1);
        assert_eq!(report.verified_count(), 1);
        assert_eq!(report.unverified_count(), 0);
        assert!(report.all_verified());
    }

    // =======================================================================
    // 29. Generated FP conversion instructions are verified
    // =======================================================================

    #[test]
    fn test_generated_fp_conversion_ops_verified() {
        for (opcode, proof_substring) in [
            (AArch64Opcode::FcvtzsRR, "FCVTZS"),
            (AArch64Opcode::FcvtzuRR, "FCVTZU"),
            (AArch64Opcode::ScvtfRR, "SCVTF"),
            (AArch64Opcode::UcvtfRR, "UCVTF"),
            (AArch64Opcode::FcvtSD, "Fpromote_F64_F32 -> FCVT Dd,Sn"),
            (AArch64Opcode::FcvtDS, "Fdemote_F32_F64 -> FCVT Ss,Dn"),
        ] {
            assert_verified_with_proof(opcode, ProofCategory::FpConversion, proof_substring);
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
    fn test_generated_fp_conversion_sequence_has_full_verifier_coverage() {
        // FP conversion ops verify; the trailing RET (proof retracted #62) is
        // tested separately and excluded from this conversion-coverage sequence.
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
        assert_eq!(report.verified_count(), 6);
        assert_eq!(report.unverified_count(), 0);
        assert!(report.all_verified());
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
        assert_eq!(report.verified_count(), 2);
        assert_eq!(report.unverified_count(), 0);

        match &report.instructions[0].result {
            InstructionVerificationResult::Verified {
                proof_name,
                category,
                ..
            } => {
                assert_eq!(*category, ProofCategory::RegAlloc);
                assert!(
                    proof_name.contains("spill/reload semantic roundtrip"),
                    "unexpected stack-slot reload proof name: {proof_name}"
                );
            }
            other => panic!("expected stack-slot reload proof, got {other:?}"),
        }

        match &report.instructions[1].result {
            InstructionVerificationResult::Verified {
                proof_name,
                category,
                ..
            } => {
                assert_eq!(*category, ProofCategory::RegAlloc);
                assert!(
                    proof_name.contains("spill offset non-interference"),
                    "unexpected stack-slot spill proof name: {proof_name}"
                );
            }
            other => panic!("expected stack-slot spill non-interference proof, got {other:?}"),
        }
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
        assert_eq!(report.verified_count(), 2);
        assert_eq!(report.unverified_count(), 0);

        match &report.instructions[0].result {
            InstructionVerificationResult::Verified {
                proof_name,
                category,
                ..
            } => {
                assert_eq!(*category, ProofCategory::RegAlloc);
                assert!(
                    proof_name.contains("spill/reload semantic roundtrip"),
                    "unexpected post-frame reload proof name: {proof_name}"
                );
            }
            other => panic!("expected post-frame reload proof, got {other:?}"),
        }

        match &report.instructions[1].result {
            InstructionVerificationResult::Verified {
                proof_name,
                category,
                ..
            } => {
                assert_eq!(*category, ProofCategory::RegAlloc);
                assert!(
                    proof_name.contains("spill offset non-interference"),
                    "unexpected post-frame spill proof name: {proof_name}"
                );
            }
            other => panic!("expected post-frame spill non-interference proof, got {other:?}"),
        }
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
        assert_eq!(report.verified_count(), 3);
        assert_eq!(report.unverified_count(), 0);

        for inst_report in &report.instructions {
            match &inst_report.result {
                InstructionVerificationResult::Verified {
                    proof_name,
                    category,
                    ..
                } => {
                    assert_eq!(*category, ProofCategory::RegAlloc);
                    assert!(
                        proof_name.contains("spill offset non-interference"),
                        "unexpected generated spill-store proof name: {proof_name}"
                    );
                }
                other => panic!("expected spill-store non-interference proof, got {other:?}"),
            }
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
        assert_eq!(report.verified_count(), 3);

        for inst_report in &report.instructions {
            match &inst_report.result {
                InstructionVerificationResult::Verified {
                    proof_name,
                    category,
                    ..
                } => {
                    assert_eq!(*category, ProofCategory::Memory);
                    assert!(
                        proof_name.to_lowercase().contains("load")
                            || proof_name.to_lowercase().contains("store"),
                        "unexpected generic memory proof name: {proof_name}"
                    );
                }
                other => panic!("expected generic memory proof, got {other:?}"),
            }
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
    fn test_generated_stp_spill_scalarization_stores_verified() {
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
        assert_eq!(report.verified_count(), 6);
        assert_eq!(report.unverified_count(), 0);

        // #62: the dedicated "stp spill scalarization" FrameLayout proof was a
        // degenerate X==X and was RETRACTED, so the two scalarized stores now bind
        // their ordinary store (Memory) proof rather than the dedicated FrameLayout
        // one. They still verify (the spilled values' store semantics are covered by
        // the Memory family).
        for inst_report in [&report.instructions[3], &report.instructions[5]] {
            match &inst_report.result {
                InstructionVerificationResult::Verified { category, .. } => {
                    assert_eq!(*category, ProofCategory::Memory);
                }
                other => panic!("expected scalarized store to verify via Memory, got {other:?}"),
            }
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
        assert_eq!(report.verified_count(), 2);
        assert_eq!(report.unverified_count(), 0);

        for inst_report in &report.instructions {
            match &inst_report.result {
                InstructionVerificationResult::Verified {
                    proof_name,
                    category,
                    ..
                } => {
                    assert_eq!(*category, ProofCategory::Memory);
                    assert!(
                        proof_name.to_lowercase().contains("store"),
                        "unexpected generic store proof name: {proof_name}"
                    );
                    assert!(
                        !proof_name.contains("stp spill scalarization"),
                        "plain scratch store was overclassified as STP scalarization: {proof_name}"
                    );
                }
                other => panic!("expected generic memory proof, got {other:?}"),
            }
        }

        let (query, category) = FunctionVerifier::inst_to_proof_query(&func.insts[0])
            .expect("plain StrRI must keep the generic store proof mapping");
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
        assert_eq!(report.verified_count(), 2);

        for inst_report in &report.instructions {
            match &inst_report.result {
                InstructionVerificationResult::Verified {
                    proof_name,
                    category,
                    ..
                } => {
                    assert_eq!(*category, ProofCategory::Memory);
                    assert!(
                        proof_name.to_lowercase().contains("store"),
                        "unexpected generic store proof name: {proof_name}"
                    );
                }
                other => panic!("expected generic memory proof, got {other:?}"),
            }
        }
    }

    // =======================================================================
    // 32. Generated emergency spill-slot address instructions are verified
    // =======================================================================

    #[test]
    fn test_generated_emergency_spill_slot_address_memops_verified() {
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
        assert_eq!(report.verified_count(), 2);
        assert_eq!(report.unverified_count(), 0);

        // #62: the dedicated "emergency spill slot address via X16" FrameLayout proof
        // was a degenerate X==X and was RETRACTED, so the X16-base load/store fall
        // through to their ordinary Memory load/store proofs (still verified).
        for inst_report in &report.instructions {
            match &inst_report.result {
                InstructionVerificationResult::Verified { category, .. } => {
                    assert_eq!(*category, ProofCategory::Memory);
                }
                other => panic!(
                    "expected emergency spill-slot memop to verify via Memory, got {other:?}"
                ),
            }
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
        assert_eq!(report.verified_count(), 2);

        for inst_report in &report.instructions {
            match &inst_report.result {
                InstructionVerificationResult::Verified {
                    proof_name,
                    category,
                    ..
                } => {
                    assert_eq!(*category, ProofCategory::Memory);
                    assert!(
                        proof_name.to_lowercase().contains("load")
                            || proof_name.to_lowercase().contains("store"),
                        "unexpected generic memory proof name: {proof_name}"
                    );
                }
                other => panic!("expected generic memory proof, got {other:?}"),
            }
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
            inst(AArch64Opcode::AddRR), // verified
            inst(AArch64Opcode::SubRR), // verified
            inst(AArch64Opcode::MulRR), // verified
            inst(AArch64Opcode::Neg),   // verified
            inst(AArch64Opcode::Phi),   // skipped
            inst(AArch64Opcode::Ret),   // unverified (#62: RET proof retracted)
        ]);
        let report = verify_function(&func);
        assert_eq!(report.total(), 6);
        assert_eq!(report.verified_count(), 4);
        assert_eq!(report.skipped_count(), 1);
        assert_eq!(report.unverified_count(), 1);
        assert_eq!(report.failed_count(), 0);
    }

    // =======================================================================
    // 33. with_config constructor
    // =======================================================================

    #[test]
    fn test_with_config() {
        let config = VerificationConfig::with_sample_count(1_000);
        let verifier = FunctionVerifier::with_config(config);
        let func = make_func_with_insts(vec![inst(AArch64Opcode::AddRR)]);
        let report = verifier.verify(&func);
        assert_eq!(report.verified_count(), 1);
    }

    // =======================================================================
    // 34. FP ops coverage
    // =======================================================================

    #[test]
    fn test_fp_ops_verified() {
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::FaddRR),
            inst(AArch64Opcode::FsubRR),
            inst(AArch64Opcode::FmulRR),
            inst(AArch64Opcode::FnegRR),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.verified_count(), 4);
        for ir in &report.instructions {
            if let InstructionVerificationResult::Verified { category, .. } = &ir.result {
                assert_eq!(*category, ProofCategory::FloatingPoint);
            } else {
                panic!("expected Verified for FP ops");
            }
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

        let (query, cat) =
            FunctionVerifier::opcode_to_proof_query(AArch64Opcode::StpPreIndex).unwrap();
        assert_eq!(query, "sp alignment preserved");
        assert_eq!(cat, ProofCategory::FrameLayout);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::StpRI).unwrap();
        assert_eq!(query, "callee-save pair slots don't overlap");
        assert_eq!(cat, ProofCategory::FrameLayout);

        let (query, cat) = FunctionVerifier::opcode_to_proof_query(AArch64Opcode::LdpRI).unwrap();
        assert_eq!(query, "callee-save restore is identity");
        assert_eq!(cat, ProofCategory::FrameLayout);

        let (query, cat) =
            FunctionVerifier::opcode_to_proof_query(AArch64Opcode::LdpPostIndex).unwrap();
        assert_eq!(query, "callee-save restore is identity");
        assert_eq!(cat, ProofCategory::FrameLayout);

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
        // proof was retracted in #62, so they now have NO value-proof mapping
        // (FailClosedAllowlisted in classify_aarch64).
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
            "MOVK's hw0 idempotence theorem is not a general lowering proof; \
             per-(width,shift) credit comes from movk_halfword_query only"
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
        // ADD verifies (genuine); RET is now Unverified (#62: RET X==X retracted).
        assert_eq!(report.verified_count(), 1);
        assert_eq!(report.unverified_count(), 1);
    }

    // =======================================================================
    // 38. Trap pseudo-ops are skipped
    // =======================================================================

    #[test]
    fn test_trap_pseudo_ops_skipped() {
        let func = make_func_with_insts(vec![
            inst(AArch64Opcode::Brk),
            inst(AArch64Opcode::TrapOverflow),
            inst(AArch64Opcode::TrapBoundsCheck),
            inst(AArch64Opcode::TrapNull),
            inst(AArch64Opcode::TrapDivZero),
            inst(AArch64Opcode::TrapShiftRange),
        ]);
        let report = verify_function(&func);
        assert_eq!(report.skipped_count(), 6);
        assert_eq!(report.unverified_count(), 0);
        assert_eq!(report.coverage_percent(), 100.0);
        for ir in &report.instructions {
            assert!(
                ir.result.is_skipped(),
                "trap opcode {:?} should be skipped, got {:?}",
                ir.opcode,
                ir.result
            );
        }
        assert!(
            FunctionVerifier::inst_to_proof_query(&inst(AArch64Opcode::Brk)).is_none(),
            "BRK should be handled by trap skip policy, not a proof query"
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
        assert_eq!(report.verified_count(), 3);
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
        report.instructions.iter().any(|r| {
            matches!(
                &r.result,
                InstructionVerificationResult::Failed { proof_name, .. }
                    if proof_name == "provenance-crosscheck (TV-2)"
            )
        })
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

    /// ENC-11 verdict-tier TAXONOMY LOCK / M3 criterion (a): a Statistically-
    /// credited verified instruction is NEVER counted in the Formal
    /// (SolverProven) tally, and vice versa. The two taxonomy scans partition the
    /// `Verified` set by their ACTUAL strength; a sampled verdict can never
    /// inflate the formal count. Crediting a sampled verdict as proven is the
    /// exact soundness-reporting lie PROOF-4/5 + P3c (df8f6bd) closed. Counts are
    /// deliberately ASYMMETRIC (2 Statistical, 1 Formal) so any strength-swap in
    /// either counter changes an asserted value (the test's teeth).
    #[test]
    fn enc11_statistical_verified_never_counted_as_formal() {
        fn verified(strength: VerificationStrength) -> InstructionReport {
            InstructionReport {
                inst_index: 0,
                opcode: InstructionOpcode::AArch64(AArch64Opcode::AddRR),
                result: InstructionVerificationResult::Verified {
                    proof_name: "add".to_string(),
                    category: ProofCategory::Arithmetic,
                    strength,
                    degenerate: false,
                },
            }
        }
        let report = FunctionVerificationReport {
            function_name: "enc11_taxonomy_fn".to_string(),
            instructions: vec![
                verified(VerificationStrength::Statistical {
                    sample_count: 100_000,
                }),
                verified(VerificationStrength::Statistical {
                    sample_count: 100_000,
                }),
                verified(VerificationStrength::Formal),
                verified(VerificationStrength::Exhaustive),
            ],
        };
        assert_eq!(report.verified_count(), 4);
        assert_eq!(
            report.statistically_credited_count(),
            2,
            "exactly the two Statistical instructions are statistically credited"
        );
        assert_eq!(
            report.formally_credited_count(),
            1,
            "the Statistical (and Exhaustive) instructions must NOT inflate the Formal tally"
        );
        // Disjoint tiers: Statistical + Formal < verified (the Exhaustive
        // instruction belongs to NEITHER), so a sampled verdict can never be
        // lumped in with the SolverProven ones.
        assert!(
            report.statistically_credited_count() + report.formally_credited_count()
                < report.verified_count(),
            "the credited tiers must be disjoint and neither may swallow the other"
        );
    }
}
